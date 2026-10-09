// fused_attention.cu — L3 flash-attention 式融合注意力 kernel + 13-kernel MHA 链基线
// 自包含：同一文件内给出
//   (a) 基线 13-kernel MHA 链（语义逐字对应 comm_to_cuda_llm.ml 的 mha_block_test：
//       q/k/v 投影 → splitheads×3 → QK^T → ×scale → causal mask → softmax → AV
//       → mergeheads → 输出投影）；
//   (b) 融合注意力 kernel（warp-per-row flash attention：K/V 分块流式载入共享内存，
//       online softmax running max/sum 重缩放 + AV 寄存器累加，causal mask 内联，
//       中间 score/prob 不落全局内存，split/merge 折叠为头索引），
//       融合链 = q/k/v 投影 + fused_attn + 输出投影 = 5 次发射。
// 形状为运行时参数：./fused_attention B H S D [REPS]；默认 1 2 8 16（L1 基线形状）。
// 输入 bin：fatt_input.bin (B,S,DM) fatt_wq/wk/wv/wo.bin (DM,DM)，DM=H*D。
// 输出 bin：fatt_out_chain.bin / fatt_out_fused.bin (B,S,DM)。
// 计时：CUDA events，5 warmup + REPS 次，min/median，与 wrap_generated_cuda.py 同口径。
#include <cuda_runtime.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#define CUDA_CHECK(x) do { cudaError_t e = (x); if (e != cudaSuccess) { \
  fprintf(stderr, "CUDA error %s at %s:%d\n", cudaGetErrorString(e), __FILE__, __LINE__); \
  exit(1); } } while (0)

#define FATT_WARPS 4          // 每 block 的 warp 数（每 warp 一行 query）
#define FATT_TILEJ 32         // K/V 流式分块行数
#define FATT_NE 4             // 每 lane 寄存器元素数上限（D ≤ 128）

// ---------------- 基线 13 kernel（runtime 维度版，语义同 mha_block_test） ----------------

__global__ void k_proj(const float* x, const float* w, float* out, int b, int s, int dm)
{
  int idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= b * s * dm) return;
  int i2 = idx % dm; int t = idx / dm;
  float acc = 0.f;
  for (int k = 0; k < dm; k++) acc += x[t * dm + k] * w[k * dm + i2];
  out[idx] = acc;
}

__global__ void k_split(const float* x, float* out, int b, int h, int s, int d)
{
  int idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= b * h * s * d) return;
  int dd = idx % d; int t = idx / d;
  int i = t % s; t /= s;
  int hh = t % h; int bi = t / h;
  out[idx] = x[(bi * s + i) * h * d + hh * d + dd];
}

__global__ void k_score(const float* q, const float* k, float* out, int b, int h, int s, int d)
{
  int idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= b * h * s * s) return;
  int j = idx % s; int t = idx / s;
  int i = t % s; int bh = t / s;
  const float* qr = q + ((size_t)bh * s + i) * d;
  const float* kr = k + ((size_t)bh * s + j) * d;
  float acc = 0.f;
  for (int dd = 0; dd < d; dd++) acc += qr[dd] * kr[dd];
  out[idx] = acc;
}

__global__ void k_mulc(float* x, float c, int n)
{
  int idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= n) return;
  x[idx] = c * x[idx];
}

__global__ void k_causal(float* x, int b, int h, int s)
{
  int idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= b * h * s * s) return;
  int j = idx % s; int i = (idx / s) % s;
  if (j > i) x[idx] = -1e30f;
}

__global__ void k_softmax(const float* x, float* out, int b, int h, int s)
{
  int idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= b * h * s * s) return;
  int row = idx / s;
  float sum = 0.f;
  for (int j = 0; j < s; j++) sum += expf(x[(size_t)row * s + j]);
  out[idx] = expf(x[idx]) / sum;
}

__global__ void k_av(const float* p, const float* v, float* out, int b, int h, int s, int d)
{
  int idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= b * h * s * d) return;
  int dd = idx % d; int t = idx / d;
  int i = t % s; int bh = t / s;
  float acc = 0.f;
  for (int j = 0; j < s; j++)
    acc += p[((size_t)bh * s + i) * s + j] * v[((size_t)bh * s + j) * d + dd];
  out[idx] = acc;
}

__global__ void k_merge(const float* x, float* out, int b, int h, int s, int d)
{
  int idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= b * s * h * d) return;
  int i2 = idx % (h * d); int t = idx / (h * d);
  int i = t % s; int bi = t / s;
  out[idx] = x[(((size_t)bi * h + i2 / d) * s + i) * d + i2 % d];
}

// ---------------- 融合注意力 kernel（flash-attention 式，warp-per-row） ----------------
// 直接读 q/k/v 的 (b,s,dm) 布局（split/merge 折叠为头索引），写 (b,s,dm) 融合输出。
// 每 block FATT_WARPS 个 warp，warp w 处理行 i = blockIdx.x*WARPS + w；
// K/V 按 FATT_TILEJ 行分块流入共享内存，online softmax（m/l 重缩放）+ AV 寄存器累加，
// causal mask 内联（j>i 跳过，整块 j0>imax 不载入）。

__global__ void k_fused_attn(const float* q, const float* k, const float* v,
                             float* out, int b, int h, int s, int d, float scale)
{
  extern __shared__ float smem[];            // K tile | V tile，各 TILEJ*d
  float* ks = smem;
  float* vs = smem + FATT_TILEJ * d;
  int warp = threadIdx.x >> 5, lane = threadIdx.x & 31;
  int i = blockIdx.x * FATT_WARPS + warp;
  int bh = blockIdx.y;
  int bi = bh / h, hi = bh % h;
  int dm = h * d;
  int active = (i < s);
  // 块内最大行号（causal 下块内所有 warp 的 j 上界）
  int imax = min(s - 1, (blockIdx.x + 1) * FATT_WARPS - 1);
  int ne = (d + 31) >> 5;

  float qreg[FATT_NE], acc[FATT_NE];
  for (int e = 0; e < FATT_NE; e++) acc[e] = 0.f;
  for (int e = 0; e < ne; e++) {
    int dd = (e << 5) + lane;
    qreg[e] = (active && dd < d) ? q[((size_t)bi * s + i) * dm + hi * d + dd] : 0.f;
  }
  float m = -INFINITY, l = 0.f;

  for (int j0 = 0; j0 <= imax; j0 += FATT_TILEJ) {
    int jt = min(FATT_TILEJ, imax - j0 + 1);
    // 全 block 协作载入 K/V 分块（含未激活 warp 的线程，保证 __syncthreads 一致）
    for (int t = threadIdx.x; t < jt * d; t += blockDim.x) {
      int jj = t / d, dd = t % d;
      ks[jj * d + dd] = k[((size_t)bi * s + (j0 + jj)) * dm + hi * d + dd];
      vs[jj * d + dd] = v[((size_t)bi * s + (j0 + jj)) * dm + hi * d + dd];
    }
    __syncthreads();
    if (active) {
      int jlim = min(jt, i - j0 + 1);   // 本行 causal 界
      for (int j = 0; j < jlim; j++) {
        float part = 0.f;
        for (int e = 0; e < ne; e++) {
          int dd = (e << 5) + lane;
          if (dd < d) part += qreg[e] * ks[j * d + dd];
        }
        #pragma unroll
        for (int off = 16; off > 0; off >>= 1)
          part += __shfl_xor_sync(0xffffffffu, part, off);
        float sc = part * scale;
        float m_new = fmaxf(m, sc);
        float alpha = expf(m - m_new);
        float p = expf(sc - m_new);
        l = l * alpha + p;
        for (int e = 0; e < ne; e++) {
          int dd = (e << 5) + lane;
          if (dd < d) acc[e] = acc[e] * alpha + p * vs[j * d + dd];
        }
        m = m_new;
      }
    }
    __syncthreads();
  }
  if (active) {
    for (int e = 0; e < ne; e++) {
      int dd = (e << 5) + lane;
      if (dd < d) out[((size_t)bi * s + i) * dm + hi * d + dd] = acc[e] / l;
    }
  }
}

// ---------------- host：链发射 ----------------

static int ceil_div(int a, int b) { return (a + b - 1) / b; }

static void launch_chain(float* x, float* wq, float* wk, float* wv, float* wo,
                         float* q, float* k, float* v, float* qs, float* ks_,
                         float* vs, float* sc, float* pb, float* att, float* mg,
                         float* out, int b, int h, int s, int d, int sync_each)
{
  int dm = h * d;
  float scale = 1.f / sqrtf((float)d);
  int n_dm = b * s * dm, n_hsd = b * h * s * d, n_ss = b * h * s * s;
  k_proj<<<ceil_div(n_dm, 256), 256>>>(x, wq, q, b, s, dm); if (sync_each) cudaDeviceSynchronize();
  k_proj<<<ceil_div(n_dm, 256), 256>>>(x, wk, k, b, s, dm); if (sync_each) cudaDeviceSynchronize();
  k_proj<<<ceil_div(n_dm, 256), 256>>>(x, wv, v, b, s, dm); if (sync_each) cudaDeviceSynchronize();
  k_split<<<ceil_div(n_hsd, 256), 256>>>(q, qs, b, h, s, d); if (sync_each) cudaDeviceSynchronize();
  k_split<<<ceil_div(n_hsd, 256), 256>>>(k, ks_, b, h, s, d); if (sync_each) cudaDeviceSynchronize();
  k_split<<<ceil_div(n_hsd, 256), 256>>>(v, vs, b, h, s, d); if (sync_each) cudaDeviceSynchronize();
  k_score<<<ceil_div(n_ss, 256), 256>>>(qs, ks_, sc, b, h, s, d); if (sync_each) cudaDeviceSynchronize();
  k_mulc<<<ceil_div(n_ss, 256), 256>>>(sc, scale, n_ss); if (sync_each) cudaDeviceSynchronize();
  k_causal<<<ceil_div(n_ss, 256), 256>>>(sc, b, h, s); if (sync_each) cudaDeviceSynchronize();
  k_softmax<<<ceil_div(n_ss, 256), 256>>>(sc, pb, b, h, s); if (sync_each) cudaDeviceSynchronize();
  k_av<<<ceil_div(n_hsd, 256), 256>>>(pb, vs, att, b, h, s, d); if (sync_each) cudaDeviceSynchronize();
  k_merge<<<ceil_div(n_dm, 256), 256>>>(att, mg, b, h, s, d); if (sync_each) cudaDeviceSynchronize();
  k_proj<<<ceil_div(n_dm, 256), 256>>>(mg, wo, out, b, s, dm); if (sync_each) cudaDeviceSynchronize();
}

static void launch_fused(float* x, float* wq, float* wk, float* wv, float* wo,
                         float* q, float* k, float* v, float* ao, float* out,
                         int b, int h, int s, int d)
{
  int dm = h * d;
  float scale = 1.f / sqrtf((float)d);
  int n_dm = b * s * dm;
  k_proj<<<ceil_div(n_dm, 256), 256>>>(x, wq, q, b, s, dm);
  k_proj<<<ceil_div(n_dm, 256), 256>>>(x, wk, k, b, s, dm);
  k_proj<<<ceil_div(n_dm, 256), 256>>>(x, wv, v, b, s, dm);
  dim3 grid(ceil_div(s, FATT_WARPS), b * h);
  size_t smem = 2 * (size_t)FATT_TILEJ * d * sizeof(float);
  k_fused_attn<<<grid, FATT_WARPS * 32, smem>>>(q, k, v, ao, b, h, s, d, scale);
  k_proj<<<ceil_div(n_dm, 256), 256>>>(ao, wo, out, b, s, dm);
}

// 仅注意力核：基线 5 kernel（score→mulc→causal→softmax→av，无同步）vs 融合 1 kernel
static void launch_core_baseline(float* qs, float* ks_, float* vs, float* sc,
                                 float* pb, float* att, int b, int h, int s, int d)
{
  float scale = 1.f / sqrtf((float)d);
  int n_hsd = b * h * s * d, n_ss = b * h * s * s;
  k_score<<<ceil_div(n_ss, 256), 256>>>(qs, ks_, sc, b, h, s, d);
  k_mulc<<<ceil_div(n_ss, 256), 256>>>(sc, scale, n_ss);
  k_causal<<<ceil_div(n_ss, 256), 256>>>(sc, b, h, s);
  k_softmax<<<ceil_div(n_ss, 256), 256>>>(sc, pb, b, h, s);
  k_av<<<ceil_div(n_hsd, 256), 256>>>(pb, vs, att, b, h, s, d);
}

// ---------------- 计时与主流程 ----------------

typedef void (*chain_fn)(void);

static float* g_args[16];
static int g_b, g_h, g_s, g_d;

static void fn_chain_sync(void)  { launch_chain(g_args[0], g_args[1], g_args[2], g_args[3], g_args[4], g_args[5], g_args[6], g_args[7], g_args[8], g_args[9], g_args[10], g_args[11], g_args[12], g_args[13], g_args[14], g_args[15], g_b, g_h, g_s, g_d, 1); }
static void fn_chain_nosync(void){ launch_chain(g_args[0], g_args[1], g_args[2], g_args[3], g_args[4], g_args[5], g_args[6], g_args[7], g_args[8], g_args[9], g_args[10], g_args[11], g_args[12], g_args[13], g_args[14], g_args[15], g_b, g_h, g_s, g_d, 0); }
// 融合链缓冲复用：q,k,v 用链的 q,k,v；ao 用 att；out 用独立 out2
static float* g_out2;
static void fn_fused(void)       { launch_fused(g_args[0], g_args[1], g_args[2], g_args[3], g_args[4], g_args[5], g_args[6], g_args[7], g_args[13], g_out2, g_b, g_h, g_s, g_d); }
static void fn_core_base(void)   { launch_core_baseline(g_args[8], g_args[9], g_args[10], g_args[11], g_args[12], g_args[13], g_b, g_h, g_s, g_d); }
static void fn_core_fused(void)  {
  int dm = g_h * g_d;
  dim3 grid(ceil_div(g_s, FATT_WARPS), g_b * g_h);
  size_t smem = 2 * (size_t)FATT_TILEJ * g_d * sizeof(float);
  k_fused_attn<<<grid, FATT_WARPS * 32, smem>>>(g_args[5], g_args[6], g_args[7], g_args[13], g_b, g_h, g_s, g_d, 1.f / sqrtf((float)g_d));
}

static void bench(const char* tag, chain_fn fn, int reps)
{
  for (int w = 0; w < 5; w++) fn();
  CUDA_CHECK(cudaDeviceSynchronize());
  cudaEvent_t t0, t1;
  CUDA_CHECK(cudaEventCreate(&t0)); CUDA_CHECK(cudaEventCreate(&t1));
  float best = 1e30f; float* all = (float*)malloc(reps * sizeof(float));
  for (int it = 0; it < reps; it++) {
    CUDA_CHECK(cudaEventRecord(t0));
    fn();
    CUDA_CHECK(cudaEventRecord(t1));
    CUDA_CHECK(cudaEventSynchronize(t1));
    float ms; CUDA_CHECK(cudaEventElapsedTime(&ms, t0, t1));
    all[it] = ms; if (ms < best) best = ms;
  }
  for (int a = 0; a < reps; a++)
    for (int c = a + 1; c < reps; c++)
      if (all[c] < all[a]) { float t = all[a]; all[a] = all[c]; all[c] = t; }
  printf("TIME %s %.6f\n", tag, best);
  printf("TIMEMED %s %.6f\n", tag, all[reps / 2]);
  CUDA_CHECK(cudaEventDestroy(t0)); CUDA_CHECK(cudaEventDestroy(t1));
  free(all);
}

static float* read_bin(const char* path, size_t n)
{
  FILE* f = fopen(path, "rb");
  if (!f) { fprintf(stderr, "cannot open %s\n", path); exit(1); }
  float* h = (float*)malloc(n * sizeof(float));
  if (fread(h, sizeof(float), n, f) != n) { fprintf(stderr, "short read %s\n", path); exit(1); }
  fclose(f);
  return h;
}

static void write_bin(const char* path, const float* h, size_t n)
{
  FILE* f = fopen(path, "wb");
  if (!f) { fprintf(stderr, "cannot write %s\n", path); exit(1); }
  fwrite(h, sizeof(float), n, f);
  fclose(f);
}

static float* dev_alloc_load(const char* path, size_t n)
{
  float* d; CUDA_CHECK(cudaMalloc(&d, n * sizeof(float)));
  float* h = read_bin(path, n);
  CUDA_CHECK(cudaMemcpy(d, h, n * sizeof(float), cudaMemcpyHostToDevice));
  free(h);
  return d;
}

int main(int argc, char** argv)
{
  int b = 1, h = 2, s = 8, d = 16, reps = 20;
  if (argc >= 5) { b = atoi(argv[1]); h = atoi(argv[2]); s = atoi(argv[3]); d = atoi(argv[4]); }
  if (argc >= 6) reps = atoi(argv[5]);
  if (d > FATT_NE * 32) { fprintf(stderr, "d=%d exceeds max %d\n", d, FATT_NE * 32); return 1; }
  int dm = h * d;
  size_t n_x = (size_t)b * s * dm, n_w = (size_t)dm * dm;
  size_t n_hsd = (size_t)b * h * s * d, n_ss = (size_t)b * h * s * s;
  g_b = b; g_h = h; g_s = s; g_d = d;

  float *dx = dev_alloc_load("fatt_input.bin", n_x);
  float *dwq = dev_alloc_load("fatt_wq.bin", n_w);
  float *dwk = dev_alloc_load("fatt_wk.bin", n_w);
  float *dwv = dev_alloc_load("fatt_wv.bin", n_w);
  float *dwo = dev_alloc_load("fatt_wo.bin", n_w);
  float *dq, *dk, *dv, *dqs, *dks, *dvs, *dsc, *dpb, *datt, *dmg, *dout, *dout2;
  CUDA_CHECK(cudaMalloc(&dq, n_x * 4)); CUDA_CHECK(cudaMalloc(&dk, n_x * 4));
  CUDA_CHECK(cudaMalloc(&dv, n_x * 4));
  CUDA_CHECK(cudaMalloc(&dqs, n_hsd * 4)); CUDA_CHECK(cudaMalloc(&dks, n_hsd * 4));
  CUDA_CHECK(cudaMalloc(&dvs, n_hsd * 4));
  CUDA_CHECK(cudaMalloc(&dsc, n_ss * 4)); CUDA_CHECK(cudaMalloc(&dpb, n_ss * 4));
  CUDA_CHECK(cudaMalloc(&datt, n_hsd * 4)); CUDA_CHECK(cudaMalloc(&dmg, n_x * 4));
  CUDA_CHECK(cudaMalloc(&dout, n_x * 4)); CUDA_CHECK(cudaMalloc(&dout2, n_x * 4));

  g_args[0] = dx; g_args[1] = dwq; g_args[2] = dwk; g_args[3] = dwv; g_args[4] = dwo;
  g_args[5] = dq; g_args[6] = dk; g_args[7] = dv; g_args[8] = dqs; g_args[9] = dks;
  g_args[10] = dvs; g_args[11] = dsc; g_args[12] = dpb; g_args[13] = datt;
  g_args[14] = dmg; g_args[15] = dout;
  g_out2 = dout2;

  printf("SHAPE b=%d h=%d s=%d d=%d dm=%d reps=%d\n", b, h, s, d, dm, reps);

  // 基线（L1 口径：每 kernel cudaDeviceSynchronize）与无同步变体
  bench("chain13_sync", fn_chain_sync, reps);
  bench("chain13_nosync", fn_chain_nosync, reps);
  // 融合链（5 次发射）
  bench("fused5", fn_fused, reps);
  // 仅注意力核：基线 5 kernel vs 融合 1 kernel
  bench("core5_nosync", fn_core_base, reps);
  bench("core1_fused", fn_core_fused, reps);

  // 落盘输出供 NumPy 对比
  CUDA_CHECK(cudaDeviceSynchronize());
  float* hout = (float*)malloc(n_x * 4);
  fn_chain_nosync();
  CUDA_CHECK(cudaDeviceSynchronize());
  CUDA_CHECK(cudaMemcpy(hout, dout, n_x * 4, cudaMemcpyDeviceToHost));
  write_bin("fatt_out_chain.bin", hout, n_x);
  fn_fused();
  CUDA_CHECK(cudaDeviceSynchronize());
  CUDA_CHECK(cudaMemcpy(hout, dout2, n_x * 4, cudaMemcpyDeviceToHost));
  write_bin("fatt_out_fused.bin", hout, n_x);
  free(hout);
  return 0;
}
