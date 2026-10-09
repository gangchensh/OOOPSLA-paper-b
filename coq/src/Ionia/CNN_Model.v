From Stdlib Require Import Reals String Nat List Bool Arith Lra Lia.
Require Export Ionia.CNN_OP.
Import ListNotations.
Set Implicit Arguments.

Definition LeNet_5(input: Tensor3 1 32 32)
  (kernel_c1: Tensor4 6 1 5 5)(bias_c1: Tensor1 6)
  (kernel_c2: Tensor4 16 6 5 5) (bias_c2: Tensor1 16)
  (full_c1: Tensor2 120 (16*5*5))(full_b1: Tensor1 120)
  (full_c2: Tensor2 84 120)(full_b2: Tensor1 84)
  (full_c3: Tensor2 10 84)(full_b3: Tensor1 10)
  :=
  tlet feature_map_1 := Conv3d 0 1 bias_c1 kernel_c1 input in 
  tlet relu_map_1 := ReLU3d feature_map_1 in
  tlet pool_map_2 := Maxpool3d 2 relu_map_1 in
  tlet feature_map_3 := Conv3d 0 1 bias_c2 kernel_c2 pool_map_2 in
  tlet relu_map_3 := ReLU3d feature_map_3 in
  tlet pool_map_4 := Maxpool3d 2 relu_map_3 in
  tlet full_map_5 := Linear full_c1 full_b1 (Flatten3d pool_map_4) in
  tlet relu_map_5 := ReLU1d full_map_5 in
  tlet full_map_6 := Linear full_c2 full_b2 relu_map_5 in
  tlet relu_map_6 := ReLU1d full_map_6 in 
  tlet full_map_7 := Linear full_c3 full_b3 relu_map_6 in
  Softmax1d full_map_7.

Definition mnist(input: Tensor4 64 1 28 28)
  (kernel_c1: Tensor4 32 1 3 3)(bias_c1: Tensor1 32)
  (kernel_c2: Tensor4 64 32 3 3) (bias_c2: Tensor1 64)
  (full_c1: Tensor2 128 (64*12*12))(full_b1: Tensor1 128)
  (full_c2: Tensor2 10 128)(full_b2: Tensor1 10)
  (output_label : list nat )
  :=
  (* -> *)
  tlet feature_map_1 := Conv4d 0 1 bias_c1 kernel_c1 input in 
  tlet relu_map_1 := ReLU4d feature_map_1 in
  tlet feature_map_2 := Conv4d 0 1 bias_c2 kernel_c2 relu_map_1 in
  tlet relu_map_2 := ReLU4d feature_map_2 in
  tlet pool_map_1 := Maxpool4d 2 relu_map_2 in
  tlet drop_map_1 := Dropout4d pool_map_1 (REconst 0.25%R "0.25") in
  tlet flatten_map := Flatten4d drop_map_1 in
  tlet fc_map_1 := Linear2d full_c1 full_b1 flatten_map in
  tlet relu_map_3 := ReLU2d fc_map_1 in
  tlet drop_map_2 := Dropout2d relu_map_3 (REconst 0.5%R "0.5") in
  tlet fc_map_2 := Linear2d full_c2 full_b2 drop_map_2 in
  tlet output := Log_Softmax2d fc_map_2 in

  NLLLoss2d output output_label.

Definition AlexNet{batch channel m1 m2}
  (input: Tensor4 batch channel m1 m2)
  (c1_w: Tensor4 64 channel 11 11)(c1_b: Tensor1 64)
  (c2_w: Tensor4 192 64 5 5)(c2_b: Tensor1 192)
  (c3_w: Tensor4 384 192 3 3)(c3_b: Tensor1 384)
  (c4_w: Tensor4 256 384 3 3)(c4_b: Tensor1 256)
  (c5_w: Tensor4 256 256 3 3)(c5_b: Tensor1 256)
  (f1_w: Tensor2 4096 (256*6*6))(f1_b: Tensor1 4096)
  (f2_w: Tensor2 4096 4096)(f2_b: Tensor1 4096)
  (f3_w: Tensor2 1000 4096)(f3_b: Tensor1 1000)
  :=
  tlet conv1 := Conv4d 2 4 c1_b c1_w input in
  tlet conv1_relu := ReLU4d conv1 in
  tlet conv1_pool := Maxpool4d_pad 3 2 0 conv1_relu in
  tlet conv2 := Conv4d 2 1 c2_b c2_w conv1_pool in
  tlet conv2_relu := ReLU4d conv2 in
  tlet conv2_pool := Maxpool4d_pad 3 2 0 conv2_relu in
  tlet conv3 := Conv4d 1 1 c3_b c3_w conv2_pool in
  tlet conv3_relu := ReLU4d conv3 in
  tlet conv4 := Conv4d 1 1 c4_b c4_w conv3_relu in
  tlet conv4_relu := ReLU4d conv4 in
  tlet conv5 := Conv4d 1 1 c5_b c5_w conv4_relu in
  tlet conv5_relu := ReLU4d conv5 in
  tlet conv5_pool := Maxpool4d_pad 3 2 0 conv5_relu in
  
  tlet avgpool := AdaptiveAvgPool4d 6 6 conv5_pool in
  
  tlet drop1 := Dropout2d (Flatten4d avgpool) (REconst 0.5%R "0.5") in
  tlet fc1 := Linear2d f1_w f1_b drop1 in
  tlet fc1_relu := ReLU2d fc1 in
  tlet drop2 := Dropout2d fc1_relu (REconst 0.5%R "0.5") in
  tlet fc2 := Linear2d f2_w f2_b drop2 in
  tlet fc2_relu := ReLU2d fc2 in
  Linear2d f3_w f3_b fc2_relu.

(* ResNet *)

Definition BasicBlock{batch m1 m2}
  (in_channel out_channel stride:nat)(downsample: bool) 
  (input: Tensor4 batch in_channel m1 m2)
  :=

  let conv1_w := mkTensor4 out_channel in_channel 3 3 in
  let conv1_b := mkTensor1 out_channel in
  let conv2_w := mkTensor4 out_channel out_channel 3 3 in
  let conv2_b := mkTensor1 out_channel in 

  tlet conv1 := Conv4d 1 stride conv1_b conv1_w input in
  tlet bn1 := BatchNorm4d out_channel conv1 in
  tlet relu1 := ReLU4d bn1 in
  
  tlet conv2 := convert_3 (Conv4d 1 1 conv2_b conv2_w relu1) in
  tlet bn2 := BatchNorm4d out_channel conv2 in

  tlet identity := if downsample then
  (* in_channel != out_channel *)
  let convdown_w := mkTensor4 out_channel in_channel 1 1 in
  let convdown_b := mkTensor1 out_channel in
  tlet identity1 := Conv4d 0 stride convdown_b convdown_w input in
  BatchNorm4d out_channel identity1 else
  (* in_channel = out_channel *)
  convert_in stride input in

  tlet conn := Add4d (convert_1_3 stride bn2) identity in
  ReLU4d conn.

Definition BottleNeck{batch m1 m2}
  (in_channel out_channel s:nat)(downsample: bool) 
  (input: Tensor4 batch in_channel m1 m2)
  :=

  let conv1_w := mkTensor4 out_channel in_channel 1 1 in
  let conv1_b := mkTensor1 out_channel in
  let conv2_w := mkTensor4 out_channel out_channel 3 3 in
  let conv2_b := mkTensor1 out_channel in 
  let conv3_w := mkTensor4 (out_channel*4) out_channel 1 1 in
  let conv3_b := mkTensor1 (out_channel*4) in 

  tlet conv1 := convert_1 (Conv4d 0 1 conv1_b conv1_w input) in
  tlet bn1 := BatchNorm4d out_channel conv1 in
  tlet relu1 := ReLU4d bn1 in
  
  tlet conv2 := Conv4d 1 s conv2_b conv2_w relu1 in
  tlet bn2 := BatchNorm4d out_channel conv2 in
  tlet relu2 := ReLU4d bn2 in

  tlet conv3 := convert_1 (Conv4d 0 1 conv3_b conv3_w relu2) in
  tlet bn3 := BatchNorm4d (out_channel*4) conv3 in

  tlet identity := if downsample then
  let convdown_w := mkTensor4 (out_channel*4) in_channel 1 1 in
  let convdown_b := mkTensor1 (out_channel*4) in
  tlet identity1 := Conv4d 0 s convdown_b convdown_w input in
  BatchNorm4d (out_channel*4) identity1 else
  (* in_channel = out_channel*4 *)
  convert_in s input in

  tlet conn := Add4d (convert_1_3 s bn3) identity in
  ReLU4d conn.

Fixpoint make_layer {batch m1 m2 in_channel out_channel}(num_block :nat):
  Tensor4 batch in_channel m1 m2 ->
  Tensor4 batch out_channel m1 m2 :=
  match num_block with
  | O => fun (input: Tensor4 batch in_channel m1 m2) =>
         convert_1 (BasicBlock in_channel out_channel 1 false input)
  | S p' => fun (input:Tensor4 batch in_channel m1 m2) =>
         convert_1 (BasicBlock in_channel out_channel 1 false (make_layer p' input))
  end.

Definition ResNet_34{batch channel m1 m2}
  (input: Tensor4 batch channel m1 m2)
  :=
  
  let b1_cv1_w := mkTensor4 64 channel 7 7 in
  let b1_cv1_b := mkTensor1 64 in
  let b6_w := mkTensor2 10 (512*1*1) in
  let b6_b := mkTensor1 10 in

  (* block1: conv + bn + relu + maxpool *)
  tlet block1_conv := Conv4d 3 2 b1_cv1_b b1_cv1_w input in
  tlet block1_bn := BatchNorm4d 64 block1_conv in
  tlet block1_relu := ReLU4d block1_bn in
  tlet block1 := Maxpool4d_pad 3 2 1 block1_relu in
  
   (* block2: BasicBlock*3 *)
  tlet block2 := make_layer 3 block1 in

  (* block3: BasicBlock*4 *)
  tlet block3_1 := BasicBlock 64 128 2 true block2 in
  tlet block3 := make_layer 3 block3_1 in
  
  (* block4: BasicBlock*6  *)
  tlet block4_1 := BasicBlock 128 256 2 true block3 in
  tlet block4 := make_layer 5 block4_1 in

  (* block5: BasicBlock*3  *)
  tlet block5_1 := BasicBlock 256 512 2 true block4 in
  tlet block5 := make_layer 2 block5_1 in
  
  (* block6: avgpool + flatten + linear *)
  tlet block6_pool := AdaptiveAvgPool4d 1 1 block5 in (* (4,512,1,1) *)
  tlet block6_flatt := Flatten4d block6_pool in       (* (4,512) *)
  Linear2d b6_w b6_b block6_flatt.

(* VGG-16 *)
Definition VGG_16{batch} (input: Tensor4 batch 3 224 224)
  (c1_w: Tensor4 64 3 3 3) (c1_b: Tensor1 64)
  (c2_w: Tensor4 64 64 3 3) (c2_b: Tensor1 64)
  (c3_w: Tensor4 128 64 3 3) (c3_b: Tensor1 128)
  (c4_w: Tensor4 128 128 3 3) (c4_b: Tensor1 128)
  (c5_w: Tensor4 256 128 3 3) (c5_b: Tensor1 256)
  (c6_w: Tensor4 256 256 3 3) (c6_b: Tensor1 256)
  (c7_w: Tensor4 256 256 3 3) (c7_b: Tensor1 256)
  (c8_w: Tensor4 512 256 3 3) (c8_b: Tensor1 512)
  (c9_w: Tensor4 512 512 3 3) (c9_b: Tensor1 512)
  (c10_w: Tensor4 512 512 3 3) (c10_b: Tensor1 512)
  (c11_w: Tensor4 512 512 3 3) (c11_b: Tensor1 512)
  (c12_w: Tensor4 512 512 3 3) (c12_b: Tensor1 512)
  (c13_w: Tensor4 512 512 3 3) (c13_b: Tensor1 512)
  (f1_w: Tensor2 4096 (512*7*7)) (f1_b: Tensor1 4096)
  (f2_w: Tensor2 4096 4096) (f2_b: Tensor1 4096)
  (f3_w: Tensor2 1000 4096) (f3_b: Tensor1 1000)
  := 

  tlet conv1 := Conv4d 1 1 c1_b c1_w input in
  tlet conv1_relu := ReLU4d conv1 in
  tlet conv2 := Conv4d 1 1 c2_b c2_w conv1_relu in
  tlet conv2_relu := ReLU4d conv2 in

  tlet pool1 := Maxpool4d 2 conv2_relu in     (* (batch,64,112,112) *)
  
  tlet conv3 := Conv4d 1 1 c3_b c3_w pool1 in
  tlet conv3_relu := ReLU4d conv3 in
  tlet conv4 := Conv4d 1 1 c4_b c4_w conv3_relu in
  tlet conv4_relu := ReLU4d conv4 in

  tlet pool2 := Maxpool4d 2 conv4_relu in     (* (batch,128,56,56) *)

  tlet conv5 := Conv4d 1 1 c5_b c5_w pool2 in
  tlet conv5_relu := ReLU4d conv5 in
  tlet conv6 := Conv4d 1 1 c6_b c6_w conv5_relu in
  tlet conv6_relu := ReLU4d conv6 in
  tlet conv7 := Conv4d 1 1 c7_b c7_w conv6_relu in
  tlet conv7_relu := ReLU4d conv7 in

  tlet pool3 := Maxpool4d 2 conv7_relu in     (* (batch,256,28,28) *)

  tlet conv8 := Conv4d 1 1 c8_b c8_w pool3 in
  tlet conv8_relu := ReLU4d conv8 in
  tlet conv9 := Conv4d 1 1 c9_b c9_w conv8_relu in
  tlet conv9_relu := ReLU4d conv9 in
  tlet conv10 := Conv4d 1 1 c10_b c10_w conv9_relu in
  tlet conv10_relu := ReLU4d conv10 in

  tlet pool4 := Maxpool4d 2 conv10_relu in    (* (batch,512,14,14) *)

  tlet conv11 := Conv4d 1 1 c11_b c11_w pool4 in
  tlet conv11_relu := ReLU4d conv11 in
  tlet conv12 := Conv4d 1 1 c12_b c12_w conv11_relu in
  tlet conv12_relu := ReLU4d conv12 in
  tlet conv13 := Conv4d 1 1 c13_b c13_w conv12_relu in
  tlet conv13_relu := ReLU4d conv13 in

  tlet pool5 := Maxpool4d 2 conv13_relu in     (* (batch,512,7,7) *)

  tlet fc1 := Linear2d f1_w f1_b (Flatten4d pool5) in (* (batch,4096) *)
  tlet fc1_relu := ReLU2d fc1 in 
  tlet fc2 := Linear2d f2_w f2_b fc1_relu in          (* (batch,4096) *)
  tlet fc2_relu := ReLU2d fc2 in
  tlet fc3 := Linear2d f3_w f3_b fc2_relu in          (* (batch,1000) *)
  Softmax2d fc3.


(* GoogleNet *)

Definition Inception{batch channel m1 m2}
  (c1_ch1 c2_ch1 c2_ch3 c3_ch1 c3_ch5 c4_ch1: nat)
  (input: Tensor4 batch channel m1 m2)
  :=

  let c1_w := mkTensor4 c1_ch1 channel 1 1 in
  let c1_b := mkTensor1 c1_ch1 in
  let c2_w1 := mkTensor4 c2_ch1 channel 1 1 in
  let c2_b1 := mkTensor1 c2_ch1 in 
  let c2_w2 := mkTensor4 c2_ch3 c2_ch1 3 3 in
  let c2_b2 := mkTensor1 c2_ch3 in
  let c3_w1 := mkTensor4 c3_ch1 channel 1 1 in
  let c3_b1 := mkTensor1 c3_ch1 in 
  let c3_w2 := mkTensor4 c3_ch5 c3_ch1 5 5 in
  let c3_b2 := mkTensor1 c3_ch5 in
  let c4_w := mkTensor4 c4_ch1 channel 1 1 in
  let c4_b := mkTensor1 c4_ch1 in

  (* branch1 *)
  tlet p1_1 := convert_1 (Conv4d 0 1 c1_b c1_w input) in
  tlet p1_2 := ReLU4d p1_1 in
  
  (* branch2 *)
  tlet p2_1 := convert_1 (Conv4d 0 1 c2_b1 c2_w1 input) in
  tlet p2_2 := ReLU4d p2_1 in
  tlet p2_3 := convert_3 (Conv4d 1 1 c2_b2 c2_w2 p2_2) in
  tlet p2_4 := ReLU4d p2_3 in

  (* branch3 *)
  tlet p3_1 := convert_1 (Conv4d 0 1 c3_b1 c3_w1 input) in
  tlet p3_2 := ReLU4d p3_1 in
  tlet p3_3 := convert_5 (Conv4d 2 1 c3_b2 c3_w2 p3_2) in
  tlet p3_4 := ReLU4d p3_3 in

  (* branch4 *)
  tlet p4_1 := convert_3 (Maxpool4d_pad 3 1 1 input) in
  tlet p4_2 := convert_1 (Conv4d 0 1 c4_b c4_w p4_1) in
  tlet p4_3 := ReLU4d p4_2 in

  Concat4d (Concat4d (Concat4d p1_2 p2_4) p3_4) p4_3.
  

Definition GoogLeNet{batch channel m1 m2}
  (input: Tensor4 batch channel m1 m2)           (* batch,3,224,224 *)
  :=
  
  let b1_w := mkTensor4 64 channel 7 7 in
  let b1_b := mkTensor1 64 in

  let b2_w1 := mkTensor4 64 64 1 1 in
  let b2_b1 := mkTensor1 64 in
  let b2_w2 := mkTensor4 192 64 3 3 in
  let b2_b2 := mkTensor1 192 in
  
  let f_w := mkTensor2 1000 1024 in
  let f_b := mkTensor1 1000 in

  tlet b1_conv := Conv4d 3 2 b1_b b1_w input in
  tlet b1_relu := ReLU4d b1_conv in
  tlet b1_pool := Maxpool4d_pad 3 2 0 b1_relu in (* batch,64,56,56 *)

  tlet b2_conv1 := Conv4d 0 1 b2_b1 b2_w1 b1_pool in
  tlet b2_relu1 := ReLU4d b2_conv1 in
  tlet b2_conv2 := Conv4d 1 1 b2_b2 b2_w2 b2_relu1 in
  tlet b2_relu2 := ReLU4d b2_conv2 in
  tlet b2_pool := Maxpool4d_pad 3 2 0 b2_relu2 in (* batch,192,28,28 *)

  tlet b3_1 := Inception 64 96 128 16 32 32 b2_pool in (* batch,256,28,28 *)
  tlet b3_2 := Inception 128 128 192 32 96 64 b3_1 in  (* batch,480,28,28 *)
  tlet b3_pool := Maxpool4d_pad 3 2 0 b3_2 in          (* batch,480,14,14 *)
  
  tlet b4_1 := Inception 192 96 208 16 48 64 b3_pool in     (* batch,512,14,14 *)
  tlet b4_2 := Inception 160 112 224 24 64 64 b3_1 in       (* batch,512,14,14 *)
  tlet b4_3 := Inception 128 128 256 24 64 64 b3_pool in    (* batch,512,14,14 *)
  tlet b4_4 := Inception 112 144 288 32 64 64 b3_1 in       (* batch,528,14,14 *)
  tlet b4_5 := Inception 256 160 320 32 128 128 b3_pool in  (* batch,832,14,14 *)
  tlet b4_pool := Maxpool4d 2 b4_5 in                       (* batch,832,7,7 *)
 
  tlet b5_1 := Inception 256 160 320 32 128 128 b4_pool in  (* batch,832,7,7 *)
  tlet b5_2 := Inception 384 192 384 48 128 128 b3_1 in     (* batch,1024,7,7 *)
  tlet b5_3 := AdaptiveAvgPool4d 1 1 b5_2 in                (* batch,1024,1,1 *)
  
  tlet b6_1 := Flatten4d b5_3  in                           (* batch,1024*1*1 *)
  tlet b6_2 := Dropout2d b6_1 (REconst 0.2%R "0.2") in                      (* batch,1024*1*1 *)
  Linear2d f_w f_b b6_2                                     (* batch,1000 *)
  .


(* DenseNet *)

Definition DenseLayer{batch channel m1 m2}
  (bn_size growth_rate : nat)(drop_rate: exp num)
  (input: Tensor4 batch channel m1 m2)
  := 
  
  let c1_w := mkTensor4 (bn_size * growth_rate) channel 1 1 in
  let c1_b := mkTensor1 (bn_size * growth_rate) in
  let c2_w := mkTensor4 growth_rate (bn_size * growth_rate) 3 3 in
  let c2_b := mkTensor1 growth_rate in

  tlet norm1 := BatchNorm4d channel input in
  tlet relu1 := ReLU4d norm1 in
  tlet conv1 := convert_1 (Conv4d 0 1 c1_b c1_w relu1) in
  
  tlet norm2 := BatchNorm4d (bn_size * growth_rate) conv1 in
  tlet relu2 := ReLU4d norm2 in
  tlet conv2 := convert_3 (Conv4d 1 1 c2_b c2_w relu2) in

  tlet new_features := Dropout4d conv2 drop_rate in
  Concat4d input new_features.


Fixpoint DenseBlock {batch channel m1 m2}
  (bn_size growth_rate num_layers :nat) (drop_rate: exp num):
  Tensor4 batch channel m1 m2 ->
  Tensor4 batch (channel + growth_rate * num_layers) m1 m2
  :=
  match num_layers with
  | O => fun (input: Tensor4 batch channel m1 m2) =>
         convert_times_1 eq_refl input
  | S p' => fun (input:Tensor4 batch channel m1 m2) =>
            convert_times (DenseLayer bn_size growth_rate drop_rate 
            (DenseBlock bn_size growth_rate p' drop_rate input))
  end.


(* Transition *)
Definition Transition{batch channel m1 m2}
  (out_channel:nat)(input: Tensor4 batch channel m1 m2)
  :=
  let c1_w := mkTensor4 out_channel channel 1 1 in
  let c1_b := mkTensor1 out_channel in

  tlet norm := BatchNorm4d channel input in
  tlet relu := ReLU4d norm in
  tlet conv := Conv4d 0 1 c1_b c1_w relu in
  Avgpool4d 2 conv.

Definition DenseNet_121{batch channel m1 m2}
  (bn_size growth_rate num_init_features compression_rate : nat)
  (drop_rate: exp num)
  (input: Tensor4 batch channel m1 m2)
  :=
  
  let c1_w := mkTensor4 64 channel 7 7 in
  let c1_b := mkTensor1 64 in

  let f1_w := mkTensor2 1000 1024 in
  let f1_b := mkTensor1 1000 in

  (* First convolution *)
  tlet conv0 := Conv4d 3 2 c1_b c1_w input in
  tlet norm0 := BatchNorm4d 64 conv0 in
  tlet relu0 := ReLU4d norm0 in
  tlet pool0 := Maxpool4d_pad 3 2 1 relu0 in

  (* DenseBlock *)
  tlet db1 := DenseBlock 4 32 6 (REconst 0%R "0") pool0 in
  tlet trans1 := Transition 128 db1 in
  tlet db2 := DenseBlock 4 32 12 (REconst 0%R "0") trans1 in
  tlet trans2 := Transition 256 db2 in
  tlet db3 := DenseBlock 4 32 24 (REconst 0%R "0") trans2 in
  tlet trans3 := Transition 512 db3 in
  tlet db4 := DenseBlock 4 32 16 (REconst 0%R "0") trans3 in

  (* Final batch norm *)
  tlet norm5 := BatchNorm4d 1024 db4 in
  tlet relu5 := ReLU4d norm5 in
  tlet pool5 := AdaptiveAvgPool4d 1 1 relu5 in
  tlet flatt := Flatten4d pool5 in
  Linear2d f1_w f1_b flatt
  .

(* vae *)
Definition VAE(input: Tensor4 128 1 28 28)
  (fc1_w: Tensor2 400 784) (fc1_b: Tensor1 400)
  (fc21_w: Tensor2 20 400) (fc21_b: Tensor1 20)
  (fc22_w: Tensor2 20 400) (fc22_b: Tensor1 20)
  (fc3_w: Tensor2 400 20) (fc3_b: Tensor1 400)
  (fc4_w: Tensor2 784 400) (fc4_b: Tensor1 784)
  :=
  (* encode *)
  tlet flatten_map := Flatten4d input in              (* (128,784) *)
  tlet fc1_map := Linear2d fc1_w fc1_b flatten_map in (* (128,400) *)
  tlet relu1_map := ReLU2d fc1_map in                 (* (128,400) *)
  tlet mu := Linear2d fc21_w fc21_b relu1_map in      (* mean: (128,20) *)
  tlet logvar := Linear2d fc22_w fc22_b relu1_map in  (* var:  (128,20) *)
  
  tlet std := Exp2d (Mulc2d (REconst 0.5%R "0.5") logvar) in          (* (128,20) *)
  tlet eps := Randn2d std in                          (* (128,20) *)
  tlet z := Add2d (Mul2d eps std) mu in               (* (128,20) *)
  
  (* decode *)
  tlet fc3_map := Linear2d fc3_w fc3_b z in           (* (128,400) *)
  tlet relu3_map := ReLU2d fc3_map in                 (* (128,400) *)
  tlet fc4_map := Linear2d fc4_w fc4_b relu3_map in   (* (128,784) *)
  tlet output := Sigmoid2d fc4_map in                 (* (128,784) *)

  tlet BCE := BCELoss2d output flatten_map in
  (* 0.5 * sum(1 + log(sigma^2) - mu^2 - sigma^2) *)
  tlet KLD := mul (negate (REconst 0.5%R "0.5"))(Sum2d (Sub2d (Sub2d 
  (Addc2d (REconst 1%R "1") logvar) (Mul2d mu mu)) (Exp2d logvar))) in
  Addc2d KLD BCE .

(* DCGAN *)

Definition Generator{nz ngf nc:nat}(input: Tensor4 64 nz 1 1)
  (ct1_w: Tensor4 (ngf*8) nz 4 4) (ct1_b: Tensor1 (ngf*8)) 
  (ct2_w: Tensor4 (ngf*4) (ngf*8) 4 4) (ct2_b: Tensor1 (ngf*4))
  (ct3_w: Tensor4 (ngf*2) (ngf*4) 4 4) (ct3_b: Tensor1 (ngf*2))
  (ct4_w: Tensor4 ngf (ngf*2) 4 4) (ct4_b: Tensor1 ngf)
  (ct5_w: Tensor4 nc ngf 4 4) (ct5_b: Tensor1 nc)
  : Tensor4 64 nc 64 64 :=
  tlet feature_map_1 := ConvTranspose4d 0 1 ct1_b ct1_w input in      (* (64,ngf*8,4,4) *)
  tlet norm_map_1 := BatchNorm4d (ngf*8) feature_map_1 in             (* (64,ngf*8,4,4) *)
  tlet relu_map_1 := ReLU4d norm_map_1 in                             (* (64,ngf*8,4,4) *)
  tlet feature_map_2 := ConvTranspose4d 1 2 ct2_b ct2_w relu_map_1 in (* (64,ngf*4,8,8) *)
  tlet norm_map_2 := BatchNorm4d (ngf*4) feature_map_2 in             (* (64,ngf*4,8,8) *)
  tlet relu_map_2 := ReLU4d norm_map_2 in                             (* (64,ngf*4,8,8) *)
  tlet feature_map_3 := ConvTranspose4d 1 2 ct3_b ct3_w relu_map_2 in (* (64,ngf*2,16,16) *)
  tlet norm_map_3 := BatchNorm4d (ngf*2) feature_map_3 in             (* (64,ngf*2,16,16) *)
  tlet relu_map_3 := ReLU4d norm_map_3 in                             (* (64,ngf*2,16,16) *)
  tlet feature_map_4 := ConvTranspose4d 1 2 ct4_b ct4_w relu_map_3 in (* (64,ngf,32,32) *)
  tlet norm_map_4 := BatchNorm4d ngf feature_map_4 in                 (* (64,ngf,32,32) *)
  tlet relu_map_4 := ReLU4d norm_map_4 in                             (* (64,ngf,32,32) *)
  tlet feature_map_5 := ConvTranspose4d 1 2 ct5_b ct5_w relu_map_4 in (* (64,nc,64,64) *)
  Tanh4d feature_map_5                                                (* (64,nc,64,64) *)
  .

Definition Discriminator{ndf nc:nat}(D_input: Tensor4 64 nc 64 64)
  (c1_w: Tensor4 ndf nc 4 4) (c1_b: Tensor1 ndf)           
  (c2_w: Tensor4 (ndf*2) ndf 4 4) (c2_b: Tensor1 (ndf*2))
  (c3_w: Tensor4 (ndf*4) (ndf*2) 4 4) (c3_b: Tensor1 (ndf*4))
  (c4_w: Tensor4 (ndf*8) (ndf*4) 4 4) (c4_b: Tensor1 (ndf*8) )
  (c5_w: Tensor4 1 (ndf*8) 4 4) (c5_b: Tensor1 1)
  :=
  tlet feature_1 := Conv4d 1 2 c1_b c1_w D_input in                   (* (64,ndf,32,32) *)
  tlet relu_1 := LeakyReLU4d (REconst 0.2%R "0.2") feature_1 in                       (* (64,ndf,32,32) *)
  tlet feature_2 := Conv4d 1 2 c2_b c2_w relu_1 in                    (* (64,ndf*2,16,16) *)
  tlet norm_2 := BatchNorm4d (ndf*2) feature_2 in                     (* (64,ndf*2,16,16) *)
  tlet relu_2 := LeakyReLU4d (REconst 0.2%R "0.2") norm_2 in                          (* (64,ndf*2,16,16) *)
  tlet feature_3 := Conv4d 1 2 c3_b c3_w relu_2 in                    (* (64,ndf*4,8,8) *)
  tlet norm_3 := BatchNorm4d (ndf*4) feature_3 in                     (* (64,ndf*4,8,8) *)
  tlet relu_3 := LeakyReLU4d (REconst 0.2%R "0.2") norm_3 in                          (* (64,ndf*4,8,8) *)
  tlet feature_4 := Conv4d 1 2 c4_b c4_w relu_3 in                    (* (64,ndf*8,4,4) *)
  tlet norm_4 := BatchNorm4d (ndf*8) feature_4 in                     (* (64,ndf*8,4,4) *)
  tlet relu_4 := LeakyReLU4d (REconst 0.2%R "0.2") norm_4 in                          (* (64,ndf*8,4,4) *)
  tlet feature_5 := Conv4d 0 1 c5_b c5_w relu_4 in                    (* (64,1,1,1) *)
  Flatten4d (Sigmoid4d feature_5)                                     (* (64,1) *)
  .

Definition DCGAN{nz ngf ndf nc:nat}
  (G_input: Tensor4 64 nz 1 1)(D_real_input: Tensor4 64 nc 64 64)
  (ct1_w: Tensor4 (ngf*8) nz 4 4) (ct1_b: Tensor1 (ngf*8)) 
  (ct2_w: Tensor4 (ngf*4) (ngf*8) 4 4) (ct2_b: Tensor1 (ngf*4))
  (ct3_w: Tensor4 (ngf*2) (ngf*4) 4 4) (ct3_b: Tensor1 (ngf*2))
  (ct4_w: Tensor4 ngf (ngf*2) 4 4) (ct4_b: Tensor1 ngf)
  (ct5_w: Tensor4 nc ngf 4 4) (ct5_b: Tensor1 nc)
  (c1_w: Tensor4 ndf nc 4 4) (c1_b: Tensor1 ndf)          
  (c2_w: Tensor4 (ndf*2) ndf 4 4) (c2_b: Tensor1 (ndf*2))
  (c3_w: Tensor4 (ndf*4) (ndf*2) 4 4) (c3_b: Tensor1 (ndf*4))
  (c4_w: Tensor4 (ndf*8) (ndf*4) 4 4) (c4_b: Tensor1 (ndf*8) )
  (c5_w: Tensor4 1 (ndf*8) 4 4) (c5_b: Tensor1 1)
  (real_label: Tensor2 64 1) 
  :=

  tlet D_real_output := Discriminator D_real_input 
    c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b in

  tlet errD_real := BCELoss2d D_real_output real_label in 
  
  tlet fake := Generator G_input 
    ct1_w ct1_b ct2_w ct2_b ct3_w ct3_b ct4_w ct4_b ct5_w ct5_b in
  tlet D_fake_output := Discriminator fake 
    c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b in
  tlet fake_label := Fill2d zero real_label in            
  tlet errD_fake := BCELoss2d D_fake_output fake_label in
  
  tlet label := Fill2d one fake_label in
  BCELoss2d D_fake_output label
  .


(* RNN -> LSTM

  LSTM解决了RNN的长依赖问题，其主要组成由遗忘门、输入门、输出门和记忆部分组成
  首先确定LSTM的批量大小n、输入节点数d和隐藏节点数h
 
  # 输入门参数
  W_xi[d][h]: 连接输入与细胞输入门的权重矩阵;
  W_hi[h][h]: 连接上一细胞输出与本细胞单元中输入门的权重矩阵;
  b_i[h]
  # 遗忘门参数
  W_xf[d][h]: 连接输入与细胞遗忘门的权重矩阵;
  W_hf[h][h]: 连接上一细胞与本细胞中遗忘门的权重矩阵;
  b_f[h]
  # 输出门参数
  W_xo[d][h]: 连接输入与细胞输出门的权值矩阵;
  W_ho[h][h]: 连接上一细胞与现在时刻的细胞的权值矩阵;
  b_o[h]
  # 候选记忆元参数
  W_xc[d][h]: 用于产生新记忆的权值矩阵;
  W_hc[h][h]: 用于产生新记忆的权值矩阵;
  b_c[h]
  
  参数：
  输入：input[sequence_length][n][d]
  隐状态: H[num_layers][n][h]
  记忆：C[num_layers][n][h]

  输出：[num_layer][n][h] *)

Definition LSTM{seq_length n:nat}(d h:nat)
  (input: Tensor3 seq_length n d)
  (H: Tensor3 1 n h)
  (C: Tensor3 1 n h)
  :=
  (* 输入门参数 *)
  let W_xi := mkTensor2 d h in
  let W_hi := mkTensor2 h h in
  let b_i := mkTensor1 h in
  (* 遗忘门参数 *)
  let W_xf := mkTensor2 d h in
  let W_hf := mkTensor2 h h in
  let b_f := mkTensor1 h in
  (* 输出门参数 *)
  let W_xo := mkTensor2 d h in
  let W_ho := mkTensor2 h h in
  let b_o := mkTensor1 h in
  (* 候选记忆元参数 *)
  let W_xc := mkTensor2 d h in
  let W_hc := mkTensor2 h h in
  let b_c := mkTensor1 h in

  mkvSeq(fun i:fin seq_length => 
  tlet I := Sigmoid2d (mm_mul input[i] W_xi H[@nat2fin _ 0 (Nat.lt_0_succ _)] W_hi b_i) in
  tlet F := Sigmoid2d (mm_mul input[i] W_xf H[@nat2fin _ 0 (Nat.lt_0_succ _)] W_hf b_f) in
  tlet O := Sigmoid2d (mm_mul input[i] W_xo H[@nat2fin _ 0 (Nat.lt_0_succ _)] W_ho b_o) in
  tlet C_tilda := Sigmoid2d (mm_mul input[i] W_xc H[@nat2fin _ 0 (Nat.lt_0_succ _)] W_hc b_c) in
  tlet C_t := Add2d (Mul2d F C[@nat2fin _ 0 (Nat.lt_0_succ _)]) (Mul2d I C_tilda) in
  Mul2d O (Tanh2d C_t)
).



















