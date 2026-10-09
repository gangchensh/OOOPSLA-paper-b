(* ImageNet ResNet-18 imperative AST.
   Architecture (batch = 1):
     input  : 1 x 3   x 224 x 224
     conv1  : 3 -> 64, 7x7, padding=3, stride=2  => 1 x 64  x 112 x 112
     maxpool: 3x3, padding=1, stride=2           => 1 x 64  x 56  x 56
     layer1 : 2 BasicBlocks, 64  channels, 56x56 (identity shortcuts)
     layer2 : 2 BasicBlocks, 128 channels, 28x28 (first block projects)
     layer3 : 2 BasicBlocks, 256 channels, 14x14 (first block projects)
     layer4 : 2 BasicBlocks, 512 channels,  7x7  (first block projects)
     avgpool: 1 x 512 x 1 x 1
     flatten: 1 x 512
     fc     : 512 -> 1000
*)

Require Import Ionia.CNN_Examples_Base.
Require Import Logic.FunctionalExtensionality.

From Stdlib Require Import List String.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.
Opaque CG_acc CG_exp.

Definition resnet18_input : exp (ary '{1} (ary '{3} (ary '{224} (ary '{224} num)))) := vrd "input".

(* -------------------- Stem -------------------- *)
Definition resnet18_conv1_w : exp (ary '{64} (ary '{3} (ary '{7} (ary '{7} num)))) := vrd "conv1_w".
Definition resnet18_conv1_b : exp (ary '{64} num) := vrd "conv1_b".
Definition resnet18_bn1_mean  : exp (ary '{64} num) := vrd "bn1_mean".
Definition resnet18_bn1_var   : exp (ary '{64} num) := vrd "bn1_var".
Definition resnet18_bn1_gamma : exp (ary '{64} num) := vrd "bn1_gamma".
Definition resnet18_bn1_beta  : exp (ary '{64} num) := vrd "bn1_beta".
Definition resnet18_eps : exp num := vrd "bn_eps".

Definition resnet18_conv1_out  : acc (ary '{1} (ary '{64} (ary '{112} (ary '{112} num)))) := vwt "conv1_out".
Definition resnet18_bn1_out    : acc (ary '{1} (ary '{64} (ary '{112} (ary '{112} num)))) := vwt "bn1_out".
Definition resnet18_relu1_out  : acc (ary '{1} (ary '{64} (ary '{112} (ary '{112} num)))) := vwt "relu1_out".
Definition resnet18_pool_out   : acc (ary '{1} (ary '{64} (ary '{56} (ary '{56} num)))) := vwt "pool_out".

(* -------------------- Layer 1 : 64 x 56 x 56 -------------------- *)
(* Block 1 : identity shortcut *)
Definition resnet18_l1_b1_w1 : exp (ary '{64} (ary '{64} (ary '{3} (ary '{3} num)))) := vrd "l1_b1_w1".
Definition resnet18_l1_b1_b1 : exp (ary '{64} num) := vrd "l1_b1_b1".
Definition resnet18_l1_b1_w2 : exp (ary '{64} (ary '{64} (ary '{3} (ary '{3} num)))) := vrd "l1_b1_w2".
Definition resnet18_l1_b1_b2 : exp (ary '{64} num) := vrd "l1_b1_b2".
Definition resnet18_l1_b1_bn1_mean : exp (ary '{64} num) := vrd "l1_b1_bn1_mean".
Definition resnet18_l1_b1_bn1_var  : exp (ary '{64} num) := vrd "l1_b1_bn1_var".
Definition resnet18_l1_b1_bn1_gamma: exp (ary '{64} num) := vrd "l1_b1_bn1_gamma".
Definition resnet18_l1_b1_bn1_beta : exp (ary '{64} num) := vrd "l1_b1_bn1_beta".
Definition resnet18_l1_b1_bn2_mean : exp (ary '{64} num) := vrd "l1_b1_bn2_mean".
Definition resnet18_l1_b1_bn2_var  : exp (ary '{64} num) := vrd "l1_b1_bn2_var".
Definition resnet18_l1_b1_bn2_gamma: exp (ary '{64} num) := vrd "l1_b1_bn2_gamma".
Definition resnet18_l1_b1_bn2_beta : exp (ary '{64} num) := vrd "l1_b1_bn2_beta".
Definition resnet18_l1_b1_conv1_out : acc (ary '{1} (ary '{64} (ary '{56} (ary '{56} num)))) := vwt "l1_b1_conv1_out".
Definition resnet18_l1_b1_bn1_out   : acc (ary '{1} (ary '{64} (ary '{56} (ary '{56} num)))) := vwt "l1_b1_bn1_out".
Definition resnet18_l1_b1_relu1_out : acc (ary '{1} (ary '{64} (ary '{56} (ary '{56} num)))) := vwt "l1_b1_relu1_out".
Definition resnet18_l1_b1_conv2_out : acc (ary '{1} (ary '{64} (ary '{56} (ary '{56} num)))) := vwt "l1_b1_conv2_out".
Definition resnet18_l1_b1_bn2_out   : acc (ary '{1} (ary '{64} (ary '{56} (ary '{56} num)))) := vwt "l1_b1_bn2_out".
Definition resnet18_l1_b1_add_out   : acc (ary '{1} (ary '{64} (ary '{56} (ary '{56} num)))) := vwt "l1_b1_add_out".

(* Block 2 : identity shortcut *)
Definition resnet18_l1_b2_w1 : exp (ary '{64} (ary '{64} (ary '{3} (ary '{3} num)))) := vrd "l1_b2_w1".
Definition resnet18_l1_b2_b1 : exp (ary '{64} num) := vrd "l1_b2_b1".
Definition resnet18_l1_b2_w2 : exp (ary '{64} (ary '{64} (ary '{3} (ary '{3} num)))) := vrd "l1_b2_w2".
Definition resnet18_l1_b2_b2 : exp (ary '{64} num) := vrd "l1_b2_b2".
Definition resnet18_l1_b2_bn1_mean : exp (ary '{64} num) := vrd "l1_b2_bn1_mean".
Definition resnet18_l1_b2_bn1_var  : exp (ary '{64} num) := vrd "l1_b2_bn1_var".
Definition resnet18_l1_b2_bn1_gamma: exp (ary '{64} num) := vrd "l1_b2_bn1_gamma".
Definition resnet18_l1_b2_bn1_beta : exp (ary '{64} num) := vrd "l1_b2_bn1_beta".
Definition resnet18_l1_b2_bn2_mean : exp (ary '{64} num) := vrd "l1_b2_bn2_mean".
Definition resnet18_l1_b2_bn2_var  : exp (ary '{64} num) := vrd "l1_b2_bn2_var".
Definition resnet18_l1_b2_bn2_gamma: exp (ary '{64} num) := vrd "l1_b2_bn2_gamma".
Definition resnet18_l1_b2_bn2_beta : exp (ary '{64} num) := vrd "l1_b2_bn2_beta".
Definition resnet18_l1_b2_conv1_out : acc (ary '{1} (ary '{64} (ary '{56} (ary '{56} num)))) := vwt "l1_b2_conv1_out".
Definition resnet18_l1_b2_bn1_out   : acc (ary '{1} (ary '{64} (ary '{56} (ary '{56} num)))) := vwt "l1_b2_bn1_out".
Definition resnet18_l1_b2_relu1_out : acc (ary '{1} (ary '{64} (ary '{56} (ary '{56} num)))) := vwt "l1_b2_relu1_out".
Definition resnet18_l1_b2_conv2_out : acc (ary '{1} (ary '{64} (ary '{56} (ary '{56} num)))) := vwt "l1_b2_conv2_out".
Definition resnet18_l1_b2_bn2_out   : acc (ary '{1} (ary '{64} (ary '{56} (ary '{56} num)))) := vwt "l1_b2_bn2_out".
Definition resnet18_l1_b2_add_out   : acc (ary '{1} (ary '{64} (ary '{56} (ary '{56} num)))) := vwt "l1_b2_add_out".

(* -------------------- Layer 2 : 128 x 28 x 28 -------------------- *)
(* Block 1 : projection shortcut *)
Definition resnet18_l2_b1_w1 : exp (ary '{128} (ary '{64} (ary '{3} (ary '{3} num)))) := vrd "l2_b1_w1".
Definition resnet18_l2_b1_b1 : exp (ary '{128} num) := vrd "l2_b1_b1".
Definition resnet18_l2_b1_w2 : exp (ary '{128} (ary '{128} (ary '{3} (ary '{3} num)))) := vrd "l2_b1_w2".
Definition resnet18_l2_b1_b2 : exp (ary '{128} num) := vrd "l2_b1_b2".
Definition resnet18_l2_b1_bn1_mean : exp (ary '{128} num) := vrd "l2_b1_bn1_mean".
Definition resnet18_l2_b1_bn1_var  : exp (ary '{128} num) := vrd "l2_b1_bn1_var".
Definition resnet18_l2_b1_bn1_gamma: exp (ary '{128} num) := vrd "l2_b1_bn1_gamma".
Definition resnet18_l2_b1_bn1_beta : exp (ary '{128} num) := vrd "l2_b1_bn1_beta".
Definition resnet18_l2_b1_bn2_mean : exp (ary '{128} num) := vrd "l2_b1_bn2_mean".
Definition resnet18_l2_b1_bn2_var  : exp (ary '{128} num) := vrd "l2_b1_bn2_var".
Definition resnet18_l2_b1_bn2_gamma: exp (ary '{128} num) := vrd "l2_b1_bn2_gamma".
Definition resnet18_l2_b1_bn2_beta : exp (ary '{128} num) := vrd "l2_b1_bn2_beta".
Definition resnet18_l2_b1_shortcut_w : exp (ary '{128} (ary '{64} (ary '{1} (ary '{1} num)))) := vrd "l2_b1_shortcut_w".
Definition resnet18_l2_b1_shortcut_b : exp (ary '{128} num) := vrd "l2_b1_shortcut_b".
Definition resnet18_l2_b1_shortcut_mean : exp (ary '{128} num) := vrd "l2_b1_shortcut_mean".
Definition resnet18_l2_b1_shortcut_var  : exp (ary '{128} num) := vrd "l2_b1_shortcut_var".
Definition resnet18_l2_b1_shortcut_gamma: exp (ary '{128} num) := vrd "l2_b1_shortcut_gamma".
Definition resnet18_l2_b1_shortcut_beta : exp (ary '{128} num) := vrd "l2_b1_shortcut_beta".
Definition resnet18_l2_b1_shortcut_out : acc (ary '{1} (ary '{128} (ary '{28} (ary '{28} num)))) := vwt "l2_b1_shortcut_out".
Definition resnet18_l2_b1_conv1_out : acc (ary '{1} (ary '{128} (ary '{28} (ary '{28} num)))) := vwt "l2_b1_conv1_out".
Definition resnet18_l2_b1_bn1_out   : acc (ary '{1} (ary '{128} (ary '{28} (ary '{28} num)))) := vwt "l2_b1_bn1_out".
Definition resnet18_l2_b1_relu1_out : acc (ary '{1} (ary '{128} (ary '{28} (ary '{28} num)))) := vwt "l2_b1_relu1_out".
Definition resnet18_l2_b1_conv2_out : acc (ary '{1} (ary '{128} (ary '{28} (ary '{28} num)))) := vwt "l2_b1_conv2_out".
Definition resnet18_l2_b1_bn2_out   : acc (ary '{1} (ary '{128} (ary '{28} (ary '{28} num)))) := vwt "l2_b1_bn2_out".
Definition resnet18_l2_b1_add_out   : acc (ary '{1} (ary '{128} (ary '{28} (ary '{28} num)))) := vwt "l2_b1_add_out".

(* Block 2 : identity shortcut *)
Definition resnet18_l2_b2_w1 : exp (ary '{128} (ary '{128} (ary '{3} (ary '{3} num)))) := vrd "l2_b2_w1".
Definition resnet18_l2_b2_b1 : exp (ary '{128} num) := vrd "l2_b2_b1".
Definition resnet18_l2_b2_w2 : exp (ary '{128} (ary '{128} (ary '{3} (ary '{3} num)))) := vrd "l2_b2_w2".
Definition resnet18_l2_b2_b2 : exp (ary '{128} num) := vrd "l2_b2_b2".
Definition resnet18_l2_b2_bn1_mean : exp (ary '{128} num) := vrd "l2_b2_bn1_mean".
Definition resnet18_l2_b2_bn1_var  : exp (ary '{128} num) := vrd "l2_b2_bn1_var".
Definition resnet18_l2_b2_bn1_gamma: exp (ary '{128} num) := vrd "l2_b2_bn1_gamma".
Definition resnet18_l2_b2_bn1_beta : exp (ary '{128} num) := vrd "l2_b2_bn1_beta".
Definition resnet18_l2_b2_bn2_mean : exp (ary '{128} num) := vrd "l2_b2_bn2_mean".
Definition resnet18_l2_b2_bn2_var  : exp (ary '{128} num) := vrd "l2_b2_bn2_var".
Definition resnet18_l2_b2_bn2_gamma: exp (ary '{128} num) := vrd "l2_b2_bn2_gamma".
Definition resnet18_l2_b2_bn2_beta : exp (ary '{128} num) := vrd "l2_b2_bn2_beta".
Definition resnet18_l2_b2_conv1_out : acc (ary '{1} (ary '{128} (ary '{28} (ary '{28} num)))) := vwt "l2_b2_conv1_out".
Definition resnet18_l2_b2_bn1_out   : acc (ary '{1} (ary '{128} (ary '{28} (ary '{28} num)))) := vwt "l2_b2_bn1_out".
Definition resnet18_l2_b2_relu1_out : acc (ary '{1} (ary '{128} (ary '{28} (ary '{28} num)))) := vwt "l2_b2_relu1_out".
Definition resnet18_l2_b2_conv2_out : acc (ary '{1} (ary '{128} (ary '{28} (ary '{28} num)))) := vwt "l2_b2_conv2_out".
Definition resnet18_l2_b2_bn2_out   : acc (ary '{1} (ary '{128} (ary '{28} (ary '{28} num)))) := vwt "l2_b2_bn2_out".
Definition resnet18_l2_b2_add_out   : acc (ary '{1} (ary '{128} (ary '{28} (ary '{28} num)))) := vwt "l2_b2_add_out".

(* -------------------- Layer 3 : 256 x 14 x 14 -------------------- *)
(* Block 1 : projection shortcut *)
Definition resnet18_l3_b1_w1 : exp (ary '{256} (ary '{128} (ary '{3} (ary '{3} num)))) := vrd "l3_b1_w1".
Definition resnet18_l3_b1_b1 : exp (ary '{256} num) := vrd "l3_b1_b1".
Definition resnet18_l3_b1_w2 : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))) := vrd "l3_b1_w2".
Definition resnet18_l3_b1_b2 : exp (ary '{256} num) := vrd "l3_b1_b2".
Definition resnet18_l3_b1_bn1_mean : exp (ary '{256} num) := vrd "l3_b1_bn1_mean".
Definition resnet18_l3_b1_bn1_var  : exp (ary '{256} num) := vrd "l3_b1_bn1_var".
Definition resnet18_l3_b1_bn1_gamma: exp (ary '{256} num) := vrd "l3_b1_bn1_gamma".
Definition resnet18_l3_b1_bn1_beta : exp (ary '{256} num) := vrd "l3_b1_bn1_beta".
Definition resnet18_l3_b1_bn2_mean : exp (ary '{256} num) := vrd "l3_b1_bn2_mean".
Definition resnet18_l3_b1_bn2_var  : exp (ary '{256} num) := vrd "l3_b1_bn2_var".
Definition resnet18_l3_b1_bn2_gamma: exp (ary '{256} num) := vrd "l3_b1_bn2_gamma".
Definition resnet18_l3_b1_bn2_beta : exp (ary '{256} num) := vrd "l3_b1_bn2_beta".
Definition resnet18_l3_b1_shortcut_w : exp (ary '{256} (ary '{128} (ary '{1} (ary '{1} num)))) := vrd "l3_b1_shortcut_w".
Definition resnet18_l3_b1_shortcut_b : exp (ary '{256} num) := vrd "l3_b1_shortcut_b".
Definition resnet18_l3_b1_shortcut_mean : exp (ary '{256} num) := vrd "l3_b1_shortcut_mean".
Definition resnet18_l3_b1_shortcut_var  : exp (ary '{256} num) := vrd "l3_b1_shortcut_var".
Definition resnet18_l3_b1_shortcut_gamma: exp (ary '{256} num) := vrd "l3_b1_shortcut_gamma".
Definition resnet18_l3_b1_shortcut_beta : exp (ary '{256} num) := vrd "l3_b1_shortcut_beta".
Definition resnet18_l3_b1_shortcut_out : acc (ary '{1} (ary '{256} (ary '{14} (ary '{14} num)))) := vwt "l3_b1_shortcut_out".
Definition resnet18_l3_b1_conv1_out : acc (ary '{1} (ary '{256} (ary '{14} (ary '{14} num)))) := vwt "l3_b1_conv1_out".
Definition resnet18_l3_b1_bn1_out   : acc (ary '{1} (ary '{256} (ary '{14} (ary '{14} num)))) := vwt "l3_b1_bn1_out".
Definition resnet18_l3_b1_relu1_out : acc (ary '{1} (ary '{256} (ary '{14} (ary '{14} num)))) := vwt "l3_b1_relu1_out".
Definition resnet18_l3_b1_conv2_out : acc (ary '{1} (ary '{256} (ary '{14} (ary '{14} num)))) := vwt "l3_b1_conv2_out".
Definition resnet18_l3_b1_bn2_out   : acc (ary '{1} (ary '{256} (ary '{14} (ary '{14} num)))) := vwt "l3_b1_bn2_out".
Definition resnet18_l3_b1_add_out   : acc (ary '{1} (ary '{256} (ary '{14} (ary '{14} num)))) := vwt "l3_b1_add_out".

(* Block 2 : identity shortcut *)
Definition resnet18_l3_b2_w1 : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))) := vrd "l3_b2_w1".
Definition resnet18_l3_b2_b1 : exp (ary '{256} num) := vrd "l3_b2_b1".
Definition resnet18_l3_b2_w2 : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))) := vrd "l3_b2_w2".
Definition resnet18_l3_b2_b2 : exp (ary '{256} num) := vrd "l3_b2_b2".
Definition resnet18_l3_b2_bn1_mean : exp (ary '{256} num) := vrd "l3_b2_bn1_mean".
Definition resnet18_l3_b2_bn1_var  : exp (ary '{256} num) := vrd "l3_b2_bn1_var".
Definition resnet18_l3_b2_bn1_gamma: exp (ary '{256} num) := vrd "l3_b2_bn1_gamma".
Definition resnet18_l3_b2_bn1_beta : exp (ary '{256} num) := vrd "l3_b2_bn1_beta".
Definition resnet18_l3_b2_bn2_mean : exp (ary '{256} num) := vrd "l3_b2_bn2_mean".
Definition resnet18_l3_b2_bn2_var  : exp (ary '{256} num) := vrd "l3_b2_bn2_var".
Definition resnet18_l3_b2_bn2_gamma: exp (ary '{256} num) := vrd "l3_b2_bn2_gamma".
Definition resnet18_l3_b2_bn2_beta : exp (ary '{256} num) := vrd "l3_b2_bn2_beta".
Definition resnet18_l3_b2_conv1_out : acc (ary '{1} (ary '{256} (ary '{14} (ary '{14} num)))) := vwt "l3_b2_conv1_out".
Definition resnet18_l3_b2_bn1_out   : acc (ary '{1} (ary '{256} (ary '{14} (ary '{14} num)))) := vwt "l3_b2_bn1_out".
Definition resnet18_l3_b2_relu1_out : acc (ary '{1} (ary '{256} (ary '{14} (ary '{14} num)))) := vwt "l3_b2_relu1_out".
Definition resnet18_l3_b2_conv2_out : acc (ary '{1} (ary '{256} (ary '{14} (ary '{14} num)))) := vwt "l3_b2_conv2_out".
Definition resnet18_l3_b2_bn2_out   : acc (ary '{1} (ary '{256} (ary '{14} (ary '{14} num)))) := vwt "l3_b2_bn2_out".
Definition resnet18_l3_b2_add_out   : acc (ary '{1} (ary '{256} (ary '{14} (ary '{14} num)))) := vwt "l3_b2_add_out".

(* -------------------- Layer 4 : 512 x 7 x 7 -------------------- *)
(* Block 1 : projection shortcut *)
Definition resnet18_l4_b1_w1 : exp (ary '{512} (ary '{256} (ary '{3} (ary '{3} num)))) := vrd "l4_b1_w1".
Definition resnet18_l4_b1_b1 : exp (ary '{512} num) := vrd "l4_b1_b1".
Definition resnet18_l4_b1_w2 : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))) := vrd "l4_b1_w2".
Definition resnet18_l4_b1_b2 : exp (ary '{512} num) := vrd "l4_b1_b2".
Definition resnet18_l4_b1_bn1_mean : exp (ary '{512} num) := vrd "l4_b1_bn1_mean".
Definition resnet18_l4_b1_bn1_var  : exp (ary '{512} num) := vrd "l4_b1_bn1_var".
Definition resnet18_l4_b1_bn1_gamma: exp (ary '{512} num) := vrd "l4_b1_bn1_gamma".
Definition resnet18_l4_b1_bn1_beta : exp (ary '{512} num) := vrd "l4_b1_bn1_beta".
Definition resnet18_l4_b1_bn2_mean : exp (ary '{512} num) := vrd "l4_b1_bn2_mean".
Definition resnet18_l4_b1_bn2_var  : exp (ary '{512} num) := vrd "l4_b1_bn2_var".
Definition resnet18_l4_b1_bn2_gamma: exp (ary '{512} num) := vrd "l4_b1_bn2_gamma".
Definition resnet18_l4_b1_bn2_beta : exp (ary '{512} num) := vrd "l4_b1_bn2_beta".
Definition resnet18_l4_b1_shortcut_w : exp (ary '{512} (ary '{256} (ary '{1} (ary '{1} num)))) := vrd "l4_b1_shortcut_w".
Definition resnet18_l4_b1_shortcut_b : exp (ary '{512} num) := vrd "l4_b1_shortcut_b".
Definition resnet18_l4_b1_shortcut_mean : exp (ary '{512} num) := vrd "l4_b1_shortcut_mean".
Definition resnet18_l4_b1_shortcut_var  : exp (ary '{512} num) := vrd "l4_b1_shortcut_var".
Definition resnet18_l4_b1_shortcut_gamma: exp (ary '{512} num) := vrd "l4_b1_shortcut_gamma".
Definition resnet18_l4_b1_shortcut_beta : exp (ary '{512} num) := vrd "l4_b1_shortcut_beta".
Definition resnet18_l4_b1_shortcut_out : acc (ary '{1} (ary '{512} (ary '{7} (ary '{7} num)))) := vwt "l4_b1_shortcut_out".
Definition resnet18_l4_b1_conv1_out : acc (ary '{1} (ary '{512} (ary '{7} (ary '{7} num)))) := vwt "l4_b1_conv1_out".
Definition resnet18_l4_b1_bn1_out   : acc (ary '{1} (ary '{512} (ary '{7} (ary '{7} num)))) := vwt "l4_b1_bn1_out".
Definition resnet18_l4_b1_relu1_out : acc (ary '{1} (ary '{512} (ary '{7} (ary '{7} num)))) := vwt "l4_b1_relu1_out".
Definition resnet18_l4_b1_conv2_out : acc (ary '{1} (ary '{512} (ary '{7} (ary '{7} num)))) := vwt "l4_b1_conv2_out".
Definition resnet18_l4_b1_bn2_out   : acc (ary '{1} (ary '{512} (ary '{7} (ary '{7} num)))) := vwt "l4_b1_bn2_out".
Definition resnet18_l4_b1_add_out   : acc (ary '{1} (ary '{512} (ary '{7} (ary '{7} num)))) := vwt "l4_b1_add_out".

(* Block 2 : identity shortcut *)
Definition resnet18_l4_b2_w1 : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))) := vrd "l4_b2_w1".
Definition resnet18_l4_b2_b1 : exp (ary '{512} num) := vrd "l4_b2_b1".
Definition resnet18_l4_b2_w2 : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))) := vrd "l4_b2_w2".
Definition resnet18_l4_b2_b2 : exp (ary '{512} num) := vrd "l4_b2_b2".
Definition resnet18_l4_b2_bn1_mean : exp (ary '{512} num) := vrd "l4_b2_bn1_mean".
Definition resnet18_l4_b2_bn1_var  : exp (ary '{512} num) := vrd "l4_b2_bn1_var".
Definition resnet18_l4_b2_bn1_gamma: exp (ary '{512} num) := vrd "l4_b2_bn1_gamma".
Definition resnet18_l4_b2_bn1_beta : exp (ary '{512} num) := vrd "l4_b2_bn1_beta".
Definition resnet18_l4_b2_bn2_mean : exp (ary '{512} num) := vrd "l4_b2_bn2_mean".
Definition resnet18_l4_b2_bn2_var  : exp (ary '{512} num) := vrd "l4_b2_bn2_var".
Definition resnet18_l4_b2_bn2_gamma: exp (ary '{512} num) := vrd "l4_b2_bn2_gamma".
Definition resnet18_l4_b2_bn2_beta : exp (ary '{512} num) := vrd "l4_b2_bn2_beta".
Definition resnet18_l4_b2_conv1_out : acc (ary '{1} (ary '{512} (ary '{7} (ary '{7} num)))) := vwt "l4_b2_conv1_out".
Definition resnet18_l4_b2_bn1_out   : acc (ary '{1} (ary '{512} (ary '{7} (ary '{7} num)))) := vwt "l4_b2_bn1_out".
Definition resnet18_l4_b2_relu1_out : acc (ary '{1} (ary '{512} (ary '{7} (ary '{7} num)))) := vwt "l4_b2_relu1_out".
Definition resnet18_l4_b2_conv2_out : acc (ary '{1} (ary '{512} (ary '{7} (ary '{7} num)))) := vwt "l4_b2_conv2_out".
Definition resnet18_l4_b2_bn2_out   : acc (ary '{1} (ary '{512} (ary '{7} (ary '{7} num)))) := vwt "l4_b2_bn2_out".
Definition resnet18_l4_b2_add_out   : acc (ary '{1} (ary '{512} (ary '{7} (ary '{7} num)))) := vwt "l4_b2_add_out".

(* -------------------- Classifier -------------------- *)
Definition resnet18_avgpool_out : acc (ary '{1} (ary '{512} num)) := vwt "avgpool_out".
Definition resnet18_fc_w        : exp (ary '{1000} (ary '{512} num)) := vrd "fc_w".
Definition resnet18_fc_b        : exp (ary '{1000} num) := vrd "fc_b".
Definition resnet18_output      : acc (ary '{1} (ary '{1000} num)) := vwt "output".

(* -------------------- Full network -------------------- *)
Definition resnet18_comm : comm :=
  @Conv4d_p3_k7_s2_comm 1 3 64 224 resnet18_input resnet18_conv1_w resnet18_conv1_b resnet18_conv1_out ';
  @BatchNorm4d_comm 1 64 112 112 (vrd "conv1_out") resnet18_bn1_mean resnet18_bn1_var resnet18_bn1_gamma resnet18_bn1_beta resnet18_eps resnet18_bn1_out ';
  @ReLU4d_comm 1 64 112 112 (vrd "bn1_out") resnet18_relu1_out ';
  @MaxPool4d_pad_comm 1 64 112 3 2 1 (vrd "relu1_out") resnet18_pool_out ';

  @ResNet_BB_id_comm 1 64 56
    (vrd "pool_out")
    resnet18_l1_b1_w1 resnet18_l1_b1_b1 resnet18_l1_b1_w2 resnet18_l1_b1_b2
    resnet18_l1_b1_bn1_mean resnet18_l1_b1_bn1_var resnet18_l1_b1_bn1_gamma resnet18_l1_b1_bn1_beta
    resnet18_l1_b1_bn2_mean resnet18_l1_b1_bn2_var resnet18_l1_b1_bn2_gamma resnet18_l1_b1_bn2_beta
    resnet18_eps
    resnet18_l1_b1_conv1_out resnet18_l1_b1_bn1_out resnet18_l1_b1_relu1_out
    resnet18_l1_b1_conv2_out resnet18_l1_b1_bn2_out resnet18_l1_b1_add_out
    "l1_b1_conv1_out" "l1_b1_bn1_out" "l1_b1_relu1_out" "l1_b1_conv2_out" "l1_b1_bn2_out" "l1_b1_add_out" ';

  @ResNet_BB_id_comm 1 64 56
    (vrd "l1_b1_add_out")
    resnet18_l1_b2_w1 resnet18_l1_b2_b1 resnet18_l1_b2_w2 resnet18_l1_b2_b2
    resnet18_l1_b2_bn1_mean resnet18_l1_b2_bn1_var resnet18_l1_b2_bn1_gamma resnet18_l1_b2_bn1_beta
    resnet18_l1_b2_bn2_mean resnet18_l1_b2_bn2_var resnet18_l1_b2_bn2_gamma resnet18_l1_b2_bn2_beta
    resnet18_eps
    resnet18_l1_b2_conv1_out resnet18_l1_b2_bn1_out resnet18_l1_b2_relu1_out
    resnet18_l1_b2_conv2_out resnet18_l1_b2_bn2_out resnet18_l1_b2_add_out
    "l1_b2_conv1_out" "l1_b2_bn1_out" "l1_b2_relu1_out" "l1_b2_conv2_out" "l1_b2_bn2_out" "l1_b2_add_out" ';

  @ResNet_BB_proj_comm 1 64 128 56
    (vrd "l1_b2_add_out")
    resnet18_l2_b1_w1 resnet18_l2_b1_b1 resnet18_l2_b1_w2 resnet18_l2_b1_b2
    resnet18_l2_b1_bn1_mean resnet18_l2_b1_bn1_var resnet18_l2_b1_bn1_gamma resnet18_l2_b1_bn1_beta
    resnet18_l2_b1_bn2_mean resnet18_l2_b1_bn2_var resnet18_l2_b1_bn2_gamma resnet18_l2_b1_bn2_beta
    resnet18_eps
    resnet18_l2_b1_conv1_out resnet18_l2_b1_bn1_out resnet18_l2_b1_relu1_out
    resnet18_l2_b1_conv2_out resnet18_l2_b1_bn2_out resnet18_l2_b1_add_out
    resnet18_l2_b1_shortcut_out
    resnet18_l2_b1_shortcut_w resnet18_l2_b1_shortcut_b
    resnet18_l2_b1_shortcut_mean resnet18_l2_b1_shortcut_var
    resnet18_l2_b1_shortcut_gamma resnet18_l2_b1_shortcut_beta
    "l2_b1_shortcut_out" "l2_b1_conv1_out" "l2_b1_bn1_out" "l2_b1_relu1_out"
    "l2_b1_conv2_out" "l2_b1_bn2_out" "l2_b1_add_out" ';

  @ResNet_BB_id_comm 1 128 28
    (vrd "l2_b1_add_out")
    resnet18_l2_b2_w1 resnet18_l2_b2_b1 resnet18_l2_b2_w2 resnet18_l2_b2_b2
    resnet18_l2_b2_bn1_mean resnet18_l2_b2_bn1_var resnet18_l2_b2_bn1_gamma resnet18_l2_b2_bn1_beta
    resnet18_l2_b2_bn2_mean resnet18_l2_b2_bn2_var resnet18_l2_b2_bn2_gamma resnet18_l2_b2_bn2_beta
    resnet18_eps
    resnet18_l2_b2_conv1_out resnet18_l2_b2_bn1_out resnet18_l2_b2_relu1_out
    resnet18_l2_b2_conv2_out resnet18_l2_b2_bn2_out resnet18_l2_b2_add_out
    "l2_b2_conv1_out" "l2_b2_bn1_out" "l2_b2_relu1_out" "l2_b2_conv2_out" "l2_b2_bn2_out" "l2_b2_add_out" ';

  @ResNet_BB_proj_comm 1 128 256 28
    (vrd "l2_b2_add_out")
    resnet18_l3_b1_w1 resnet18_l3_b1_b1 resnet18_l3_b1_w2 resnet18_l3_b1_b2
    resnet18_l3_b1_bn1_mean resnet18_l3_b1_bn1_var resnet18_l3_b1_bn1_gamma resnet18_l3_b1_bn1_beta
    resnet18_l3_b1_bn2_mean resnet18_l3_b1_bn2_var resnet18_l3_b1_bn2_gamma resnet18_l3_b1_bn2_beta
    resnet18_eps
    resnet18_l3_b1_conv1_out resnet18_l3_b1_bn1_out resnet18_l3_b1_relu1_out
    resnet18_l3_b1_conv2_out resnet18_l3_b1_bn2_out resnet18_l3_b1_add_out
    resnet18_l3_b1_shortcut_out
    resnet18_l3_b1_shortcut_w resnet18_l3_b1_shortcut_b
    resnet18_l3_b1_shortcut_mean resnet18_l3_b1_shortcut_var
    resnet18_l3_b1_shortcut_gamma resnet18_l3_b1_shortcut_beta
    "l3_b1_shortcut_out" "l3_b1_conv1_out" "l3_b1_bn1_out" "l3_b1_relu1_out"
    "l3_b1_conv2_out" "l3_b1_bn2_out" "l3_b1_add_out" ';

  @ResNet_BB_id_comm 1 256 14
    (vrd "l3_b1_add_out")
    resnet18_l3_b2_w1 resnet18_l3_b2_b1 resnet18_l3_b2_w2 resnet18_l3_b2_b2
    resnet18_l3_b2_bn1_mean resnet18_l3_b2_bn1_var resnet18_l3_b2_bn1_gamma resnet18_l3_b2_bn1_beta
    resnet18_l3_b2_bn2_mean resnet18_l3_b2_bn2_var resnet18_l3_b2_bn2_gamma resnet18_l3_b2_bn2_beta
    resnet18_eps
    resnet18_l3_b2_conv1_out resnet18_l3_b2_bn1_out resnet18_l3_b2_relu1_out
    resnet18_l3_b2_conv2_out resnet18_l3_b2_bn2_out resnet18_l3_b2_add_out
    "l3_b2_conv1_out" "l3_b2_bn1_out" "l3_b2_relu1_out" "l3_b2_conv2_out" "l3_b2_bn2_out" "l3_b2_add_out" ';

  @ResNet_BB_proj_comm 1 256 512 14
    (vrd "l3_b2_add_out")
    resnet18_l4_b1_w1 resnet18_l4_b1_b1 resnet18_l4_b1_w2 resnet18_l4_b1_b2
    resnet18_l4_b1_bn1_mean resnet18_l4_b1_bn1_var resnet18_l4_b1_bn1_gamma resnet18_l4_b1_bn1_beta
    resnet18_l4_b1_bn2_mean resnet18_l4_b1_bn2_var resnet18_l4_b1_bn2_gamma resnet18_l4_b1_bn2_beta
    resnet18_eps
    resnet18_l4_b1_conv1_out resnet18_l4_b1_bn1_out resnet18_l4_b1_relu1_out
    resnet18_l4_b1_conv2_out resnet18_l4_b1_bn2_out resnet18_l4_b1_add_out
    resnet18_l4_b1_shortcut_out
    resnet18_l4_b1_shortcut_w resnet18_l4_b1_shortcut_b
    resnet18_l4_b1_shortcut_mean resnet18_l4_b1_shortcut_var
    resnet18_l4_b1_shortcut_gamma resnet18_l4_b1_shortcut_beta
    "l4_b1_shortcut_out" "l4_b1_conv1_out" "l4_b1_bn1_out" "l4_b1_relu1_out"
    "l4_b1_conv2_out" "l4_b1_bn2_out" "l4_b1_add_out" ';

  @ResNet_BB_id_comm 1 512 7
    (vrd "l4_b1_add_out")
    resnet18_l4_b2_w1 resnet18_l4_b2_b1 resnet18_l4_b2_w2 resnet18_l4_b2_b2
    resnet18_l4_b2_bn1_mean resnet18_l4_b2_bn1_var resnet18_l4_b2_bn1_gamma resnet18_l4_b2_bn1_beta
    resnet18_l4_b2_bn2_mean resnet18_l4_b2_bn2_var resnet18_l4_b2_bn2_gamma resnet18_l4_b2_bn2_beta
    resnet18_eps
    resnet18_l4_b2_conv1_out resnet18_l4_b2_bn1_out resnet18_l4_b2_relu1_out
    resnet18_l4_b2_conv2_out resnet18_l4_b2_bn2_out resnet18_l4_b2_add_out
    "l4_b2_conv1_out" "l4_b2_bn1_out" "l4_b2_relu1_out" "l4_b2_conv2_out" "l4_b2_bn2_out" "l4_b2_add_out" ';

  @GlobalAvgPool4d_comm 1 512 7 7 (vrd "l4_b2_add_out") resnet18_avgpool_out ';
  @Linear2d_comm 1 512 1000 resnet18_fc_w resnet18_fc_b (vrd "avgpool_out") resnet18_output.
