(* ImageNet VGG-16 imperative AST. *)

Require Import Ionia.CNN_Examples_Base.
Require Import Logic.FunctionalExtensionality.

From Stdlib Require Import List String.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.
Opaque CG_acc CG_exp.

Definition vgg16_input : exp (ary '{1} (ary '{3} (ary '{224} (ary '{224} num)))) := vrd "input".

Definition vgg16_conv1_1_w : exp (ary '{64} (ary '{3} (ary '{3} (ary '{3} num)))) := vrd "conv1_1_w".
Definition vgg16_conv1_1_b : exp (ary '{64} num) := vrd "conv1_1_b".
Definition vgg16_conv1_1_out : acc (ary '{1} (ary '{64} (ary '{224} (ary '{224} num)))) := vwt "conv1_1_out".
Definition vgg16_relu1_1_out : acc (ary '{1} (ary '{64} (ary '{224} (ary '{224} num)))) := vwt "relu1_1_out".
Definition vgg16_conv1_2_w : exp (ary '{64} (ary '{64} (ary '{3} (ary '{3} num)))) := vrd "conv1_2_w".
Definition vgg16_conv1_2_b : exp (ary '{64} num) := vrd "conv1_2_b".
Definition vgg16_conv1_2_out : acc (ary '{1} (ary '{64} (ary '{224} (ary '{224} num)))) := vwt "conv1_2_out".
Definition vgg16_relu1_2_out : acc (ary '{1} (ary '{64} (ary '{224} (ary '{224} num)))) := vwt "relu1_2_out".
Definition vgg16_conv2_1_w : exp (ary '{128} (ary '{64} (ary '{3} (ary '{3} num)))) := vrd "conv2_1_w".
Definition vgg16_conv2_1_b : exp (ary '{128} num) := vrd "conv2_1_b".
Definition vgg16_conv2_1_out : acc (ary '{1} (ary '{128} (ary '{112} (ary '{112} num)))) := vwt "conv2_1_out".
Definition vgg16_relu2_1_out : acc (ary '{1} (ary '{128} (ary '{112} (ary '{112} num)))) := vwt "relu2_1_out".
Definition vgg16_conv2_2_w : exp (ary '{128} (ary '{128} (ary '{3} (ary '{3} num)))) := vrd "conv2_2_w".
Definition vgg16_conv2_2_b : exp (ary '{128} num) := vrd "conv2_2_b".
Definition vgg16_conv2_2_out : acc (ary '{1} (ary '{128} (ary '{112} (ary '{112} num)))) := vwt "conv2_2_out".
Definition vgg16_relu2_2_out : acc (ary '{1} (ary '{128} (ary '{112} (ary '{112} num)))) := vwt "relu2_2_out".
Definition vgg16_conv3_1_w : exp (ary '{256} (ary '{128} (ary '{3} (ary '{3} num)))) := vrd "conv3_1_w".
Definition vgg16_conv3_1_b : exp (ary '{256} num) := vrd "conv3_1_b".
Definition vgg16_conv3_1_out : acc (ary '{1} (ary '{256} (ary '{56} (ary '{56} num)))) := vwt "conv3_1_out".
Definition vgg16_relu3_1_out : acc (ary '{1} (ary '{256} (ary '{56} (ary '{56} num)))) := vwt "relu3_1_out".
Definition vgg16_conv3_2_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))) := vrd "conv3_2_w".
Definition vgg16_conv3_2_b : exp (ary '{256} num) := vrd "conv3_2_b".
Definition vgg16_conv3_2_out : acc (ary '{1} (ary '{256} (ary '{56} (ary '{56} num)))) := vwt "conv3_2_out".
Definition vgg16_relu3_2_out : acc (ary '{1} (ary '{256} (ary '{56} (ary '{56} num)))) := vwt "relu3_2_out".
Definition vgg16_conv3_3_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))) := vrd "conv3_3_w".
Definition vgg16_conv3_3_b : exp (ary '{256} num) := vrd "conv3_3_b".
Definition vgg16_conv3_3_out : acc (ary '{1} (ary '{256} (ary '{56} (ary '{56} num)))) := vwt "conv3_3_out".
Definition vgg16_relu3_3_out : acc (ary '{1} (ary '{256} (ary '{56} (ary '{56} num)))) := vwt "relu3_3_out".
Definition vgg16_conv4_1_w : exp (ary '{512} (ary '{256} (ary '{3} (ary '{3} num)))) := vrd "conv4_1_w".
Definition vgg16_conv4_1_b : exp (ary '{512} num) := vrd "conv4_1_b".
Definition vgg16_conv4_1_out : acc (ary '{1} (ary '{512} (ary '{28} (ary '{28} num)))) := vwt "conv4_1_out".
Definition vgg16_relu4_1_out : acc (ary '{1} (ary '{512} (ary '{28} (ary '{28} num)))) := vwt "relu4_1_out".
Definition vgg16_conv4_2_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))) := vrd "conv4_2_w".
Definition vgg16_conv4_2_b : exp (ary '{512} num) := vrd "conv4_2_b".
Definition vgg16_conv4_2_out : acc (ary '{1} (ary '{512} (ary '{28} (ary '{28} num)))) := vwt "conv4_2_out".
Definition vgg16_relu4_2_out : acc (ary '{1} (ary '{512} (ary '{28} (ary '{28} num)))) := vwt "relu4_2_out".
Definition vgg16_conv4_3_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))) := vrd "conv4_3_w".
Definition vgg16_conv4_3_b : exp (ary '{512} num) := vrd "conv4_3_b".
Definition vgg16_conv4_3_out : acc (ary '{1} (ary '{512} (ary '{28} (ary '{28} num)))) := vwt "conv4_3_out".
Definition vgg16_relu4_3_out : acc (ary '{1} (ary '{512} (ary '{28} (ary '{28} num)))) := vwt "relu4_3_out".
Definition vgg16_conv5_1_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))) := vrd "conv5_1_w".
Definition vgg16_conv5_1_b : exp (ary '{512} num) := vrd "conv5_1_b".
Definition vgg16_conv5_1_out : acc (ary '{1} (ary '{512} (ary '{14} (ary '{14} num)))) := vwt "conv5_1_out".
Definition vgg16_relu5_1_out : acc (ary '{1} (ary '{512} (ary '{14} (ary '{14} num)))) := vwt "relu5_1_out".
Definition vgg16_conv5_2_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))) := vrd "conv5_2_w".
Definition vgg16_conv5_2_b : exp (ary '{512} num) := vrd "conv5_2_b".
Definition vgg16_conv5_2_out : acc (ary '{1} (ary '{512} (ary '{14} (ary '{14} num)))) := vwt "conv5_2_out".
Definition vgg16_relu5_2_out : acc (ary '{1} (ary '{512} (ary '{14} (ary '{14} num)))) := vwt "relu5_2_out".
Definition vgg16_conv5_3_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))) := vrd "conv5_3_w".
Definition vgg16_conv5_3_b : exp (ary '{512} num) := vrd "conv5_3_b".
Definition vgg16_conv5_3_out : acc (ary '{1} (ary '{512} (ary '{14} (ary '{14} num)))) := vwt "conv5_3_out".
Definition vgg16_relu5_3_out : acc (ary '{1} (ary '{512} (ary '{14} (ary '{14} num)))) := vwt "relu5_3_out".
Definition vgg16_pool1_out : acc (ary '{1} (ary '{64} (ary '{112} (ary '{112} num)))) := vwt "pool1_out".
Definition vgg16_pool2_out : acc (ary '{1} (ary '{128} (ary '{56} (ary '{56} num)))) := vwt "pool2_out".
Definition vgg16_pool3_out : acc (ary '{1} (ary '{256} (ary '{28} (ary '{28} num)))) := vwt "pool3_out".
Definition vgg16_pool4_out : acc (ary '{1} (ary '{512} (ary '{14} (ary '{14} num)))) := vwt "pool4_out".
Definition vgg16_pool5_out : acc (ary '{1} (ary '{512} (ary '{7} (ary '{7} num)))) := vwt "pool5_out".
Definition vgg16_flatten_out : acc (ary '{1} (ary '{25088} num)) := vwt "flatten_out".
Definition vgg16_fc1_w : exp (ary '{4096} (ary '{25088} num)) := vrd "fc1_w".
Definition vgg16_fc1_b : exp (ary '{4096} num) := vrd "fc1_b".
Definition vgg16_fc1_out : acc (ary '{1} (ary '{4096} num)) := vwt "fc1_out".
Definition vgg16_fc1_relu_out : acc (ary '{1} (ary '{4096} num)) := vwt "fc1_relu_out".
Definition vgg16_fc2_w : exp (ary '{4096} (ary '{4096} num)) := vrd "fc2_w".
Definition vgg16_fc2_b : exp (ary '{4096} num) := vrd "fc2_b".
Definition vgg16_fc2_out : acc (ary '{1} (ary '{4096} num)) := vwt "fc2_out".
Definition vgg16_fc2_relu_out : acc (ary '{1} (ary '{4096} num)) := vwt "fc2_relu_out".
Definition vgg16_fc3_w : exp (ary '{1000} (ary '{4096} num)) := vrd "fc3_w".
Definition vgg16_fc3_b : exp (ary '{1000} num) := vrd "fc3_b".
Definition vgg16_output : acc (ary '{1} (ary '{1000} num)) := vwt "output".

Definition vgg16_comm : comm :=
  @Conv4d_p1_k3_comm 1 3 64 224
    vgg16_input vgg16_conv1_1_w vgg16_conv1_1_b vgg16_conv1_1_out ';
  @ReLU4d_comm 1 64 224 224
    (vrd "conv1_1_out") vgg16_relu1_1_out ';
  @Conv4d_p1_k3_comm 1 64 64 224
    (vrd "relu1_1_out") vgg16_conv1_2_w vgg16_conv1_2_b vgg16_conv1_2_out ';
  @ReLU4d_comm 1 64 224 224
    (vrd "conv1_2_out") vgg16_relu1_2_out ';
  @MaxPool4d_k2_comm 1 64 224
    (vrd "relu1_2_out") vgg16_pool1_out ';
  @Conv4d_p1_k3_comm 1 64 128 112
    (vrd "relu1_2_out") vgg16_conv2_1_w vgg16_conv2_1_b vgg16_conv2_1_out ';
  @ReLU4d_comm 1 128 112 112
    (vrd "conv2_1_out") vgg16_relu2_1_out ';
  @Conv4d_p1_k3_comm 1 128 128 112
    (vrd "relu2_1_out") vgg16_conv2_2_w vgg16_conv2_2_b vgg16_conv2_2_out ';
  @ReLU4d_comm 1 128 112 112
    (vrd "conv2_2_out") vgg16_relu2_2_out ';
  @MaxPool4d_k2_comm 1 128 112
    (vrd "relu2_2_out") vgg16_pool2_out ';
  @Conv4d_p1_k3_comm 1 128 256 56
    (vrd "relu2_2_out") vgg16_conv3_1_w vgg16_conv3_1_b vgg16_conv3_1_out ';
  @ReLU4d_comm 1 256 56 56
    (vrd "conv3_1_out") vgg16_relu3_1_out ';
  @Conv4d_p1_k3_comm 1 256 256 56
    (vrd "relu3_1_out") vgg16_conv3_2_w vgg16_conv3_2_b vgg16_conv3_2_out ';
  @ReLU4d_comm 1 256 56 56
    (vrd "conv3_2_out") vgg16_relu3_2_out ';
  @Conv4d_p1_k3_comm 1 256 256 56
    (vrd "relu3_2_out") vgg16_conv3_3_w vgg16_conv3_3_b vgg16_conv3_3_out ';
  @ReLU4d_comm 1 256 56 56
    (vrd "conv3_3_out") vgg16_relu3_3_out ';
  @MaxPool4d_k2_comm 1 256 56
    (vrd "relu3_3_out") vgg16_pool3_out ';
  @Conv4d_p1_k3_comm 1 256 512 28
    (vrd "relu3_3_out") vgg16_conv4_1_w vgg16_conv4_1_b vgg16_conv4_1_out ';
  @ReLU4d_comm 1 512 28 28
    (vrd "conv4_1_out") vgg16_relu4_1_out ';
  @Conv4d_p1_k3_comm 1 512 512 28
    (vrd "relu4_1_out") vgg16_conv4_2_w vgg16_conv4_2_b vgg16_conv4_2_out ';
  @ReLU4d_comm 1 512 28 28
    (vrd "conv4_2_out") vgg16_relu4_2_out ';
  @Conv4d_p1_k3_comm 1 512 512 28
    (vrd "relu4_2_out") vgg16_conv4_3_w vgg16_conv4_3_b vgg16_conv4_3_out ';
  @ReLU4d_comm 1 512 28 28
    (vrd "conv4_3_out") vgg16_relu4_3_out ';
  @MaxPool4d_k2_comm 1 512 28
    (vrd "relu4_3_out") vgg16_pool4_out ';
  @Conv4d_p1_k3_comm 1 512 512 14
    (vrd "relu4_3_out") vgg16_conv5_1_w vgg16_conv5_1_b vgg16_conv5_1_out ';
  @ReLU4d_comm 1 512 14 14
    (vrd "conv5_1_out") vgg16_relu5_1_out ';
  @Conv4d_p1_k3_comm 1 512 512 14
    (vrd "relu5_1_out") vgg16_conv5_2_w vgg16_conv5_2_b vgg16_conv5_2_out ';
  @ReLU4d_comm 1 512 14 14
    (vrd "conv5_2_out") vgg16_relu5_2_out ';
  @Conv4d_p1_k3_comm 1 512 512 14
    (vrd "relu5_2_out") vgg16_conv5_3_w vgg16_conv5_3_b vgg16_conv5_3_out ';
  @ReLU4d_comm 1 512 14 14
    (vrd "conv5_3_out") vgg16_relu5_3_out ';
  @MaxPool4d_k2_comm 1 512 14
    (vrd "relu5_3_out") vgg16_pool5_out ';
  @Flatten4d_comm 1 512 7 7
    (vrd "pool5_out") vgg16_flatten_out ';
  @Linear2d_comm 1 25088 4096
    vgg16_fc1_w vgg16_fc1_b (vrd "flatten_out") vgg16_fc1_out ';
  @ReLU2d_comm 1 4096
    (vrd "fc1_out") vgg16_fc1_relu_out ';
  @Linear2d_comm 1 4096 4096
    vgg16_fc2_w vgg16_fc2_b (vrd "fc1_relu_out") vgg16_fc2_out ';
  @ReLU2d_comm 1 4096
    (vrd "fc2_out") vgg16_fc2_relu_out ';
  @Linear2d_comm 1 4096 1000
    vgg16_fc3_w vgg16_fc3_b (vrd "fc2_relu_out") vgg16_output.
