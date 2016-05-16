Require Import Verdi.
Require Import FunctionalExtensionality.
Require Import Serialized.
Require Import Cheerios.Types.

Section SerializedCorrect.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.
  Context {orig_data_serializer : Serializer data}.
  Context {orig_input_serializer : Serializer input}.
  Context {orig_output_serializer : Serializer output}.
  Context {orig_msg_serializer : Serializer msg}.

  Definition orig_packet := @packet _ orig_multi_params.
  Definition orig_network := @network _ orig_multi_params.
  Definition serialized_packet := @packet _ multi_params.
  Definition serialized_network := @network _ multi_params.

  Definition revertPacket (p : serialized_packet) : orig_packet :=
    @mkPacket _ orig_multi_params (pSrc p) (pDst p) (serialize (pBody p)).
