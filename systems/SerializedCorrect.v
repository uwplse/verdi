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

  Definition revertPacket (p : serialized_packet) : option orig_packet :=
    match (deserialize (pBody p)) with
    | None => None
    | Some (body, rest) =>
      Some (@mkPacket _ orig_multi_params (pSrc p) (pDst p) body)
    end.

  Fixpoint filteredMap {A B: Type} (mapFun: A -> option B) (xs: list A) : list B :=
    match xs with
    | nil => nil
    | hd :: tl =>
      match mapFun hd with
      | None => filteredMap mapFun tl 
      | Some x => x :: filteredMap mapFun tl
      end
    end.

  Definition revertNetwork (net: serialized_network) : orig_network :=
    mkNetwork
      (filteredMap revertPacket (nwPackets net))
      (fun h => match (deserialize (nwState net h)) with
             | Some (data, rest) => data
             | None => 
             end).
