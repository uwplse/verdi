Require Import List.
Require Import Arith.
Require Import Omega.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import Net.

Class VerySimpleUpdateParams :=
  {
    name : Type ;
    msg : Type ;
    input : Type ;
    output : Type ;
    
    msg_eq_dec : forall x y : msg, {x = y} + {x <> y} ;
    name_eq_dec : forall x y : name, {x = y} + {x <> y} ;
    
    nodes : list name ;
    all_names_nodes : forall n, In n nodes ;
    no_dup_nodes : NoDup nodes ;

    data1 : Type;
    init_handlers : name -> data1 ;
    net_handlers1 : name -> name -> msg -> data1 -> (list output) * data1 * list (name * msg) ;
    input_handlers1 : name -> input -> data1 -> (list output) * data1 * list (name * msg) ;
    reboot1 : data1 -> data1 ;
    
    data2 : Type;
    net_handlers2 : name -> name -> msg -> data2 -> (list output) * data2 * list (name * msg) ;
    input_handlers2 : name -> input -> data2 -> (list output) * data2 * list (name * msg) ;
    reboot2 : data2 -> data2 ;

    upgrade : data1 -> data2
  }.


Section StepVerySimpleUpdate.
  Context `{params : VerySimpleUpdateParams}.

  Inductive version :=
  | One
  | Two.

  Definition data (v : version) : Type :=
    match v with
    | One => data1
    | Two => data2
    end.

  Definition state := sigT data.

  Definition upgrade_state (sigma : state) : state :=
    let (v, d) := sigma in
    match v as v' return (data v' -> state) with
    | One => fun d => existT _ Two (upgrade d)
    | Two => fun d => existT _ Two d
    end d.

  Definition net_handlers  (me : name) (src : name) (m : msg) (sigma : state) :
    list output * state * list (name * msg) :=
    let (v, d) := sigma in
    match v as v' return (data v' -> (list output * state * list (name * msg))) with
    | One =>
      fun d =>
        let '(os, d', ms) := net_handlers1 me src m d in
        (os, existT _ One d', ms)
    | Two =>
      fun d =>
        let '(os, d', ms) := net_handlers2 me src m d in
        (os, existT _ Two d', ms)
    end d.

  Definition input_handlers  (me : name) (inp : input) (sigma : state) :
    list output * state * list (name * msg) :=
    let (v, d) := sigma in
    match v as v' return (data v' -> (list output * state * list (name * msg))) with
    | One =>
      fun d =>
        let '(os, d', ms) := input_handlers1 me inp d in
        (os, existT _ One d', ms)
    | Two =>
      fun d =>
        let '(os, d', ms) := input_handlers2 me inp d in
        (os, existT _ Two d', ms)
    end d.
  
  Definition reboot (sigma: state) : state :=
    let (v, d) := sigma in
    match v as v' return (data v' -> state) with
    | One =>
      fun d =>
        existT _ One (reboot1 d)
    | Two =>
      fun d =>
        existT _ Two (reboot2 d)
    end d.

  Record packet := mkPacket { pSrc  : name;
                              pDst  : name;
                              pBody : msg }.
  
  Record network :=
    mkNetwork
      {
        nwFailed : list name ;
        nwPackets : list packet ;
        nwState : name -> state
      }.

  Definition update {A : Type} st h (v : A) := (fun nm => if name_eq_dec nm h then v else st nm).
  Definition send_packets src ps := (map (fun m => mkPacket src (fst m) (snd m)) ps).


    (* this step relation transforms a list of failed hosts (list name * network), but does not transform handlers (H : hosts) *)
  Inductive step_u : step_relation network (name * (input + list output)) :=
  (* like step_m, but only delivers to hosts that haven't failed yet *)
  | SU_deliver : forall net net' p xs ys out d l,
                nwPackets net = xs ++ p :: ys ->
                ~ In (pDst p) (nwFailed net) ->
                net_handlers (pDst p) (pSrc p) (pBody p)
                             (nwState net (pDst p)) = (out, d, l) ->
                net' = mkNetwork
                         (nwFailed net)
                         (send_packets (pDst p) l ++ xs ++ ys)
                         (update (nwState net) (pDst p) d) ->
                step_u net net' [(pDst p, inr out)]
  | SU_input : forall h net net' out inp d l,
                 ~ In h (nwFailed net) ->
                 input_handlers h inp (nwState net h) = (out, d, l) ->
                 net' = mkNetwork
                          (nwFailed net)
                          (send_packets h l ++ nwPackets net)
                          (update (nwState net) h d) ->
                 step_u net net' [(h, inl inp) ;  (h, inr out)]
  (* drops a packet *)
  | SU_drop : forall net net' p xs ys,
                nwPackets net = xs ++ p :: ys ->
                net' = mkNetwork
                         (nwFailed net)
                         (xs ++ ys)
                         (nwState net) ->
                step_u net net' []
  (* duplicates a packet *)
  | SU_dup : forall net net' p xs ys,
                nwPackets net = xs ++ p :: ys ->
                net' = mkNetwork
                         (nwFailed net)
                         (p :: xs ++ p ::ys)
                         (nwState net) ->
                step_u net net' []
  (* a host fails (potentially again) *)
  | SU_fail :  forall h net net',
                 net' = mkNetwork
                          (h :: nwFailed net)
                          (nwPackets net)
                          (nwState net) ->
                 step_u net net' []
  (* a host reboots (is not failing anymore). the new state is computed with the reboot function from the old state *)
  | SU_reboot : forall h net net' d,
                  In h (nwFailed net) ->
                  reboot (nwState net h) = d ->
                  net' = mkNetwork
                           (remove name_eq_dec h (nwFailed net))
                           (nwPackets net)
                           (update (nwState net) h d) ->
                  step_u net net' []
  | SU_update : forall h net net' d,
                  ~ In h (nwFailed net) ->
                  upgrade_state (nwState net h) = d ->
                  net' = mkNetwork
                           (nwFailed net)
                           (nwPackets net)
                           (update (nwState net) h d) ->
                  step_u net net' [].

  Definition step_u_star : step_relation network (name * (input + list output))
    := refl_trans_1n_trace step_u.
  Definition step_u_init : network :=
    mkNetwork
      []
      []
      (fun n =>
         existT _ One (init_handlers n)).
End StepVerySimpleUpdate.

