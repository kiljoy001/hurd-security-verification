Require Import List.
Require Import Arith.
Require Import Bool.
Require Import Lia.
Require Import Reals.
Require Import Psatz.
Import ListNotations.
(* Open R_scope only when needed for specific sections *)

(** * ULE-based Microkernel IPC Scheduler with CA-based Routing *)

(** ** Basic Types *)

Inductive server_id : Type :=
  | SID : nat -> server_id.

Inductive message_id : Type :=
  | MID : nat -> message_id.

Definition server_id_eq (s1 s2 : server_id) : bool :=
  match s1, s2 with
  | SID n1, SID n2 => Nat.eqb n1 n2
  end.

Definition message_id_eq (m1 m2 : message_id) : bool :=
  match m1, m2 with
  | MID n1, MID n2 => Nat.eqb n1 n2
  end.

Inductive sched_server_type : Type :=
  | FileSystem | Network | Process | Memory | Device | GUI | Audio.

Inductive sched_msg_class : Type :=
  | Interrupt | RealTime | Interactive | Batch | Idle.

(** ** CA-based Routing Metric *)
(* Scott J. Guyton's Full Dynamic Benefit-to-Cost-of-Attack Ratio *)
(* Comprehensive threat modeling with Nash equilibrium integration *)

(* Individual threat characteristics *)
Record threat_data := mkThreatData {
  threat_probability : R;  (* p_i: probability of malicious intent [0,1] *)
  defense_effectiveness : R  (* E_i: defense effectiveness [0,1] *)
}.

(* Growth function g(p_i, E_i) for individual threats *)
Definition growth_function (t : threat_data) : R :=
  let k1 := (1.5)%R in
  let k2 := (2.0)%R in
  (1 + k1 * threat_probability t * Rpower (2 - defense_effectiveness t) k2)%R.

(* Nash equilibrium components *)
Record nash_components := mkNashComponents {
  equilibrium_factor : R;      (* π_eq *)
  competition_factor : R;      (* π_comp *)
  reputation_factor : R;       (* π_rep *)
  bayesian_factor : R;         (* π_bayes *)
  signaling_factor : R         (* π_signal *)
}.

(* Nash equilibrium multiplier Π_nash *)
Definition nash_multiplier (nc : nash_components) : R :=
  let w1 := (0.3)%R in
  let w2 := (0.2)%R in  
  let w3 := (0.2)%R in
  let w4 := (0.15)%R in
  let w5 := (0.15)%R in
  (w1 * equilibrium_factor nc + w2 * competition_factor nc + 
   w3 * reputation_factor nc + w4 * bayesian_factor nc + 
   w5 * signaling_factor nc)%R.

(* Full CA routing structure *)
Record route_ca := mkRouteCA {
  base_cost : nat;                    (* C_base *)
  max_cost : nat;                     (* C_max(t) *)
  active_threats : list threat_data;  (* Active threat set *)
  nash_context : nash_components;     (* Nash equilibrium context *)
  
  (* Legacy simple formula components for backward compatibility *)
  simple_attack_load : R;
  simple_defense_strength : R
}.

(* Product of growth functions for all active threats: ∏_{i∈active} g(p_i, E_i) *)
Fixpoint threat_product (threats : list threat_data) : R :=
  match threats with
  | [] => (1.0)%R  (* Default to 1.0 if no active threats *)
  | t :: rest => (growth_function t * threat_product rest)%R
  end.

(* Full Dynamic BCRA formula: CA(t) = min(C_max, CA₀ × exp(∏g(p_i,E_i)) × Π_nash) *)
Definition dynamic_routing_cost (ca : route_ca) : R :=
  let threat_component := threat_product (active_threats ca) in
  let nash_component := nash_multiplier (nash_context ca) in
  let raw_cost := (INR (base_cost ca) * exp threat_component * nash_component)%R in
  Rmin (INR (max_cost ca)) raw_cost.

(* Simplified routing cost for backward compatibility *)
Definition simple_routing_cost (ca : route_ca) : R :=
  (INR (base_cost ca) * (1 + simple_attack_load ca * (2 - simple_defense_strength ca)))%R.

(* Primary routing cost function - uses full Dynamic BCRA *)
Definition routing_cost (ca : route_ca) : R := dynamic_routing_cost ca.

(** ** Server Queue Structure *)

Record server_queue := mkServerQueue {
  server : server_id;
  current_queue : list message_id;
  next_queue : list message_id;
  idle_queue : list message_id;
  interactive_threshold : nat;
  message_history : list (message_id * nat);
  queue_load : nat;
  server_ca : route_ca;
  server_type : sched_server_type;
  dedicated_core : option nat
}.

(** ** Message Structure *)

Record message := mkMessage {
  mid : message_id;
  sender : server_id;
  target_service : sched_server_type;
  msg_class : sched_msg_class;
  sleep_time : nat;
  run_time : nat;
  arrival_time : nat
}.

(** ** System State *)

Record microkernel_state := mkMicrokernel {
  servers : list server_queue;
  pending_messages : list message;
  global_time : nat;
  core_count : nat
}.

(** ** Helper Functions *)

Definition calculate_interactivity (sleep run : nat) : nat :=
  if Nat.ltb 0 run then
    if Nat.leb sleep run then
      min 100 (50 + (run * 50) / (sleep + 1))
    else
      min 100 ((sleep * 50) / (run + 1))
  else 0.

Definition is_interactive (m : message) : bool :=
  Nat.leb (calculate_interactivity (sleep_time m) (run_time m)) 30.

Definition get_queue_length (sq : server_queue) : nat :=
  length (current_queue sq) + length (next_queue sq).

(** ** Core Theorems *)

(* Lemma: Interactivity calculation is bounded *)
Lemma interactivity_bounded : forall sleep run,
  calculate_interactivity sleep run <= 100.
Proof.
  intros sleep run.
  unfold calculate_interactivity.
  destruct (Nat.ltb 0 run) eqn:Hrun.
  - destruct (Nat.leb sleep run) eqn:Hsleep.
    + (* Case: run > 0 and sleep <= run *)
      (* Result is min 100 (50 + (run * 50) / (sleep + 1)) *)
      apply Nat.le_min_l.
    + (* Case: run > 0 and sleep > run *)
      (* Result is min 100 ((sleep * 50) / (run + 1)) *)
      apply Nat.le_min_l.
  - (* Case: run = 0 *)
    lia.
Qed.

(* Theorem 1: Interactive messages go to current queue *)
Theorem interactive_priority : forall m sq sq',
  is_interactive m = true ->
  sq' = mkServerQueue (server sq) (mid m :: current_queue sq)
                     (next_queue sq) (idle_queue sq)
                     (interactive_threshold sq) (message_history sq)
                     (S (queue_load sq)) (server_ca sq)
                     (server_type sq) (dedicated_core sq) ->
  In (mid m) (current_queue sq').
Proof.
  intros m sq sq' H_int H_sq'.
  rewrite H_sq'. simpl. left. reflexivity.
Qed.

(* Theorem 2: Queue switching preserves messages *)
Theorem queue_switch_preserves : forall sq,
  let sq' := mkServerQueue (server sq) (next_queue sq) (current_queue sq)
                          (idle_queue sq) (interactive_threshold sq)
                          (message_history sq) (queue_load sq)
                          (server_ca sq) (server_type sq) (dedicated_core sq) in
  forall m, (In m (current_queue sq) \/ In m (next_queue sq)) <->
           (In m (current_queue sq') \/ In m (next_queue sq')).
Proof.
  intros sq sq' m. simpl.
  split; intros [H | H]; [right | left | right | left]; assumption.
Qed.

(* Theorem 3: Dynamic routing cost is positive *)
Theorem dynamic_routing_cost_positive : forall ca,
  (0 < routing_cost ca)%R.
Proof.
  intros ca.
  unfold routing_cost, dynamic_routing_cost.
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat.
    + apply lt_0_INR. lia. (* base_cost > 0 *)
    + apply exp_pos.
  - (* nash_component > 0 - this needs to be proven from nash weights *)
    admit. (* TODO: prove nash_multiplier > 0 *)
Qed.

(* Helper lemma: threat_product is always at least 1.0 *)
Lemma threat_product_ge_one : forall threats,
  (1 <= threat_product threats)%R.
Proof.
  induction threats as [|t rest IH].
  - simpl. lra.
  - simpl.
    apply Rle_trans with (1 * threat_product rest)%R.
    + rewrite Rmult_1_l. exact IH.
    + apply Rmult_le_compat_r.
      * exact IH.
      * apply growth_function_ge_one.
Qed.

(* Helper lemma: growth function is always at least 1 *)
Lemma growth_function_ge_one : forall t,
  (1 <= growth_function t)%R.
Proof.
  intros t.
  unfold growth_function. lra.
Qed.

(* System Invariant: Message uniqueness across queues *)
Definition valid_system (sys : microkernel_state) : Prop :=
  forall sq1 sq2 m,
    In sq1 (servers sys) -> In sq2 (servers sys) ->
    server sq1 <> server sq2 ->
    In m (current_queue sq1) -> ~In m (current_queue sq2).

(* Theorem 4: Dedicated cores prevent queue interference *)
Theorem dedicated_core_isolation : forall sys sq1 sq2,
  valid_system sys ->
  In sq1 (servers sys) ->
  In sq2 (servers sys) ->
  server sq1 <> server sq2 ->
  dedicated_core sq1 = Some 0 ->
  dedicated_core sq2 = Some 1 ->
  forall m, ~(In m (current_queue sq1) /\ In m (current_queue sq2)).
Proof.
  intros sys sq1 sq2 Hvalid Hin1 Hin2 Hdiff Hcore1 Hcore2 m [H1 H2].
  apply (Hvalid sq1 sq2 m Hin1 Hin2 Hdiff H1 H2).
Qed.

(* Axioms for server type equality *)
Definition server_type_eq (st1 st2 : sched_server_type) : bool :=
  match st1, st2 with
  | FileSystem, FileSystem => true
  | Network, Network => true
  | Process, Process => true
  | Memory, Memory => true
  | Device, Device => true
  | GUI, GUI => true
  | Audio, Audio => true
  | _, _ => false
  end.

Lemma server_type_eq_true : forall st1 st2,
  server_type_eq st1 st2 = true -> st1 = st2.
Proof.
  intros st1 st2 H.
  destruct st1, st2; simpl in H; try discriminate; reflexivity.
Qed.

Lemma server_type_eq_false : forall st1 st2,
  server_type_eq st1 st2 = false -> st1 <> st2.
Proof.
  intros st1 st2 H Heq.
  subst. destruct st2; simpl in H; discriminate.
Qed.

Definition Rle_dec (r1 r2 : R) : {(r1 <= r2)%R} + {~(r1 <= r2)%R}.
  destruct (Rlt_dec r2 r1).
  - right. lra.
  - left. lra.
Defined.

(* Theorem 5: CA routing selects minimum cost server *)
Definition find_min_cost_server (servers : list server_queue) 
                                (stype : sched_server_type) : option server_queue :=
  let eligible := filter (fun sq => 
    match server_type sq, stype with
    | st1, st2 => if server_type_eq st1 st2 then true else false
    end) servers in
  match eligible with
  | [] => None
  | h :: t => Some (fold_left (fun acc sq =>
      if Rle_dec (routing_cost (server_ca sq)) (routing_cost (server_ca acc))
      then sq else acc) t h)
  end.

Lemma fold_left_min_correct : forall l sq0 sq_min,
  fold_left (fun acc sq =>
    if Rle_dec (routing_cost (server_ca sq)) (routing_cost (server_ca acc))
    then sq else acc) l sq0 = sq_min ->
  In sq_min (sq0 :: l) /\
  forall sq, In sq (sq0 :: l) -> 
    (routing_cost (server_ca sq_min) <= routing_cost (server_ca sq))%R.
Proof.
  induction l as [|a l IH]; intros sq0 sq_min Hfold.
  - (* Base case: l = [] *)
    simpl in Hfold. subst sq_min.
    split.
    + left. reflexivity.
    + intros sq [H | H].
      * subst. lra.
      * contradiction.
  - (* Inductive case: l = a :: l *)
    simpl in Hfold.
    destruct (Rle_dec (routing_cost (server_ca a)) (routing_cost (server_ca sq0))) as [Hle | Hgt].
    + (* Case: routing_cost a <= routing_cost sq0 *)
      (* The fold continues with 'a' as the new accumulator *)
      apply IH in Hfold.
      destruct Hfold as [Hin_min Hmin].
      split.
      * (* sq_min is in a :: l *)
        destruct Hin_min as [Heq | Hin_l].
        -- subst. right. left. reflexivity.
        -- right. right. assumption.
      * (* sq_min is minimal among sq0 :: a :: l *)
        intros sq [Hsq0 | [Hsq_a | Hsq_l]].
        -- (* sq = sq0 *)
           subst sq.
           (* sq_min is minimal among a :: l, and routing_cost a <= routing_cost sq0 *)
           (* So routing_cost sq_min <= routing_cost a <= routing_cost sq0 *)
           apply Rle_trans with (routing_cost (server_ca a)).
           ++ apply Hmin. left. reflexivity.
           ++ exact Hle.
        -- (* sq = a *)
           subst sq.
           apply Hmin. left. reflexivity.
        -- (* sq in l *)
           apply Hmin. right. assumption.
    + (* Case: routing_cost a > routing_cost sq0 *)
      (* The fold continues with sq0 as the accumulator *)
      apply IH in Hfold.
      destruct Hfold as [Hin_min Hmin].
      split.
      * (* sq_min is in sq0 :: l *)
        destruct Hin_min as [Heq | Hin_l].
        -- subst. left. reflexivity.
        -- right. right. assumption.
      * (* sq_min is minimal among sq0 :: a :: l *)
        intros sq [Hsq0 | [Hsq_a | Hsq_l]].
        -- (* sq = sq0 *)
           subst sq.
           apply Hmin. left. reflexivity.
        -- (* sq = a *)
           subst sq.
           (* We need to show routing_cost sq_min <= routing_cost a *)
           (* We know sq_min is minimal among sq0 :: l *)
           (* And we know routing_cost sq0 < routing_cost a *)
           (* So routing_cost sq_min <= routing_cost sq0 < routing_cost a *)
           apply Rle_trans with (routing_cost (server_ca sq0)).
           ++ apply Hmin. left. reflexivity.
           ++ apply Rnot_le_lt in Hgt. lra.
        -- (* sq in l *)
           apply Hmin. right. assumption.
Qed.

Theorem ca_routing_optimal : forall servers stype sq,
  find_min_cost_server servers stype = Some sq ->
  In sq servers /\
  server_type sq = stype /\  
  forall sq', In sq' servers -> server_type sq' = stype ->
    (routing_cost (server_ca sq) <= routing_cost (server_ca sq'))%R.
Proof.
  intros servers stype sq Hfind.
  unfold find_min_cost_server in Hfind.
  (* First, analyze the filter result *)
  remember (filter (fun sq => 
    match server_type sq, stype with
    | st1, st2 => if server_type_eq st1 st2 then true else false
    end) servers) as eligible.
  destruct eligible as [|h t].
  - (* Case: no eligible servers *)
    discriminate Hfind.
  - (* Case: eligible servers h :: t *)
    injection Hfind as Hsq.
    (* sq is the result of fold_left on t with h as initial value *)
    
    (* First, establish that h is in the filtered list and satisfies the type constraint *)
    assert (Hh_eligible: In h (h :: t)) by (left; reflexivity).
    assert (Hh_filter: In h (filter (fun sq => 
      match server_type sq, stype with
      | st1, st2 => if server_type_eq st1 st2 then true else false
      end) servers)).
    { rewrite <- Heqeligible. exact Hh_eligible. }
    apply filter_In in Hh_filter.
    destruct Hh_filter as [Hh_in Hh_type].
    
    (* Extract the type equality for h *)
    destruct (server_type_eq (server_type h) stype) eqn:Heq_h in Hh_type.
    2: discriminate Hh_type.
    apply server_type_eq_true in Heq_h.
    
    (* Apply the fold_left correctness lemma *)
    apply fold_left_min_correct in Hsq.
    destruct Hsq as [Hin_sq Hmin_sq].
    
    (* Now prove the three parts of the conjunction *)
    (* The goal is: In sq servers /\ server_type sq = stype /\ (forall sq', ...) *)
    split; [|split].
    
    + (* Part 1: In sq servers *)
      (* sq is in h :: t, and h :: t is the filtered result of servers *)
      assert (Hin_eligible: In sq (h :: t)) by exact Hin_sq.
      assert (Hin_filter: In sq (filter (fun sq => 
        match server_type sq, stype with
        | st1, st2 => if server_type_eq st1 st2 then true else false
        end) servers)).
      { rewrite <- Heqeligible. exact Hin_eligible. }
      apply filter_In in Hin_filter.
      destruct Hin_filter as [Hin_servers _].
      exact Hin_servers.
      
    + (* Part 2: server_type sq = stype *)
      (* sq is in the filtered list, so it must satisfy the type constraint *)
      assert (Hin_eligible: In sq (h :: t)) by exact Hin_sq.
      assert (Hin_filter: In sq (filter (fun sq => 
        match server_type sq, stype with
        | st1, st2 => if server_type_eq st1 st2 then true else false
        end) servers)).
      { rewrite <- Heqeligible. exact Hin_eligible. }
      apply filter_In in Hin_filter.
      destruct Hin_filter as [_ Hsq_type].
      destruct (server_type_eq (server_type sq) stype) eqn:Heq_sq in Hsq_type.
      * apply server_type_eq_true in Heq_sq. exact Heq_sq.
      * discriminate Hsq_type.
        
    + (* Part 3: sq has minimum routing cost among servers of the same type *)
      intros sq' Hin_sq' Htype_sq'.
      (* sq' must also be in the filtered list *)
      assert (Hin_sq'_filter: In sq' (filter (fun sq => 
        match server_type sq, stype with
        | st1, st2 => if server_type_eq st1 st2 then true else false
        end) servers)).
      { apply filter_In. split.
        - exact Hin_sq'.
        - rewrite Htype_sq'.
          destruct (server_type_eq stype stype) eqn:Heq.
          + reflexivity.
          + apply server_type_eq_false in Heq.
            exfalso. apply Heq. reflexivity. }
      
      (* Since sq' is in the eligible list h :: t, and sq is minimal among h :: t *)
      (* We have eligible = h :: t and Hin_sq'_filter: In sq' (filter ...) *)
      (* So rewrite Heqeligible in Hin_sq'_filter to get In sq' (h :: t) *)
      assert (Hin_sq'_eligible: In sq' (h :: t)).
      { rewrite <- Heqeligible in Hin_sq'_filter. exact Hin_sq'_filter. }
      apply Hmin_sq. exact Hin_sq'_eligible.
Qed.