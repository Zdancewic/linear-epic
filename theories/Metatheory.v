From Coq Require Import Lia List FunctionalExtensionality.
From Epic Require Export Syntax.
From Epic Require Import FinUtil.


Import ScopedNotations.
Import ListNotations.


Definition r_ctxt n := fin n -> nat.
Definition e_ctxt m := fin m -> nat.

Definition tail {n} (c : fin (S n) -> nat) : fin n -> nat :=
  fun x => c (Some x : fin (S n)).

Definition sum {n} (c : fin n -> nat) (d : fin n -> nat) : fin n -> nat :=
  fun x => (c x) + (d x).

Definition zero {n} (x:fin n) : nat := 0.

Lemma sum_zero_l : forall {n} (c : fin n -> nat),
    sum c zero = c.
Proof.
  intros. apply functional_extensionality.
  intros. unfold sum. unfold zero. lia.
Qed.

Lemma sum_zero_r : forall {n} (c : fin n -> nat),
    sum zero c = c.
Proof.
  intros. apply functional_extensionality.
  intros. unfold sum. unfold zero. reflexivity.
Qed.

Definition delta {n} (x:fin n) (c:nat) : fin n -> nat :=
  fun (y : fin n) =>
    if fin_eqb x y then c else 0.

Lemma delta_eq : forall n c (i1 i2 : fin n),
    c <> 0 ->
    delta i1 c i2 = c <-> i1 = i2.
Proof.
  intros.
  unfold delta.
  destruct (fin_eqb i1 i2) eqn:EQ.
  rewrite fin_eqb_eq in EQ.
  subst. tauto.
  rewrite fin_eqb_neq in EQ.
  split. intros; subst. contradiction. intros; contradiction.
Qed.

Lemma delta_neq : forall n c (i1 i2 : fin n),
    delta i1 c i2 = 0  <-> (c = 0 \/ i1 <> i2).
Proof.
    intros. split; intros.
    - destruct c. left; auto.
      right. intros Heq. eapply delta_eq with (c:=S c) in Heq.
      rewrite  H in Heq. discriminate.
      intros C.  discriminate.
    - destruct H.
      + unfold delta. destruct (fin_eqb i1 i2) eqn: He; auto.
      + unfold delta. destruct (fin_eqb i1 i2) eqn: He; auto. rewrite fin_eqb_eq in He.        contradiction.
Qed.

Definition one {n} (r : fin n) : fin n -> nat := delta r 1.
  
  Definition SUM {n} (l : list (fin n -> nat)) : fin n -> nat :=
  List.fold_right sum zero l.

(*
Definition ctxt_app {n m : nat} (c : fin n -> nat) (d : fin m -> nat) :  fin (plus n m) -> nat.
  induction n.
  - exact d.
  - apply scons.
    simpl in c.
    apply c.
    exact None.
    intros H.
    apply IHn.
    exact (tail c).
    exact H.
Defined.
Print ctxt_app.
*)
(* TODO: look up how to do it this way *)
(*
Fixpoint ctxt_app' {n m : nat} (c : fin n -> nat) (d : fin m -> nat) :  fin (plus n m) -> nat :=
  match n with
  | 0 => d
  | S n => scons (c None) (ctxt_app' _ _ (tail c) d)
  end.
 *)

Definition ctxt_app {n m : nat} (c : fin n -> nat) (d : fin m -> nat) :  fin (plus n m) -> nat := scons_p n c d.

Infix "⊗" := ctxt_app (at level 50).

Definition coerce {X} {n m} (c : fin (n + S m) -> X) : fin (S (n + m)) -> X.
  replace (n + S m) with (S (n + m)) in c by lia.
  exact c.
Defined.

Definition sigma_lift {n} : fin 0 -> res n :=
  fun x => match x with end.

Definition lift_tm (n m :nat) (t : tm 0 m) : tm n m :=
  subst_tm sigma_lift var_exp t.

Inductive wf_tm : forall (n m : nat), e_ctxt m -> tm n m -> Prop :=
  wf_lam :
    forall (m : nat)
      (Γ : e_ctxt m)
      (HΓ : forall (e : fin m), Γ e = 0)      
      (rs : r_scope 1 m),
      wf_r_scope (S 0) m Γ (1 .: null) rs ->
      wf_tm 0 m Γ (lam rs)

with wf_r_scope : forall (n m : nat), e_ctxt m -> r_ctxt n -> r_scope n m -> Prop :=
  wf_rs :
    forall n m n'
      (Γ : e_ctxt m)
      (HΓ : forall (e : fin m), Γ e = 0)
      (Δ : r_ctxt n)
      (HΔ : forall (r : fin n), Δ r = 1)
      (Δ' : r_ctxt n')
      (HΔ' : forall (r' : fin n'), Δ' r' = 2)
      (es : e_scope (n' + n) m)
      (WFes : wf_e_scope (n' + n) m Γ (Δ' ⊗ Δ) es),
      wf_r_scope n m Γ Δ (rbnd n' es)

with wf_e_scope : forall (n m : nat), e_ctxt m -> r_ctxt n -> e_scope n m -> Prop :=
  wf_es :
    forall n m m'
      (Γ : e_ctxt m)
      (HΓ : forall (e : fin m), Γ e = 0)
      (Δ : r_ctxt n)
      (Γ' : e_ctxt m')
      (HΓ' : forall (e' : fin m'), Γ' e' = 1)      
      (stmts : list (stmt n (m' + m)))
      (GDs : list (e_ctxt (m' + m) * r_ctxt n))
      (GS : (Γ' ⊗ Γ) = SUM (List.map fst GDs))
      (DS : Δ = SUM (List.map snd GDs))
      (WFstmts : List.Forall2
                   (fun s gd => wf_stmt n (m' + m) (fst gd) (snd gd) s) stmts GDs),
        wf_e_scope n m Γ Δ (ebnd m' stmts)

with wf_stmt : forall (n m : nat), e_ctxt m -> r_ctxt n -> stmt n m -> Prop :=
| wf_cut :
    forall n m
      (r1 r2 : fin n)
      (Γ : e_ctxt m)
      (HΓ : forall (e : fin m), Γ e = 0)
      (Δ : r_ctxt n)
      (HΔ : Δ = sum (one r1) (one r2)),
      wf_stmt n m Γ Δ (cut (var_res r1) (var_res r2))

| wf_tup :
    forall n m
      (r : fin n)
      (rs : list (fin n))
      (Γ : e_ctxt m)
      (HΓ : forall (e : fin m), Γ e = 0)
      (Δ : r_ctxt n)
      (HΔ : Δ = sum (one r) (SUM (List.map one rs))),
      wf_stmt n m Γ Δ (tup (var_res r) (List.map var_res rs))
              
| wf_def :
    forall n m
      (r : fin n)
      (t : tm 0 m)
      (Γ : e_ctxt m)
      (HΓ : forall (e : fin m), Γ e = 0)
      (Δ : r_ctxt n)
      (HΔ : Δ = (one r))
      (Ht : wf_tm 0 m Γ t),
      wf_stmt n m Γ Δ (def (var_res r) (lift_tm n m t))

| wf_nam :
    forall n m
      (r : fin n)
      (e : fin m)
      (Γ : e_ctxt m)
      (HΓ : Γ = (one e))
      (Δ : r_ctxt n)
      (HΔ : Δ = (one r)),
      wf_stmt n m Γ Δ (nam (var_res r) (var_exp e))

| wf_app :               
    forall n m
      (r : fin n)
      (e : fin m)
      (Γ : e_ctxt m)
      (HΓ : forall (e : fin m), Γ e = 0)
      (Δ : r_ctxt n)
      (HΔ : Δ = (one r)),
      wf_stmt n m Γ Δ (app (var_exp e) (var_res r)).

(*
[λr0.
  r0 = (r1, r1)]

*)

Example tm_id : tm 0 0 :=
  lam (rbnd 1 (ebnd 0
                 ([tup (var_res (var_zero))
                     (List.map var_res ([shift (var_zero); shift (var_zero)])%list)]%list))).

(*
Lemma wf_tm_id : wf_tm 0 0 null tm_id.
Proof.
  econstructor.
  - intros; auto. inversion e.
  - eapply wf_rs with (Δ' := 2 .: null).
    intros. inversion e.
    auto_case. inversion f.
    auto_case. inversion f.
    eapply wf_es with (Γ' := zero).
    intros. inversion e.
    intros. inversion e'.
    3 : { eapply Forall2_cons with (y := (null, _)).
          eapply wf_tup with (Γ := null).
          intros. inversion e.
          simpl.  reflexivity.
          eapply Forall2_nil. }
    simpl. unfold ctxt_app. fsimpl. unfold sum.
    apply functional_extensionality. intros. inversion x.
    simpl. 
    unfold ctxt_app.
    fsimpl.
    repeat rewrite sum_zero_l.
    apply functional_extensionality. intros.
    unfold one.
    destruct (fin_eqb var_zero x) eqn:Hx.
    rewrite fin_eqb_eq in Hx.
    subst. fsimpl. 
*)          
          
                
    




(* A "scope" picks out a list of statements from within a term *)
Inductive scope (n m : nat) :=
| here (n' m' : nat)   (* lam n' m'. [] *)
| deeper (n' m' : nat) (i:nat) (rest : scope (n' + S n) (m' + m)).


Inductive lookup_stmts : forall (n : nat) (m:nat) n' m' , tm n m -> scope n m -> list (stmt n' m') -> Prop :=
| lookup_here : forall n m n' m' body,
    lookup_stmts n m (n' + S n) (m' + m) (lam (rbnd n' (ebnd m' body))) (here n m n' m') body

| lookup_deeper : forall n m n' m' n'' m'' i (rest : scope _ _ ) body body1 r t body2,
    length body1 = i ->
    lookup_stmts (n' + S n) (m' + m) n'' m'' t rest body ->
    
    lookup_stmts n m n'' m''
      (lam (rbnd n' (ebnd m' (body1 ++ [def r t] ++ body2)))) (deeper _ _ n' m' i rest) body.


(*

Inductive tm_redex (n m : nat) :=
| lam_r (n' m' : nat) (s : body_redex (n' + S n) (m' + m))
with body_redex (n m : nat) :=
| cut_r (i:nat) (r1 r2 : fin n)
| tup_r (i j:nat) (H:i<>j) (r1 : fin n) (rs rs' : list (fin n))
| app_local_r (i j k :nat) (H1:i<>j) (H2:j<>k) (H3:i<>k) (re : fin n) (t: tm n m) (e : fin m) (r : fin n)
| app_deep_r (i j k : nat) 

Scheme mut_tm_path := Induction for tm_path Sort Prop
with mut_stmts_path := Induction for stmts_path Sort Prop.
*)



(*
Inductive tm (n_res n_exp : nat) : Type :=
    lam : r_scope (S n_res) n_exp -> tm n_res n_exp
with stmt (n_res n_exp : nat) : Type :=
  | cut : res n_res -> res n_res -> stmt n_res n_exp
  | tup : res n_res -> list (res n_res) -> stmt n_res n_exp
  | def : res n_res -> tm n_res n_exp -> stmt n_res n_exp
  | nam : res n_res -> exp n_exp -> stmt n_res n_exp
  | app : exp n_exp -> res n_res -> stmt n_res n_exp
with r_scope (n_res n_exp : nat) : Type :=
    rbnd :
      forall n : nat, e_scope (plus n n_res) n_exp -> r_scope n_res n_exp
with e_scope (n_res n_exp : nat) : Type :=
    ebnd :
      forall m : nat, list (stmt n_res (plus m n_exp)) -> e_scope n_res n_exp.
*)



