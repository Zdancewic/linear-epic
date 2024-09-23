From Epic Require Export Syntax.
From Epic Require Import FinUtil.
From Coq Require Import Lia.

Import ScopedNotations.

Definition r_ctxt n := fin n -> nat.
Definition e_ctxt m := fin m -> nat.

Definition tail {n} (c : fin (S n) -> nat) : fin n -> nat :=
  fun x => c (Some x : fin (S n)).

Definition sum {n} (c : fin n -> nat) (d : fin n -> nat) : fin n -> nat :=
  fun x => (c x) + (d x).

Definition zero {n} (x:fin n) : nat := 0.

Definition one {n} (x:fin n) : fin n -> nat :=
  fun (y : fin n) =>
    if fin_eqb x y then 1 else 0.

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

Infix "⊎" := ctxt_app (at level 50).

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
      (WFes : wf_e_scope (n' + n) m Γ (Δ' ⊎ Δ) es),
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
      (GS : (Γ' ⊎ Γ) = SUM (List.map fst GDs))
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



