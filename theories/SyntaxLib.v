From Epic Require Import Syntax.

Section Induction.

(*
Scheme ind_tm := Induction for tm Sort Prop
with ind_stmt := Induction for stmt Sort Prop
with ind_r_scope := Induction for r_scope Sort Prop
with ind_e_scope := Induction for e_scope Sort Prop.                                               

Print ind_tm.
 *)

Context 
 (P : forall n_res n_exp : nat, tm n_res n_exp -> Prop)
  (P0 : forall n_res n_exp : nat, stmt n_res n_exp -> Prop)
  (P1 : forall n_res n_exp : nat, r_scope n_res n_exp -> Prop)
  (P2 : forall n_res n_exp : nat, e_scope n_res n_exp -> Prop)
  (f : forall (n_res n_exp : nat) (r : r_scope (S n_res) n_exp),
       P1 (S n_res) n_exp r -> P n_res n_exp (lam r))
  (f0 : forall (n_res n_exp : nat) (r r0 : res n_res), P0 n_res n_exp (cut r r0))
  (f1 : forall (n_res n_exp : nat) (r : res n_res) (l : list (res n_res)),
      P0 n_res n_exp (tup r l))
  (f2 : forall (n_res n_exp : nat) (r : res n_res) (t : tm n_res n_exp),
        P n_res n_exp t -> P0 n_res n_exp (def r t))
  (f3 : forall (n_res n_exp : nat) (r : res n_res) (e : exp n_exp), P0 n_res n_exp (nam r e))
  (f4 : forall (n_res n_exp : nat) (e : exp n_exp) (r : res n_res), P0 n_res n_exp (app e r))
  (f5 : forall (n_res n_exp n : nat) (e : e_scope (n + n_res) n_exp),
        P2 (n + n_res) n_exp e -> P1 n_res n_exp (rbnd n e))
  (f6 : forall (n_res n_exp m : nat) (l : list (stmt n_res (m + n_exp)))
      (HL : List.Forall (P0 n_res (m + n_exp)) l),
      P2 n_res n_exp (ebnd m l)).

Fixpoint F (n_res n_exp : nat) (t : tm n_res n_exp) {struct t} : P n_res n_exp t :=
  match t as t0 return (P n_res n_exp t0) with
  | lam r => f n_res n_exp r (F1 (S n_res) n_exp r)
  end
with F0 (n_res n_exp : nat) (s : stmt n_res n_exp) {struct s} : P0 n_res n_exp s :=
  match s as s0 return (P0 n_res n_exp s0) with
  | cut r r0 => f0 n_res n_exp r r0
  | tup r l => f1 n_res n_exp r l
  | def r t => f2 n_res n_exp r t (F n_res n_exp t)
  | nam r e => f3 n_res n_exp r e
  | app e r => f4 n_res n_exp e r
  end
with F1 (n_res n_exp : nat) (r : r_scope n_res n_exp) {struct r} : P1 n_res n_exp r :=
  match r as r0 return (P1 n_res n_exp r0) with
  | rbnd n e => f5 n_res n_exp n e (F2 (n + n_res) n_exp e)
  end
with F2 (n_res n_exp : nat) (e : e_scope n_res n_exp) {struct e} : P2 n_res n_exp e :=
       let fix rec_list m (l : list (stmt n_res (m + n_exp))) : List.Forall (P0 n_res (m + n_exp)) l :=
         match l with
         | nil => List.Forall_nil _
         | cons s ss => @List.Forall_cons _ (P0 n_res (m + n_exp)) s ss (F0 n_res (m + n_exp) s) (rec_list m ss)
         end
       in     
       match e as e0 return (P2 n_res n_exp e0) with
       | ebnd m l => f6 n_res n_exp m l (rec_list m l)
       end.

Lemma mut_ind : forall (n_res n_exp : nat)
                  (t : tm n_res n_exp)
                  (s : stmt n_res n_exp)
                  (rs : r_scope n_res n_exp)
                  (es : e_scope n_res n_exp),
    (P n_res n_exp t) /\
     (P0 n_res n_exp s) /\
      (P1 n_res n_exp rs) /\
      (P2 n_res n_exp es).
Proof.
  intros.
  repeat split.
  - apply F; auto.
  - apply F0; auto.
  - apply F1; auto.
  - apply F2; auto.
Qed.    

End Induction.

