Require Import Epic.core Epic.fintype.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive res (n_res : nat) : Type :=
    var_res : fin n_res -> res n_res.

Definition subst_res {m_res : nat} {n_res : nat}
  (sigma_res : fin m_res -> res n_res) (s : res m_res) : res n_res :=
  match s with
  | var_res _ s0 => sigma_res s0
  end.

Lemma up_res_res {m : nat} {n_res : nat} (sigma : fin m -> res n_res) :
  fin (S m) -> res (S n_res).
Proof.
exact (scons (var_res (S n_res) var_zero)
         (funcomp (subst_res (funcomp (var_res _) shift)) sigma)).
Defined.

Lemma up_list_res_res (p : nat) {m : nat} {n_res : nat}
  (sigma : fin m -> res n_res) : fin (plus p m) -> res (plus p n_res).
Proof.
exact (scons_p p (funcomp (var_res (plus p n_res)) (zero_p p))
         (funcomp (subst_res (funcomp (var_res _) (shift_p p))) sigma)).
Defined.

Lemma upId_res_res {m_res : nat} (sigma : fin m_res -> res m_res)
  (Eq : forall x, sigma x = var_res m_res x) :
  forall x, up_res_res sigma x = var_res (S m_res) x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (subst_res (funcomp (var_res _) shift)) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upId_list_res_res {p : nat} {m_res : nat}
  (sigma : fin m_res -> res m_res) (Eq : forall x, sigma x = var_res m_res x)
  : forall x, up_list_res_res p sigma x = var_res (plus p m_res) x.
Proof.
exact (fun n =>
       scons_p_eta (var_res (plus p m_res))
         (fun n => ap (subst_res (funcomp (var_res _) (shift_p p))) (Eq n))
         (fun n => eq_refl)).
Qed.

Definition idSubst_res {m_res : nat} (sigma_res : fin m_res -> res m_res)
  (Eq_res : forall x, sigma_res x = var_res m_res x) (s : res m_res) :
  subst_res sigma_res s = s := match s with
                               | var_res _ s0 => Eq_res s0
                               end.

Lemma upExt_res_res {m : nat} {n_res : nat} (sigma : fin m -> res n_res)
  (tau : fin m -> res n_res) (Eq : forall x, sigma x = tau x) :
  forall x, up_res_res sigma x = up_res_res tau x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (subst_res (funcomp (var_res _) shift)) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExt_list_res_res {p : nat} {m : nat} {n_res : nat}
  (sigma : fin m -> res n_res) (tau : fin m -> res n_res)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_res_res p sigma x = up_list_res_res p tau x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl)
         (fun n => ap (subst_res (funcomp (var_res _) (shift_p p))) (Eq n))).
Qed.

Definition ext_res {m_res : nat} {n_res : nat}
  (sigma_res : fin m_res -> res n_res) (tau_res : fin m_res -> res n_res)
  (Eq_res : forall x, sigma_res x = tau_res x) (s : res m_res) :
  subst_res sigma_res s = subst_res tau_res s :=
  match s with
  | var_res _ s0 => Eq_res s0
  end.

Definition compSubstSubst_res {k_res : nat} {l_res : nat} {m_res : nat}
  (sigma_res : fin m_res -> res k_res) (tau_res : fin k_res -> res l_res)
  (theta_res : fin m_res -> res l_res)
  (Eq_res : forall x, funcomp (subst_res tau_res) sigma_res x = theta_res x)
  (s : res m_res) :
  subst_res tau_res (subst_res sigma_res s) = subst_res theta_res s :=
  match s with
  | var_res _ s0 => Eq_res s0
  end.

Lemma up_subst_subst_res_res {k : nat} {l_res : nat} {m_res : nat}
  (sigma : fin k -> res l_res) (tau_res : fin l_res -> res m_res)
  (theta : fin k -> res m_res)
  (Eq : forall x, funcomp (subst_res tau_res) sigma x = theta x) :
  forall x,
  funcomp (subst_res (up_res_res tau_res)) (up_res_res sigma) x =
  up_res_res theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compSubstSubst_res (funcomp (var_res _) shift)
                (up_res_res tau_res) (funcomp (up_res_res tau_res) shift)
                (fun x => eq_refl) (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compSubstSubst_res tau_res (funcomp (var_res _) shift)
                      (funcomp (subst_res (funcomp (var_res _) shift))
                         tau_res) (fun x => eq_refl) (sigma fin_n)))
                (ap (subst_res (funcomp (var_res _) shift)) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_subst_list_res_res {p : nat} {k : nat} {l_res : nat}
  {m_res : nat} (sigma : fin k -> res l_res)
  (tau_res : fin l_res -> res m_res) (theta : fin k -> res m_res)
  (Eq : forall x, funcomp (subst_res tau_res) sigma x = theta x) :
  forall x,
  funcomp (subst_res (up_list_res_res p tau_res)) (up_list_res_res p sigma) x =
  up_list_res_res p theta x.
Proof.
exact (fun n =>
       eq_trans
         (scons_p_comp' (funcomp (var_res (plus p l_res)) (zero_p p)) _ _ n)
         (scons_p_congr
            (fun x =>
             scons_p_head' _
               (fun z => subst_res (funcomp (var_res _) (shift_p p)) _) x)
            (fun n =>
             eq_trans
               (compSubstSubst_res (funcomp (var_res _) (shift_p p))
                  (up_list_res_res p tau_res)
                  (funcomp (up_list_res_res p tau_res) (shift_p p))
                  (fun x => eq_refl) (sigma n))
               (eq_trans
                  (eq_sym
                     (compSubstSubst_res tau_res
                        (funcomp (var_res _) (shift_p p)) _
                        (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
                  (ap (subst_res (funcomp (var_res _) (shift_p p))) (Eq n)))))).
Qed.

Lemma substSubst_res {k_res : nat} {l_res : nat} {m_res : nat}
  (sigma_res : fin m_res -> res k_res) (tau_res : fin k_res -> res l_res)
  (s : res m_res) :
  subst_res tau_res (subst_res sigma_res s) =
  subst_res (funcomp (subst_res tau_res) sigma_res) s.
Proof.
exact (compSubstSubst_res sigma_res tau_res _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_res_pointwise {k_res : nat} {l_res : nat} {m_res : nat}
  (sigma_res : fin m_res -> res k_res) (tau_res : fin k_res -> res l_res) :
  pointwise_relation _ eq (funcomp (subst_res tau_res) (subst_res sigma_res))
    (subst_res (funcomp (subst_res tau_res) sigma_res)).
Proof.
exact (fun s => compSubstSubst_res sigma_res tau_res _ (fun n => eq_refl) s).
Qed.

Lemma instId'_res {m_res : nat} (s : res m_res) :
  subst_res (var_res m_res) s = s.
Proof.
exact (idSubst_res (var_res m_res) (fun n => eq_refl) s).
Qed.

Lemma instId'_res_pointwise {m_res : nat} :
  pointwise_relation _ eq (subst_res (var_res m_res)) id.
Proof.
exact (fun s => idSubst_res (var_res m_res) (fun n => eq_refl) s).
Qed.

Lemma varL'_res {m_res : nat} {n_res : nat}
  (sigma_res : fin m_res -> res n_res) (x : fin m_res) :
  subst_res sigma_res (var_res m_res x) = sigma_res x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_res_pointwise {m_res : nat} {n_res : nat}
  (sigma_res : fin m_res -> res n_res) :
  pointwise_relation _ eq (funcomp (subst_res sigma_res) (var_res m_res))
    sigma_res.
Proof.
exact (fun x => eq_refl).
Qed.

Inductive exp (n_exp : nat) : Type :=
    var_exp : fin n_exp -> exp n_exp.

Definition subst_exp {m_exp : nat} {n_exp : nat}
  (sigma_exp : fin m_exp -> exp n_exp) (s : exp m_exp) : exp n_exp :=
  match s with
  | var_exp _ s0 => sigma_exp s0
  end.

Lemma up_exp_exp {m : nat} {n_exp : nat} (sigma : fin m -> exp n_exp) :
  fin (S m) -> exp (S n_exp).
Proof.
exact (scons (var_exp (S n_exp) var_zero)
         (funcomp (subst_exp (funcomp (var_exp _) shift)) sigma)).
Defined.

Lemma up_list_exp_exp (p : nat) {m : nat} {n_exp : nat}
  (sigma : fin m -> exp n_exp) : fin (plus p m) -> exp (plus p n_exp).
Proof.
exact (scons_p p (funcomp (var_exp (plus p n_exp)) (zero_p p))
         (funcomp (subst_exp (funcomp (var_exp _) (shift_p p))) sigma)).
Defined.

Lemma upId_exp_exp {m_exp : nat} (sigma : fin m_exp -> exp m_exp)
  (Eq : forall x, sigma x = var_exp m_exp x) :
  forall x, up_exp_exp sigma x = var_exp (S m_exp) x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (subst_exp (funcomp (var_exp _) shift)) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upId_list_exp_exp {p : nat} {m_exp : nat}
  (sigma : fin m_exp -> exp m_exp) (Eq : forall x, sigma x = var_exp m_exp x)
  : forall x, up_list_exp_exp p sigma x = var_exp (plus p m_exp) x.
Proof.
exact (fun n =>
       scons_p_eta (var_exp (plus p m_exp))
         (fun n => ap (subst_exp (funcomp (var_exp _) (shift_p p))) (Eq n))
         (fun n => eq_refl)).
Qed.

Definition idSubst_exp {m_exp : nat} (sigma_exp : fin m_exp -> exp m_exp)
  (Eq_exp : forall x, sigma_exp x = var_exp m_exp x) (s : exp m_exp) :
  subst_exp sigma_exp s = s := match s with
                               | var_exp _ s0 => Eq_exp s0
                               end.

Lemma upExt_exp_exp {m : nat} {n_exp : nat} (sigma : fin m -> exp n_exp)
  (tau : fin m -> exp n_exp) (Eq : forall x, sigma x = tau x) :
  forall x, up_exp_exp sigma x = up_exp_exp tau x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (subst_exp (funcomp (var_exp _) shift)) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExt_list_exp_exp {p : nat} {m : nat} {n_exp : nat}
  (sigma : fin m -> exp n_exp) (tau : fin m -> exp n_exp)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_exp_exp p sigma x = up_list_exp_exp p tau x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl)
         (fun n => ap (subst_exp (funcomp (var_exp _) (shift_p p))) (Eq n))).
Qed.

Definition ext_exp {m_exp : nat} {n_exp : nat}
  (sigma_exp : fin m_exp -> exp n_exp) (tau_exp : fin m_exp -> exp n_exp)
  (Eq_exp : forall x, sigma_exp x = tau_exp x) (s : exp m_exp) :
  subst_exp sigma_exp s = subst_exp tau_exp s :=
  match s with
  | var_exp _ s0 => Eq_exp s0
  end.

Definition compSubstSubst_exp {k_exp : nat} {l_exp : nat} {m_exp : nat}
  (sigma_exp : fin m_exp -> exp k_exp) (tau_exp : fin k_exp -> exp l_exp)
  (theta_exp : fin m_exp -> exp l_exp)
  (Eq_exp : forall x, funcomp (subst_exp tau_exp) sigma_exp x = theta_exp x)
  (s : exp m_exp) :
  subst_exp tau_exp (subst_exp sigma_exp s) = subst_exp theta_exp s :=
  match s with
  | var_exp _ s0 => Eq_exp s0
  end.

Lemma up_subst_subst_exp_exp {k : nat} {l_exp : nat} {m_exp : nat}
  (sigma : fin k -> exp l_exp) (tau_exp : fin l_exp -> exp m_exp)
  (theta : fin k -> exp m_exp)
  (Eq : forall x, funcomp (subst_exp tau_exp) sigma x = theta x) :
  forall x,
  funcomp (subst_exp (up_exp_exp tau_exp)) (up_exp_exp sigma) x =
  up_exp_exp theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compSubstSubst_exp (funcomp (var_exp _) shift)
                (up_exp_exp tau_exp) (funcomp (up_exp_exp tau_exp) shift)
                (fun x => eq_refl) (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compSubstSubst_exp tau_exp (funcomp (var_exp _) shift)
                      (funcomp (subst_exp (funcomp (var_exp _) shift))
                         tau_exp) (fun x => eq_refl) (sigma fin_n)))
                (ap (subst_exp (funcomp (var_exp _) shift)) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_subst_list_exp_exp {p : nat} {k : nat} {l_exp : nat}
  {m_exp : nat} (sigma : fin k -> exp l_exp)
  (tau_exp : fin l_exp -> exp m_exp) (theta : fin k -> exp m_exp)
  (Eq : forall x, funcomp (subst_exp tau_exp) sigma x = theta x) :
  forall x,
  funcomp (subst_exp (up_list_exp_exp p tau_exp)) (up_list_exp_exp p sigma) x =
  up_list_exp_exp p theta x.
Proof.
exact (fun n =>
       eq_trans
         (scons_p_comp' (funcomp (var_exp (plus p l_exp)) (zero_p p)) _ _ n)
         (scons_p_congr
            (fun x =>
             scons_p_head' _
               (fun z => subst_exp (funcomp (var_exp _) (shift_p p)) _) x)
            (fun n =>
             eq_trans
               (compSubstSubst_exp (funcomp (var_exp _) (shift_p p))
                  (up_list_exp_exp p tau_exp)
                  (funcomp (up_list_exp_exp p tau_exp) (shift_p p))
                  (fun x => eq_refl) (sigma n))
               (eq_trans
                  (eq_sym
                     (compSubstSubst_exp tau_exp
                        (funcomp (var_exp _) (shift_p p)) _
                        (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
                  (ap (subst_exp (funcomp (var_exp _) (shift_p p))) (Eq n)))))).
Qed.

Lemma substSubst_exp {k_exp : nat} {l_exp : nat} {m_exp : nat}
  (sigma_exp : fin m_exp -> exp k_exp) (tau_exp : fin k_exp -> exp l_exp)
  (s : exp m_exp) :
  subst_exp tau_exp (subst_exp sigma_exp s) =
  subst_exp (funcomp (subst_exp tau_exp) sigma_exp) s.
Proof.
exact (compSubstSubst_exp sigma_exp tau_exp _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_exp_pointwise {k_exp : nat} {l_exp : nat} {m_exp : nat}
  (sigma_exp : fin m_exp -> exp k_exp) (tau_exp : fin k_exp -> exp l_exp) :
  pointwise_relation _ eq (funcomp (subst_exp tau_exp) (subst_exp sigma_exp))
    (subst_exp (funcomp (subst_exp tau_exp) sigma_exp)).
Proof.
exact (fun s => compSubstSubst_exp sigma_exp tau_exp _ (fun n => eq_refl) s).
Qed.

Lemma instId'_exp {m_exp : nat} (s : exp m_exp) :
  subst_exp (var_exp m_exp) s = s.
Proof.
exact (idSubst_exp (var_exp m_exp) (fun n => eq_refl) s).
Qed.

Lemma instId'_exp_pointwise {m_exp : nat} :
  pointwise_relation _ eq (subst_exp (var_exp m_exp)) id.
Proof.
exact (fun s => idSubst_exp (var_exp m_exp) (fun n => eq_refl) s).
Qed.

Lemma varL'_exp {m_exp : nat} {n_exp : nat}
  (sigma_exp : fin m_exp -> exp n_exp) (x : fin m_exp) :
  subst_exp sigma_exp (var_exp m_exp x) = sigma_exp x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_exp_pointwise {m_exp : nat} {n_exp : nat}
  (sigma_exp : fin m_exp -> exp n_exp) :
  pointwise_relation _ eq (funcomp (subst_exp sigma_exp) (var_exp m_exp))
    sigma_exp.
Proof.
exact (fun x => eq_refl).
Qed.

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

Lemma congr_lam {m_res m_exp : nat} {s0 : r_scope (S m_res) m_exp}
  {t0 : r_scope (S m_res) m_exp} (H0 : s0 = t0) :
  lam m_res m_exp s0 = lam m_res m_exp t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => lam m_res m_exp x) H0)).
Qed.

Lemma congr_cut {m_res m_exp : nat} {s0 : res m_res} {s1 : res m_res}
  {t0 : res m_res} {t1 : res m_res} (H0 : s0 = t0) (H1 : s1 = t1) :
  cut m_res m_exp s0 s1 = cut m_res m_exp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => cut m_res m_exp x s1) H0))
         (ap (fun x => cut m_res m_exp t0 x) H1)).
Qed.

Lemma congr_tup {m_res m_exp : nat} {s0 : res m_res} {s1 : list (res m_res)}
  {t0 : res m_res} {t1 : list (res m_res)} (H0 : s0 = t0) (H1 : s1 = t1) :
  tup m_res m_exp s0 s1 = tup m_res m_exp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tup m_res m_exp x s1) H0))
         (ap (fun x => tup m_res m_exp t0 x) H1)).
Qed.

Lemma congr_def {m_res m_exp : nat} {s0 : res m_res} {s1 : tm m_res m_exp}
  {t0 : res m_res} {t1 : tm m_res m_exp} (H0 : s0 = t0) (H1 : s1 = t1) :
  def m_res m_exp s0 s1 = def m_res m_exp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => def m_res m_exp x s1) H0))
         (ap (fun x => def m_res m_exp t0 x) H1)).
Qed.

Lemma congr_nam {m_res m_exp : nat} {s0 : res m_res} {s1 : exp m_exp}
  {t0 : res m_res} {t1 : exp m_exp} (H0 : s0 = t0) (H1 : s1 = t1) :
  nam m_res m_exp s0 s1 = nam m_res m_exp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => nam m_res m_exp x s1) H0))
         (ap (fun x => nam m_res m_exp t0 x) H1)).
Qed.

Lemma congr_app {m_res m_exp : nat} {s0 : exp m_exp} {s1 : res m_res}
  {t0 : exp m_exp} {t1 : res m_res} (H0 : s0 = t0) (H1 : s1 = t1) :
  app m_res m_exp s0 s1 = app m_res m_exp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app m_res m_exp x s1) H0))
         (ap (fun x => app m_res m_exp t0 x) H1)).
Qed.

Lemma congr_rbnd {n : nat} {m_res m_exp : nat}
  {s0 : e_scope (plus n m_res) m_exp} {t0 : e_scope (plus n m_res) m_exp}
  (H0 : s0 = t0) : rbnd m_res m_exp n s0 = rbnd m_res m_exp n t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => rbnd m_res m_exp n x) H0)).
Qed.

Lemma congr_ebnd {m : nat} {m_res m_exp : nat}
  {s0 : list (stmt m_res (plus m m_exp))}
  {t0 : list (stmt m_res (plus m m_exp))} (H0 : s0 = t0) :
  ebnd m_res m_exp m s0 = ebnd m_res m_exp m t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => ebnd m_res m_exp m x) H0)).
Qed.

Lemma up_res_exp {m : nat} {n_exp : nat} (sigma : fin m -> exp n_exp) :
  fin m -> exp n_exp.
Proof.
exact (sigma).
Defined.

Lemma up_exp_res {m : nat} {n_res : nat} (sigma : fin m -> res n_res) :
  fin m -> res n_res.
Proof.
exact (sigma).
Defined.

Lemma up_list_res_exp (p : nat) {m : nat} {n_exp : nat}
  (sigma : fin m -> exp n_exp) : fin m -> exp n_exp.
Proof.
exact (sigma).
Defined.

Lemma up_list_exp_res (p : nat) {m : nat} {n_res : nat}
  (sigma : fin m -> res n_res) : fin m -> res n_res.
Proof.
exact (sigma).
Defined.


Fixpoint subst_tm {m_res m_exp : nat} {n_res n_exp : nat}
(sigma_res : fin m_res -> res n_res) (sigma_exp : fin m_exp -> exp n_exp)
(s : tm m_res m_exp) {struct s} : tm n_res n_exp :=
  match s with
  | lam _ _ s0 =>
      lam n_res n_exp
        (subst_r_scope (up_res_res sigma_res) (up_res_exp sigma_exp) s0)
  end
with subst_stmt {m_res m_exp : nat} {n_res n_exp : nat}
(sigma_res : fin m_res -> res n_res) (sigma_exp : fin m_exp -> exp n_exp)
(s : stmt m_res m_exp) {struct s} : stmt n_res n_exp :=
  match s with
  | cut _ _ s0 s1 =>
      cut n_res n_exp (subst_res sigma_res s0) (subst_res sigma_res s1)
  | tup _ _ s0 s1 =>
      tup n_res n_exp (subst_res sigma_res s0)
        (list_map (subst_res sigma_res) s1)
  | def _ _ s0 s1 =>
      def n_res n_exp (subst_res sigma_res s0)
        (subst_tm sigma_res sigma_exp s1)
  | nam _ _ s0 s1 =>
      nam n_res n_exp (subst_res sigma_res s0) (subst_exp sigma_exp s1)
  | app _ _ s0 s1 =>
      app n_res n_exp (subst_exp sigma_exp s0) (subst_res sigma_res s1)
  end
with subst_r_scope {m_res m_exp : nat} {n_res n_exp : nat}
(sigma_res : fin m_res -> res n_res) (sigma_exp : fin m_exp -> exp n_exp)
(s : r_scope m_res m_exp) {struct s} : r_scope n_res n_exp :=
  match s with
  | rbnd _ _ n s0 =>
      rbnd n_res n_exp n
        (subst_e_scope (up_list_res_res n sigma_res)
           (up_list_res_exp n sigma_exp) s0)
  end
with subst_e_scope {m_res m_exp : nat} {n_res n_exp : nat}
(sigma_res : fin m_res -> res n_res) (sigma_exp : fin m_exp -> exp n_exp)
(s : e_scope m_res m_exp) {struct s} : e_scope n_res n_exp :=
  match s with
  | ebnd _ _ m s0 =>
      ebnd n_res n_exp m
        (list_map
           (subst_stmt (up_list_exp_res m sigma_res)
              (up_list_exp_exp m sigma_exp)) s0)
  end.


Lemma upId_res_exp {m_exp : nat} (sigma : fin m_exp -> exp m_exp)
  (Eq : forall x, sigma x = var_exp m_exp x) :
  forall x, up_res_exp sigma x = var_exp m_exp x.
Proof.
exact (Eq).
Qed.

Lemma upId_exp_res {m_res : nat} (sigma : fin m_res -> res m_res)
  (Eq : forall x, sigma x = var_res m_res x) :
  forall x, up_exp_res sigma x = var_res m_res x.
Proof.
exact (Eq).  
Qed.

Lemma upId_list_res_exp {p : nat} {m_exp : nat}
  (sigma : fin m_exp -> exp m_exp) (Eq : forall x, sigma x = var_exp m_exp x)
  : forall x, up_list_res_exp p sigma x = var_exp m_exp x.
Proof.
exact (Eq).
Qed.

Lemma upId_list_exp_res {p : nat} {m_res : nat}
  (sigma : fin m_res -> res m_res) (Eq : forall x, sigma x = var_res m_res x)
  : forall x, up_list_exp_res p sigma x = var_res m_res x.
Proof.
exact (Eq).  
Qed.

Fixpoint idSubst_tm {m_res m_exp : nat} (sigma_res : fin m_res -> res m_res)
(sigma_exp : fin m_exp -> exp m_exp)
(Eq_res : forall x, sigma_res x = var_res m_res x)
(Eq_exp : forall x, sigma_exp x = var_exp m_exp x) (s : tm m_res m_exp)
{struct s} : subst_tm sigma_res sigma_exp s = s :=
  match s with
  | lam _ _ s0 =>
      congr_lam
        (idSubst_r_scope (up_res_res sigma_res) (up_res_exp sigma_exp)
           (upId_res_res _ Eq_res) (upId_res_exp _ Eq_exp) s0)
  end
with idSubst_stmt {m_res m_exp : nat} (sigma_res : fin m_res -> res m_res)
(sigma_exp : fin m_exp -> exp m_exp)
(Eq_res : forall x, sigma_res x = var_res m_res x)
(Eq_exp : forall x, sigma_exp x = var_exp m_exp x) (s : stmt m_res m_exp)
{struct s} : subst_stmt sigma_res sigma_exp s = s :=
  match s with
  | cut _ _ s0 s1 =>
      congr_cut (idSubst_res sigma_res Eq_res s0)
        (idSubst_res sigma_res Eq_res s1)
  | tup _ _ s0 s1 =>
      congr_tup (idSubst_res sigma_res Eq_res s0)
        (list_id (idSubst_res sigma_res Eq_res) s1)
  | def _ _ s0 s1 =>
      congr_def (idSubst_res sigma_res Eq_res s0)
        (idSubst_tm sigma_res sigma_exp Eq_res Eq_exp s1)
  | nam _ _ s0 s1 =>
      congr_nam (idSubst_res sigma_res Eq_res s0)
        (idSubst_exp sigma_exp Eq_exp s1)
  | app _ _ s0 s1 =>
      congr_app (idSubst_exp sigma_exp Eq_exp s0)
        (idSubst_res sigma_res Eq_res s1)
  end
with idSubst_r_scope {m_res m_exp : nat} (sigma_res : fin m_res -> res m_res)
(sigma_exp : fin m_exp -> exp m_exp)
(Eq_res : forall x, sigma_res x = var_res m_res x)
(Eq_exp : forall x, sigma_exp x = var_exp m_exp x) (s : r_scope m_res m_exp)
{struct s} : subst_r_scope sigma_res sigma_exp s = s :=
  match s with
  | rbnd _ _ n s0 =>
      congr_rbnd
        (idSubst_e_scope (up_list_res_res n sigma_res)
           (up_list_res_exp n sigma_exp) (upId_list_res_res _ Eq_res)
           (upId_list_res_exp _ Eq_exp) s0)
  end
with idSubst_e_scope {m_res m_exp : nat} (sigma_res : fin m_res -> res m_res)
(sigma_exp : fin m_exp -> exp m_exp)
(Eq_res : forall x, sigma_res x = var_res m_res x)
(Eq_exp : forall x, sigma_exp x = var_exp m_exp x) (s : e_scope m_res m_exp)
{struct s} : subst_e_scope sigma_res sigma_exp s = s :=
  match s with
  | ebnd _ _ m s0 =>
      congr_ebnd
        (list_id
           (idSubst_stmt (up_list_exp_res m sigma_res)
              (up_list_exp_exp m sigma_exp) (upId_list_exp_res _ Eq_res)
              (upId_list_exp_exp _ Eq_exp)) s0)
  end.

Lemma upExt_res_exp {m : nat} {n_exp : nat} (sigma : fin m -> exp n_exp)
  (tau : fin m -> exp n_exp) (Eq : forall x, sigma x = tau x) :
  forall x, up_res_exp sigma x = up_res_exp tau x.
Proof.
exact (Eq).  
Qed.

Lemma upExt_exp_res {m : nat} {n_res : nat} (sigma : fin m -> res n_res)
  (tau : fin m -> res n_res) (Eq : forall x, sigma x = tau x) :
  forall x, up_exp_res sigma x = up_exp_res tau x.
Proof.
exact (Eq).
Qed.

Lemma upExt_list_res_exp {p : nat} {m : nat} {n_exp : nat}
  (sigma : fin m -> exp n_exp) (tau : fin m -> exp n_exp)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_res_exp p sigma x = up_list_res_exp p tau x.
Proof.
exact (Eq).
Qed.

Lemma upExt_list_exp_res {p : nat} {m : nat} {n_res : nat}
  (sigma : fin m -> res n_res) (tau : fin m -> res n_res)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_exp_res p sigma x = up_list_exp_res p tau x.
Proof.
exact (Eq).
Qed.

Fixpoint ext_tm {m_res m_exp : nat} {n_res n_exp : nat}
(sigma_res : fin m_res -> res n_res) (sigma_exp : fin m_exp -> exp n_exp)
(tau_res : fin m_res -> res n_res) (tau_exp : fin m_exp -> exp n_exp)
(Eq_res : forall x, sigma_res x = tau_res x)
(Eq_exp : forall x, sigma_exp x = tau_exp x) (s : tm m_res m_exp) {struct s}
   : subst_tm sigma_res sigma_exp s = subst_tm tau_res tau_exp s :=
  match s with
  | lam _ _ s0 =>
      congr_lam
        (ext_r_scope (up_res_res sigma_res) (up_res_exp sigma_exp)
           (up_res_res tau_res) (up_res_exp tau_exp)
           (upExt_res_res _ _ Eq_res) (upExt_res_exp _ _ Eq_exp) s0)
  end
with ext_stmt {m_res m_exp : nat} {n_res n_exp : nat}
(sigma_res : fin m_res -> res n_res) (sigma_exp : fin m_exp -> exp n_exp)
(tau_res : fin m_res -> res n_res) (tau_exp : fin m_exp -> exp n_exp)
(Eq_res : forall x, sigma_res x = tau_res x)
(Eq_exp : forall x, sigma_exp x = tau_exp x) (s : stmt m_res m_exp) {struct
 s} : subst_stmt sigma_res sigma_exp s = subst_stmt tau_res tau_exp s :=
  match s with
  | cut _ _ s0 s1 =>
      congr_cut (ext_res sigma_res tau_res Eq_res s0)
        (ext_res sigma_res tau_res Eq_res s1)
  | tup _ _ s0 s1 =>
      congr_tup (ext_res sigma_res tau_res Eq_res s0)
        (list_ext (ext_res sigma_res tau_res Eq_res) s1)
  | def _ _ s0 s1 =>
      congr_def (ext_res sigma_res tau_res Eq_res s0)
        (ext_tm sigma_res sigma_exp tau_res tau_exp Eq_res Eq_exp s1)
  | nam _ _ s0 s1 =>
      congr_nam (ext_res sigma_res tau_res Eq_res s0)
        (ext_exp sigma_exp tau_exp Eq_exp s1)
  | app _ _ s0 s1 =>
      congr_app (ext_exp sigma_exp tau_exp Eq_exp s0)
        (ext_res sigma_res tau_res Eq_res s1)
  end
with ext_r_scope {m_res m_exp : nat} {n_res n_exp : nat}
(sigma_res : fin m_res -> res n_res) (sigma_exp : fin m_exp -> exp n_exp)
(tau_res : fin m_res -> res n_res) (tau_exp : fin m_exp -> exp n_exp)
(Eq_res : forall x, sigma_res x = tau_res x)
(Eq_exp : forall x, sigma_exp x = tau_exp x) (s : r_scope m_res m_exp)
{struct s} :
subst_r_scope sigma_res sigma_exp s = subst_r_scope tau_res tau_exp s :=
  match s with
  | rbnd _ _ n s0 =>
      congr_rbnd
        (ext_e_scope (up_list_res_res n sigma_res)
           (up_list_res_exp n sigma_exp) (up_list_res_res n tau_res)
           (up_list_res_exp n tau_exp) (upExt_list_res_res _ _ Eq_res)
           (upExt_list_res_exp _ _ Eq_exp) s0)
  end
with ext_e_scope {m_res m_exp : nat} {n_res n_exp : nat}
(sigma_res : fin m_res -> res n_res) (sigma_exp : fin m_exp -> exp n_exp)
(tau_res : fin m_res -> res n_res) (tau_exp : fin m_exp -> exp n_exp)
(Eq_res : forall x, sigma_res x = tau_res x)
(Eq_exp : forall x, sigma_exp x = tau_exp x) (s : e_scope m_res m_exp)
{struct s} :
subst_e_scope sigma_res sigma_exp s = subst_e_scope tau_res tau_exp s :=
  match s with
  | ebnd _ _ m s0 =>
      congr_ebnd
        (list_ext
           (ext_stmt (up_list_exp_res m sigma_res)
              (up_list_exp_exp m sigma_exp) (up_list_exp_res m tau_res)
              (up_list_exp_exp m tau_exp) (upExt_list_exp_res _ _ Eq_res)
              (upExt_list_exp_exp _ _ Eq_exp)) s0)
  end.

Lemma up_subst_subst_res_exp {k : nat} {l_exp : nat} {m_exp : nat}
  (sigma : fin k -> exp l_exp) (tau_exp : fin l_exp -> exp m_exp)
  (theta : fin k -> exp m_exp)
  (Eq : forall x, funcomp (subst_exp tau_exp) sigma x = theta x) :
  forall x,
  funcomp (subst_exp (up_res_exp tau_exp)) (up_res_exp sigma) x =
  up_res_exp theta x.
Proof.
  intros n.
  unfold up_res_exp.
  apply Eq.
Qed.


Lemma up_subst_subst_exp_res {k : nat} {l_res : nat} {m_res : nat}
  (sigma : fin k -> res l_res) (tau_res : fin l_res -> res m_res)
  (theta : fin k -> res m_res)
  (Eq : forall x, funcomp (subst_res tau_res) sigma x = theta x) :
  forall x,
  funcomp (subst_res (up_exp_res tau_res)) (up_exp_res sigma) x =
  up_exp_res theta x.
Proof.
  intros n.
  unfold up_exp_res.
  apply Eq.
Qed.  

Lemma up_subst_subst_list_res_exp {p : nat} {k : nat} {l_exp : nat}
  {m_exp : nat} (sigma : fin k -> exp l_exp)
  (tau_exp : fin l_exp -> exp m_exp) (theta : fin k -> exp m_exp)
  (Eq : forall x, funcomp (subst_exp tau_exp) sigma x = theta x) :
  forall x,
  funcomp (subst_exp (up_list_res_exp p tau_exp)) (up_list_res_exp p sigma) x =
  up_list_res_exp p theta x.
Proof.
  intros n.
  unfold up_list_res_exp.
  apply Eq.
Qed.

Lemma up_subst_subst_list_exp_res {p : nat} {k : nat} {l_res : nat}
  {m_res : nat} (sigma : fin k -> res l_res)
  (tau_res : fin l_res -> res m_res) (theta : fin k -> res m_res)
  (Eq : forall x, funcomp (subst_res tau_res) sigma x = theta x) :
  forall x,
  funcomp (subst_res (up_list_exp_res p tau_res)) (up_list_exp_res p sigma) x =
  up_list_exp_res p theta x.
Proof.
  intros n.
  unfold up_list_exp_res.
  apply Eq.
Qed.

Fixpoint compSubstSubst_tm {k_res k_exp : nat} {l_res l_exp : nat}
{m_res m_exp : nat} (sigma_res : fin m_res -> res k_res)
(sigma_exp : fin m_exp -> exp k_exp) (tau_res : fin k_res -> res l_res)
(tau_exp : fin k_exp -> exp l_exp) (theta_res : fin m_res -> res l_res)
(theta_exp : fin m_exp -> exp l_exp)
(Eq_res : forall x, funcomp (subst_res tau_res) sigma_res x = theta_res x)
(Eq_exp : forall x, funcomp (subst_exp tau_exp) sigma_exp x = theta_exp x)
(s : tm m_res m_exp) {struct s} :
subst_tm tau_res tau_exp (subst_tm sigma_res sigma_exp s) =
subst_tm theta_res theta_exp s :=
  match s with
  | lam _ _ s0 =>
      congr_lam
        (compSubstSubst_r_scope (up_res_res sigma_res) (up_res_exp sigma_exp)
           (up_res_res tau_res) (up_res_exp tau_exp) (up_res_res theta_res)
           (up_res_exp theta_exp) (up_subst_subst_res_res _ _ _ Eq_res)
           (up_subst_subst_res_exp _ _ _ Eq_exp) s0)
  end
with compSubstSubst_stmt {k_res k_exp : nat} {l_res l_exp : nat}
{m_res m_exp : nat} (sigma_res : fin m_res -> res k_res)
(sigma_exp : fin m_exp -> exp k_exp) (tau_res : fin k_res -> res l_res)
(tau_exp : fin k_exp -> exp l_exp) (theta_res : fin m_res -> res l_res)
(theta_exp : fin m_exp -> exp l_exp)
(Eq_res : forall x, funcomp (subst_res tau_res) sigma_res x = theta_res x)
(Eq_exp : forall x, funcomp (subst_exp tau_exp) sigma_exp x = theta_exp x)
(s : stmt m_res m_exp) {struct s} :
subst_stmt tau_res tau_exp (subst_stmt sigma_res sigma_exp s) =
subst_stmt theta_res theta_exp s :=
  match s with
  | cut _ _ s0 s1 =>
      congr_cut (compSubstSubst_res sigma_res tau_res theta_res Eq_res s0)
        (compSubstSubst_res sigma_res tau_res theta_res Eq_res s1)
  | tup _ _ s0 s1 =>
      congr_tup (compSubstSubst_res sigma_res tau_res theta_res Eq_res s0)
        (list_comp (compSubstSubst_res sigma_res tau_res theta_res Eq_res) s1)
  | def _ _ s0 s1 =>
      congr_def (compSubstSubst_res sigma_res tau_res theta_res Eq_res s0)
        (compSubstSubst_tm sigma_res sigma_exp tau_res tau_exp theta_res
           theta_exp Eq_res Eq_exp s1)
  | nam _ _ s0 s1 =>
      congr_nam (compSubstSubst_res sigma_res tau_res theta_res Eq_res s0)
        (compSubstSubst_exp sigma_exp tau_exp theta_exp Eq_exp s1)
  | app _ _ s0 s1 =>
      congr_app (compSubstSubst_exp sigma_exp tau_exp theta_exp Eq_exp s0)
        (compSubstSubst_res sigma_res tau_res theta_res Eq_res s1)
  end
with compSubstSubst_r_scope {k_res k_exp : nat} {l_res l_exp : nat}
{m_res m_exp : nat} (sigma_res : fin m_res -> res k_res)
(sigma_exp : fin m_exp -> exp k_exp) (tau_res : fin k_res -> res l_res)
(tau_exp : fin k_exp -> exp l_exp) (theta_res : fin m_res -> res l_res)
(theta_exp : fin m_exp -> exp l_exp)
(Eq_res : forall x, funcomp (subst_res tau_res) sigma_res x = theta_res x)
(Eq_exp : forall x, funcomp (subst_exp tau_exp) sigma_exp x = theta_exp x)
(s : r_scope m_res m_exp) {struct s} :
subst_r_scope tau_res tau_exp (subst_r_scope sigma_res sigma_exp s) =
subst_r_scope theta_res theta_exp s :=
  match s with
  | rbnd _ _ n s0 =>
      congr_rbnd
        (compSubstSubst_e_scope (up_list_res_res n sigma_res)
           (up_list_res_exp n sigma_exp) (up_list_res_res n tau_res)
           (up_list_res_exp n tau_exp) (up_list_res_res n theta_res)
           (up_list_res_exp n theta_exp)
           (up_subst_subst_list_res_res _ _ _ Eq_res)
           (up_subst_subst_list_res_exp _ _ _ Eq_exp) s0)
  end
with compSubstSubst_e_scope {k_res k_exp : nat} {l_res l_exp : nat}
{m_res m_exp : nat} (sigma_res : fin m_res -> res k_res)
(sigma_exp : fin m_exp -> exp k_exp) (tau_res : fin k_res -> res l_res)
(tau_exp : fin k_exp -> exp l_exp) (theta_res : fin m_res -> res l_res)
(theta_exp : fin m_exp -> exp l_exp)
(Eq_res : forall x, funcomp (subst_res tau_res) sigma_res x = theta_res x)
(Eq_exp : forall x, funcomp (subst_exp tau_exp) sigma_exp x = theta_exp x)
(s : e_scope m_res m_exp) {struct s} :
subst_e_scope tau_res tau_exp (subst_e_scope sigma_res sigma_exp s) =
subst_e_scope theta_res theta_exp s :=
  match s with
  | ebnd _ _ m s0 =>
      congr_ebnd
        (list_comp
           (compSubstSubst_stmt (up_list_exp_res m sigma_res)
              (up_list_exp_exp m sigma_exp) (up_list_exp_res m tau_res)
              (up_list_exp_exp m tau_exp) (up_list_exp_res m theta_res)
              (up_list_exp_exp m theta_exp)
              (up_subst_subst_list_exp_res _ _ _ Eq_res)
              (up_subst_subst_list_exp_exp _ _ _ Eq_exp)) s0)
  end.


Lemma substSubst_tm {k_res k_exp : nat} {l_res l_exp : nat}
  {m_res m_exp : nat} (sigma_res : fin m_res -> res k_res)
  (sigma_exp : fin m_exp -> exp k_exp) (tau_res : fin k_res -> res l_res)
  (tau_exp : fin k_exp -> exp l_exp) (s : tm m_res m_exp) :
  subst_tm tau_res tau_exp (subst_tm sigma_res sigma_exp s) =
  subst_tm (funcomp (subst_res tau_res) sigma_res)
    (funcomp (subst_exp tau_exp) sigma_exp) s.
Proof.
exact (compSubstSubst_tm sigma_res sigma_exp tau_res tau_exp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm_pointwise {k_res k_exp : nat} {l_res l_exp : nat}
  {m_res m_exp : nat} (sigma_res : fin m_res -> res k_res)
  (sigma_exp : fin m_exp -> exp k_exp) (tau_res : fin k_res -> res l_res)
  (tau_exp : fin k_exp -> exp l_exp) :
  pointwise_relation _ eq
    (funcomp (subst_tm tau_res tau_exp) (subst_tm sigma_res sigma_exp))
    (subst_tm (funcomp (subst_res tau_res) sigma_res)
       (funcomp (subst_exp tau_exp) sigma_exp)).
Proof.
exact (fun s =>
       compSubstSubst_tm sigma_res sigma_exp tau_res tau_exp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_stmt {k_res k_exp : nat} {l_res l_exp : nat}
  {m_res m_exp : nat} (sigma_res : fin m_res -> res k_res)
  (sigma_exp : fin m_exp -> exp k_exp) (tau_res : fin k_res -> res l_res)
  (tau_exp : fin k_exp -> exp l_exp) (s : stmt m_res m_exp) :
  subst_stmt tau_res tau_exp (subst_stmt sigma_res sigma_exp s) =
  subst_stmt (funcomp (subst_res tau_res) sigma_res)
    (funcomp (subst_exp tau_exp) sigma_exp) s.
Proof.
exact (compSubstSubst_stmt sigma_res sigma_exp tau_res tau_exp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_stmt_pointwise {k_res k_exp : nat} {l_res l_exp : nat}
  {m_res m_exp : nat} (sigma_res : fin m_res -> res k_res)
  (sigma_exp : fin m_exp -> exp k_exp) (tau_res : fin k_res -> res l_res)
  (tau_exp : fin k_exp -> exp l_exp) :
  pointwise_relation _ eq
    (funcomp (subst_stmt tau_res tau_exp) (subst_stmt sigma_res sigma_exp))
    (subst_stmt (funcomp (subst_res tau_res) sigma_res)
       (funcomp (subst_exp tau_exp) sigma_exp)).
Proof.
exact (fun s =>
       compSubstSubst_stmt sigma_res sigma_exp tau_res tau_exp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_r_scope {k_res k_exp : nat} {l_res l_exp : nat}
  {m_res m_exp : nat} (sigma_res : fin m_res -> res k_res)
  (sigma_exp : fin m_exp -> exp k_exp) (tau_res : fin k_res -> res l_res)
  (tau_exp : fin k_exp -> exp l_exp) (s : r_scope m_res m_exp) :
  subst_r_scope tau_res tau_exp (subst_r_scope sigma_res sigma_exp s) =
  subst_r_scope (funcomp (subst_res tau_res) sigma_res)
    (funcomp (subst_exp tau_exp) sigma_exp) s.
Proof.
exact (compSubstSubst_r_scope sigma_res sigma_exp tau_res tau_exp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_r_scope_pointwise {k_res k_exp : nat} {l_res l_exp : nat}
  {m_res m_exp : nat} (sigma_res : fin m_res -> res k_res)
  (sigma_exp : fin m_exp -> exp k_exp) (tau_res : fin k_res -> res l_res)
  (tau_exp : fin k_exp -> exp l_exp) :
  pointwise_relation _ eq
    (funcomp (subst_r_scope tau_res tau_exp)
       (subst_r_scope sigma_res sigma_exp))
    (subst_r_scope (funcomp (subst_res tau_res) sigma_res)
       (funcomp (subst_exp tau_exp) sigma_exp)).
Proof.
exact (fun s =>
       compSubstSubst_r_scope sigma_res sigma_exp tau_res tau_exp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_e_scope {k_res k_exp : nat} {l_res l_exp : nat}
  {m_res m_exp : nat} (sigma_res : fin m_res -> res k_res)
  (sigma_exp : fin m_exp -> exp k_exp) (tau_res : fin k_res -> res l_res)
  (tau_exp : fin k_exp -> exp l_exp) (s : e_scope m_res m_exp) :
  subst_e_scope tau_res tau_exp (subst_e_scope sigma_res sigma_exp s) =
  subst_e_scope (funcomp (subst_res tau_res) sigma_res)
    (funcomp (subst_exp tau_exp) sigma_exp) s.
Proof.
exact (compSubstSubst_e_scope sigma_res sigma_exp tau_res tau_exp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_e_scope_pointwise {k_res k_exp : nat} {l_res l_exp : nat}
  {m_res m_exp : nat} (sigma_res : fin m_res -> res k_res)
  (sigma_exp : fin m_exp -> exp k_exp) (tau_res : fin k_res -> res l_res)
  (tau_exp : fin k_exp -> exp l_exp) :
  pointwise_relation _ eq
    (funcomp (subst_e_scope tau_res tau_exp)
       (subst_e_scope sigma_res sigma_exp))
    (subst_e_scope (funcomp (subst_res tau_res) sigma_res)
       (funcomp (subst_exp tau_exp) sigma_exp)).
Proof.
exact (fun s =>
       compSubstSubst_e_scope sigma_res sigma_exp tau_res tau_exp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma instId'_tm {m_res m_exp : nat} (s : tm m_res m_exp) :
  subst_tm (var_res m_res) (var_exp m_exp) s = s.
Proof.
exact (idSubst_tm (var_res m_res) (var_exp m_exp) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma instId'_tm_pointwise {m_res m_exp : nat} :
  pointwise_relation _ eq (subst_tm (var_res m_res) (var_exp m_exp)) id.
Proof.
exact (fun s =>
       idSubst_tm (var_res m_res) (var_exp m_exp) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma instId'_stmt {m_res m_exp : nat} (s : stmt m_res m_exp) :
  subst_stmt (var_res m_res) (var_exp m_exp) s = s.
Proof.
exact (idSubst_stmt (var_res m_res) (var_exp m_exp) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma instId'_stmt_pointwise {m_res m_exp : nat} :
  pointwise_relation _ eq (subst_stmt (var_res m_res) (var_exp m_exp)) id.
Proof.
exact (fun s =>
       idSubst_stmt (var_res m_res) (var_exp m_exp) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma instId'_r_scope {m_res m_exp : nat} (s : r_scope m_res m_exp) :
  subst_r_scope (var_res m_res) (var_exp m_exp) s = s.
Proof.
exact (idSubst_r_scope (var_res m_res) (var_exp m_exp) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma instId'_r_scope_pointwise {m_res m_exp : nat} :
  pointwise_relation _ eq (subst_r_scope (var_res m_res) (var_exp m_exp)) id.
Proof.
exact (fun s =>
       idSubst_r_scope (var_res m_res) (var_exp m_exp) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma instId'_e_scope {m_res m_exp : nat} (s : e_scope m_res m_exp) :
  subst_e_scope (var_res m_res) (var_exp m_exp) s = s.
Proof.
exact (idSubst_e_scope (var_res m_res) (var_exp m_exp) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma instId'_e_scope_pointwise {m_res m_exp : nat} :
  pointwise_relation _ eq (subst_e_scope (var_res m_res) (var_exp m_exp)) id.
Proof.
exact (fun s =>
       idSubst_e_scope (var_res m_res) (var_exp m_exp) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Class Up_e_scope X Y :=
    up_e_scope : X -> Y.

Class Up_r_scope X Y :=
    up_r_scope : X -> Y.

Class Up_stmt X Y :=
    up_stmt : X -> Y.

Class Up_tm X Y :=
    up_tm : X -> Y.

Class Up_exp X Y :=
    up_exp : X -> Y.

Class Up_res X Y :=
    up_res : X -> Y.

#[global]
Instance Up_exp_res  {m n_res : nat}: (Up_res _ _) := (@up_exp_res m n_res).

#[global]
Instance Up_res_exp  {m n_exp : nat}: (Up_exp _ _) := (@up_res_exp m n_exp).

#[global]
Instance Subst_e_scope  {m_res m_exp n_res n_exp : nat}: (Subst2 _ _ _ _) :=
 (@subst_e_scope m_res m_exp n_res n_exp).

#[global]
Instance Subst_r_scope  {m_res m_exp n_res n_exp : nat}: (Subst2 _ _ _ _) :=
 (@subst_r_scope m_res m_exp n_res n_exp).

#[global]
Instance Subst_stmt  {m_res m_exp n_res n_exp : nat}: (Subst2 _ _ _ _) :=
 (@subst_stmt m_res m_exp n_res n_exp).

#[global]
Instance Subst_tm  {m_res m_exp n_res n_exp : nat}: (Subst2 _ _ _ _) :=
 (@subst_tm m_res m_exp n_res n_exp).

#[global]
Instance Up_exp_exp  {m n_exp : nat}: (Up_exp _ _) := (@up_exp_exp m n_exp).

#[global]
Instance Subst_exp  {m_exp n_exp : nat}: (Subst1 _ _ _) :=
 (@subst_exp m_exp n_exp).

#[global]
Instance VarInstance_exp  {n_exp : nat}: (Var _ _) := (@var_exp n_exp).

#[global]
Instance Up_res_res  {m n_res : nat}: (Up_res _ _) := (@up_res_res m n_res).

#[global]
Instance Subst_res  {m_res n_res : nat}: (Subst1 _ _ _) :=
 (@subst_res m_res n_res).

#[global]
Instance VarInstance_res  {n_res : nat}: (Var _ _) := (@var_res n_res).

Notation "↑__res" := up_exp_res (only printing)  : subst_scope.

Notation "↑__exp" := up_res_exp (only printing)  : subst_scope.

Notation "[ sigma_res ; sigma_exp ]" := (subst_e_scope sigma_res sigma_exp)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_res ; sigma_exp ]" :=
(subst_e_scope sigma_res sigma_exp s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__e_scope" := up_e_scope (only printing)  : subst_scope.

Notation "[ sigma_res ; sigma_exp ]" := (subst_r_scope sigma_res sigma_exp)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_res ; sigma_exp ]" :=
(subst_r_scope sigma_res sigma_exp s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__r_scope" := up_r_scope (only printing)  : subst_scope.

Notation "[ sigma_res ; sigma_exp ]" := (subst_stmt sigma_res sigma_exp)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_res ; sigma_exp ]" := (subst_stmt sigma_res sigma_exp s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__stmt" := up_stmt (only printing)  : subst_scope.

Notation "[ sigma_res ; sigma_exp ]" := (subst_tm sigma_res sigma_exp)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_res ; sigma_exp ]" := (subst_tm sigma_res sigma_exp s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__tm" := up_tm (only printing)  : subst_scope.

Notation "↑__exp" := up_exp_exp (only printing)  : subst_scope.

Notation "[ sigma_exp ]" := (subst_exp sigma_exp)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_exp ]" := (subst_exp sigma_exp s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__exp" := up_exp (only printing)  : subst_scope.

Notation "'var'" := var_exp ( at level 1, only printing)  : subst_scope.

Notation "x '__exp'" := (@ids _ _ VarInstance_exp x)
( at level 5, format "x __exp", only printing)  : subst_scope.

Notation "x '__exp'" := (var_exp x) ( at level 5, format "x __exp")  :
subst_scope.

Notation "↑__res" := up_res_res (only printing)  : subst_scope.

Notation "[ sigma_res ]" := (subst_res sigma_res)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_res ]" := (subst_res sigma_res s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__res" := up_res (only printing)  : subst_scope.

Notation "'var'" := var_res ( at level 1, only printing)  : subst_scope.

Notation "x '__res'" := (@ids _ _ VarInstance_res x)
( at level 5, format "x __res", only printing)  : subst_scope.

Notation "x '__res'" := (var_res x) ( at level 5, format "x __res")  :
subst_scope.

#[global]
Instance subst_e_scope_morphism  {m_res m_exp : nat} {n_res n_exp : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@subst_e_scope m_res m_exp n_res n_exp)).
Proof.
exact (fun f_res g_res Eq_res f_exp g_exp Eq_exp s t Eq_st =>
       eq_ind s
         (fun t' =>
          subst_e_scope f_res f_exp s = subst_e_scope g_res g_exp t')
         (ext_e_scope f_res f_exp g_res g_exp Eq_res Eq_exp s) t Eq_st).
Qed.

#[global]
Instance subst_e_scope_morphism2  {m_res m_exp : nat} {n_res n_exp : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@subst_e_scope m_res m_exp n_res n_exp)).
Proof.
exact (fun f_res g_res Eq_res f_exp g_exp Eq_exp s =>
       ext_e_scope f_res f_exp g_res g_exp Eq_res Eq_exp s).
Qed.

#[global]
Instance subst_r_scope_morphism  {m_res m_exp : nat} {n_res n_exp : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@subst_r_scope m_res m_exp n_res n_exp)).
Proof.
exact (fun f_res g_res Eq_res f_exp g_exp Eq_exp s t Eq_st =>
       eq_ind s
         (fun t' =>
          subst_r_scope f_res f_exp s = subst_r_scope g_res g_exp t')
         (ext_r_scope f_res f_exp g_res g_exp Eq_res Eq_exp s) t Eq_st).
Qed.

#[global]
Instance subst_r_scope_morphism2  {m_res m_exp : nat} {n_res n_exp : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@subst_r_scope m_res m_exp n_res n_exp)).
Proof.
exact (fun f_res g_res Eq_res f_exp g_exp Eq_exp s =>
       ext_r_scope f_res f_exp g_res g_exp Eq_res Eq_exp s).
Qed.

#[global]
Instance subst_stmt_morphism  {m_res m_exp : nat} {n_res n_exp : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@subst_stmt m_res m_exp n_res n_exp)).
Proof.
exact (fun f_res g_res Eq_res f_exp g_exp Eq_exp s t Eq_st =>
       eq_ind s
         (fun t' => subst_stmt f_res f_exp s = subst_stmt g_res g_exp t')
         (ext_stmt f_res f_exp g_res g_exp Eq_res Eq_exp s) t Eq_st).
Qed.

#[global]
Instance subst_stmt_morphism2  {m_res m_exp : nat} {n_res n_exp : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@subst_stmt m_res m_exp n_res n_exp)).
Proof.
exact (fun f_res g_res Eq_res f_exp g_exp Eq_exp s =>
       ext_stmt f_res f_exp g_res g_exp Eq_res Eq_exp s).
Qed.

#[global]
Instance subst_tm_morphism  {m_res m_exp : nat} {n_res n_exp : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@subst_tm m_res m_exp n_res n_exp)).
Proof.
exact (fun f_res g_res Eq_res f_exp g_exp Eq_exp s t Eq_st =>
       eq_ind s (fun t' => subst_tm f_res f_exp s = subst_tm g_res g_exp t')
         (ext_tm f_res f_exp g_res g_exp Eq_res Eq_exp s) t Eq_st).
Qed.

#[global]
Instance subst_tm_morphism2  {m_res m_exp : nat} {n_res n_exp : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@subst_tm m_res m_exp n_res n_exp)).
Proof.
exact (fun f_res g_res Eq_res f_exp g_exp Eq_exp s =>
       ext_tm f_res f_exp g_res g_exp Eq_res Eq_exp s).
Qed.

#[global]
Instance subst_exp_morphism  {m_exp : nat} {n_exp : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_exp m_exp n_exp)).
Proof.
exact (fun f_exp g_exp Eq_exp s t Eq_st =>
       eq_ind s (fun t' => subst_exp f_exp s = subst_exp g_exp t')
         (ext_exp f_exp g_exp Eq_exp s) t Eq_st).
Qed.

#[global]
Instance subst_exp_morphism2  {m_exp : nat} {n_exp : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_exp m_exp n_exp)).
Proof.
exact (fun f_exp g_exp Eq_exp s => ext_exp f_exp g_exp Eq_exp s).
Qed.

#[global]
Instance subst_res_morphism  {m_res : nat} {n_res : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_res m_res n_res)).
Proof.
exact (fun f_res g_res Eq_res s t Eq_st =>
       eq_ind s (fun t' => subst_res f_res s = subst_res g_res t')
         (ext_res f_res g_res Eq_res s) t Eq_st).
Qed.

#[global]
Instance subst_res_morphism2  {m_res : nat} {n_res : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_res m_res n_res)).
Proof.
exact (fun f_res g_res Eq_res s => ext_res f_res g_res Eq_res s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_res, Var, ids, Subst_res, Subst1,
                      subst1, Up_res_res, Up_res, up_res, VarInstance_exp,
                      Var, ids, Subst_exp, Subst1, subst1, Up_exp_exp,
                      Up_exp, up_exp, Subst_tm, Subst2, subst2, Subst_stmt,
                      Subst2, subst2, Subst_r_scope, Subst2, subst2,
                      Subst_e_scope, Subst2, subst2, Up_res_exp, Up_exp,
                      up_exp, Up_exp_res, Up_res, up_res.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_res, Var, ids,
                                            Subst_res, Subst1, subst1,
                                            Up_res_res, Up_res, up_res,
                                            VarInstance_exp, Var, ids,
                                            Subst_exp, Subst1, subst1,
                                            Up_exp_exp, Up_exp, up_exp,
                                            Subst_tm, Subst2, subst2,
                                            Subst_stmt, Subst2, subst2,
                                            Subst_r_scope, Subst2, subst2,
                                            Subst_e_scope, Subst2, subst2,
                                            Up_res_exp, Up_exp, up_exp,
                                            Up_exp_res, Up_res, up_res 
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_e_scope_pointwise
                 | progress setoid_rewrite substSubst_e_scope
                 | progress setoid_rewrite substSubst_r_scope_pointwise
                 | progress setoid_rewrite substSubst_r_scope
                 | progress setoid_rewrite substSubst_stmt_pointwise
                 | progress setoid_rewrite substSubst_stmt
                 | progress setoid_rewrite substSubst_tm_pointwise
                 | progress setoid_rewrite substSubst_tm
                 | progress setoid_rewrite substSubst_exp_pointwise
                 | progress setoid_rewrite substSubst_exp
                 | progress setoid_rewrite substSubst_res_pointwise
                 | progress setoid_rewrite substSubst_res
                 | progress setoid_rewrite instId'_e_scope_pointwise
                 | progress setoid_rewrite instId'_e_scope
                 | progress setoid_rewrite instId'_r_scope_pointwise
                 | progress setoid_rewrite instId'_r_scope
                 | progress setoid_rewrite instId'_stmt_pointwise
                 | progress setoid_rewrite instId'_stmt
                 | progress setoid_rewrite instId'_tm_pointwise
                 | progress setoid_rewrite instId'_tm
                 | progress setoid_rewrite varL'_exp_pointwise
                 | progress setoid_rewrite varL'_exp
                 | progress setoid_rewrite instId'_exp_pointwise
                 | progress setoid_rewrite instId'_exp
                 | progress setoid_rewrite varL'_res_pointwise
                 | progress setoid_rewrite varL'_res
                 | progress setoid_rewrite instId'_res_pointwise
                 | progress setoid_rewrite instId'_res
                 | progress
                    unfold up_list_exp_res, up_list_res_exp, up_exp_res,
                     up_res_exp, up_list_exp_exp, up_exp_exp,
                     up_list_res_res, up_res_res, up_ren
                 | progress
                    cbn[subst_e_scope subst_r_scope subst_stmt subst_tm
                       subst_exp subst_res]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_res, Var, ids, Subst_res, Subst1, subst1,
                  Up_res_res, Up_res, up_res, VarInstance_exp, Var, ids,
                  Subst_exp, Subst1, subst1, Up_exp_exp, Up_exp, up_exp,
                  Subst_tm, Subst2, subst2, Subst_stmt, Subst2, subst2,
                  Subst_r_scope, Subst2, subst2, Subst_e_scope, Subst2,
                  subst2, Up_res_exp, Up_exp, up_exp, Up_exp_res, Up_res,
                  up_res in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold.

Ltac renamify := auto_unfold.

End Core.

Module Extra.

Import
Core.

Arguments ebnd {n_res n_exp}.

Arguments rbnd {n_res n_exp}.

Arguments app {n_res n_exp}.

Arguments nam {n_res n_exp}.

Arguments def {n_res n_exp}.

Arguments tup {n_res n_exp}.

Arguments cut {n_res n_exp}.

Arguments lam {n_res n_exp}.

Arguments var_exp {n_exp}.

Arguments var_res {n_res}.

#[global]Hint Opaque subst_e_scope: rewrite.

#[global]Hint Opaque subst_r_scope: rewrite.

#[global]Hint Opaque subst_stmt: rewrite.

#[global]Hint Opaque subst_tm: rewrite.

#[global]Hint Opaque subst_exp: rewrite.

#[global]Hint Opaque subst_res: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

