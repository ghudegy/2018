Require Export D.

(* Subtask 1 *)

Theorem double_negation_excluded_middle : 이중부정 -> 배중률.
Proof.
  (* FILL IN HERE *)
  intros NNPP P. apply NNPP. intros Hc.
  eassert (~P) by (intros HP; destruct (Hc (@or_introl P (~P) HP))).
  destruct (Hc (@or_intror P (~P) H)).
Qed.

(* Natural Excluded Middle *)
Inductive nat_value :=
| Add : nat_value -> nat_value -> nat_value
| Mul : nat_value -> nat_value -> nat_value
| Var : nat -> nat_value
.

Inductive nat_prop :=
| And : nat_prop -> nat_prop -> nat_prop
| Or : nat_prop -> nat_prop -> nat_prop
| Implies : nat_prop -> nat_prop -> nat_prop
| Not : nat_prop -> nat_prop
| Forall : nat -> nat -> nat_prop -> nat_prop
| Exists : nat -> nat -> nat_prop -> nat_prop
| Eq : nat_value -> nat_value -> nat_prop
| Le : nat_value -> nat_value -> nat_prop
.

Fixpoint nv_to_nat (nv : nat_value) (env : nat -> nat) : nat :=
  match nv with
  | Add nv1 nv2 => (nv_to_nat nv1 env) + (nv_to_nat nv2 env)
  | Mul nv1 nv2 => (nv_to_nat nv1 env) * (nv_to_nat nv2 env)
  | Var v => env v
  end
.

Fixpoint np_to_prop (np : nat_prop) (env : nat -> nat) : Prop :=
  match np with
  | And np1 np2 => (np_to_prop np1 env) /\ (np_to_prop np2 env)
  | Or np1 np2 => (np_to_prop np1 env) \/ (np_to_prop np2 env)
  | Implies np1 np2 => (np_to_prop np1 env) -> (np_to_prop np2 env)
  | Not np' => ~(np_to_prop np' env)
  | Forall x l np' =>
    forall y, y < (env l) -> (np_to_prop np' (
      fun n => if Nat.eqb n x then y else env n
    ))
  | Exists x l np' =>
    exists y, y < (env l) /\ (np_to_prop np' (
      fun n => if Nat.eqb n x then y else env n
    ))
  | Eq nv1 nv2 => (nv_to_nat nv1 env) = (nv_to_nat nv2 env)
  | Le nv1 nv2 => (nv_to_nat nv1 env) <= (nv_to_nat nv2 env)
  end
.

Lemma excluded_middle_np : forall (np : nat_prop) (env : nat -> nat),
  (np_to_prop np env) \/ ~(np_to_prop np env).
Proof.
  induction np; intros.
  + destruct (IHnp1 env); destruct (IHnp2 env); try (
      right; simpl; intros [Hl Hr]; eauto; fail
    ). left. simpl; split; eauto.
  + destruct (IHnp1 env); destruct (IHnp2 env); try (
      left; simpl; eauto; fail
    ). right. simpl; intros [Hl | Hr]; eauto.
  + destruct (IHnp2 env); try (left; simpl; intros; eauto; fail).
    destruct (IHnp1 env).
    - right; simpl. intro Hc. destruct (H (Hc H0)).
    - left; simpl. intros. destruct (H0 H1).
  + destruct (IHnp env); eauto.
  + simpl. remember (env n0) as lim; clear Heqlim. induction lim.
    - left; intros. inv H.
    - specialize (IHnp (fun n0 => if Nat.eqb n0 n then lim else env n0)).
      destruct IHlim; destruct IHnp.
      * left; intros. inv H1; eauto.
      * right; intros Hc. apply H0; apply Hc; eauto.
      * right; intros Hc. apply H; intros. apply Hc; eauto.
      * right; intros Hc. apply H; intros. apply Hc; eauto.
  + simpl. remember (env n0) as lim; clear Heqlim. induction lim.
    - right; intros [y [Hy _]]. inv Hy.
    - specialize (IHnp (fun n0 => if Nat.eqb n0 n then lim else env n0)).
      destruct IHlim; destruct IHnp.
      * left. destruct H as [y [Hylt Heqy]]. exists y; split; eauto.
      * left. destruct H as [y [Hylt Heqy]]. exists y; split; eauto.
      * left. exists lim; eauto.
      * right. intros [y [Hylt Heqy]]. inv Hylt; eauto.
  + simpl.
    remember (nv_to_nat n env) as x. remember (nv_to_nat n0 env) as y.
    clear; destruct (Nat.eqb x y) eqn: EQ.
    - left. apply eqb_refl; eauto.
    - right. intros Hc. apply eqb_refl in Hc.
      rewrite Hc in EQ. inv EQ.
  + simpl.
    remember (nv_to_nat n env) as x. remember (nv_to_nat n0 env) as y.
    clear; destruct (Nat.leb x y) eqn: EQ.
    - left. apply leb_refl; eauto.
    - right. intros Hc. apply leb_refl in Hc.
      rewrite Hc in EQ. inv EQ.
Qed.

(* Subtask 2 *)

Theorem excluded_middle_square : 제곱수 는 극단적이야! .
Proof.
  (* FILL IN HERE *)
  intros x. unfold 제곱수.
  destruct (excluded_middle_np (
    Exists 2 1 (Eq (Mul (Var 2) (Var 2)) (Var 0))
  ) (fun n => match n with 0 => x | _ => S x end)); simpl in *;
  try destruct H as [y [Hylt Heqy]]; eauto.
  right. intros Hc. destruct Hc as [y Hy]. apply H; exists y; split; eauto.
  clear H. apply le_prog. subst. destruct y; eauto.
  replace (S y * S y) with (S y + y * S y) by simpl_arith.
  remember (S y) as x; remember (y * x) as z; clear.
  rewrite add_comm. induction z; simpl; eauto.
Qed.

(* Subtask 3 *)

Theorem excluded_middle_prime : 소수 는 극단적이야! .
Proof.
  (* FILL IN HERE *)
  intros x. unfold 소수. unfold divides.
  destruct (excluded_middle_np (
    And (Le (Var 2) (Var 0)) (Forall 1 0 (Implies (Le (Var 2) (Var 1)) (
      Not (Exists 3 0 (Eq (Var 0) (Mul (Var 1) (Var 3))))
    )))
  ) (fun n => match n with 0 => x | _ => 2 end)); simpl in *.
  + left. destruct H; split; eauto. intros x0 [Hx0gt Hx0lt].
    intros [x1 Heqx1]. specialize (H0 x0 Hx0lt Hx0gt). apply H0.
    exists x1; split; eauto. destruct x0; try destruct x0; try le_contra.
    destruct x1; try (subst; simpl_arith; inv Hx0lt; fail).
    subst. simpl_arith. repeat apply le_prog. clear.
    replace (x1 + x1 + x0 + x0 * x1) with (
      x1 + (x1 + x0 + x0 * x1)
    ) by simpl_arith. remember (x1 + x0 + x0 * x1) as z. clear.
    rewrite add_comm. induction z; simpl; eauto.
  + right. intros [Hxgt Heqx]. apply H. split; eauto. intros.
    specialize (Heqx y (conj H1 H0)). intros Hc. apply Heqx.
    destruct Hc as [y0 [Hy01 Hy02]]. eexists; eauto.
Qed.
