Require Export D.

(* Subtask 1 *)

Theorem double_negation_excluded_middle : 이중부정 -> 배중률.
Proof.
  (* FILL IN HERE *)
  intros NNPP P. apply NNPP. intros Hc.
  eassert (P -> False) by (intros HP; destruct (Hc (@or_introl P (~P) HP))).
  destruct (Hc (@or_intror P (~P) H)).
Qed.

(* Subtask 2 *)

Fixpoint is_square' (fuel : nat) (n : nat) (m : nat) (k : nat) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
    if Nat.ltb m n then
      is_square' fuel' n (S (2 * k + m)) (S k)
    else Nat.eqb n m
  end
.
Definition is_square (n : nat) : bool := is_square' (S n) n 0 0.

Lemma is_square'_trefl : forall fuel n m k,
  m = k * k -> is_square' fuel n m k = true -> n 이 제곱수이다.
Proof.
  intro fuel; induction fuel; intros.
  + inv H0.
  + unfold is_square' in H0. fold is_square' in H0.
    destruct (Nat.ltb m n) eqn: Hmn; reflection.
    - apply (IHfuel _ (S (2 * k + m)) (S k)); try assumption. simpl_arith.
    - subst m. exists k. congruence.
Qed.

Lemma is_square_trefl : forall n, is_square n = true -> n 이 제곱수이다.
Proof.
  intros. unfold is_square in H.
  apply is_square'_trefl in H; eauto.
Qed.

Lemma sq_inc' : forall n, n * n <= S n * S n.
Proof.
  intros. replace (S n * S n) with (S (n + n) + n * n) by simpl_arith.
  remember (n * n) as x. remember (S (n + n)) as y. clear.
  induction y; simpl; eauto.
Qed.

Lemma sq_inc : forall x y, x <= y -> x * x <= y * y.
Proof.
  intros x y; revert x. induction y; intros; inv H; eauto.
  apply (le_trans _ (y * y)).
  + apply IHy. assumption.
  + apply sq_inc'.
Qed.

Lemma is_square'_frefl : forall fuel n m k,
  fuel > n - m -> m = k * k
  -> is_square' fuel n m k = false -> forall x, x >= k -> x * x <> n.
Proof.
  intro fuel; induction fuel; intros.
  + inv H.
  + unfold is_square' in H1. fold is_square' in H1.
    destruct (Nat.ltb m n) eqn: Hmn; reflection.
    - inv H2; try (intro Hc; subst; le_contra).
      apply le_prog in H3. remember (S m0) as x; clear m0 Heqx.
      apply (IHfuel _ (S (2 * k + k * k)) (S k)); try assumption; try (
        simpl_arith; fail
      ). apply le_rev in H. apply (le_trans _ (n - k * k)); try assumption.
      remember (k * k) as y. remember (2 * k) as z. revert Hmn; clear; intros.
      destruct n; try (inv Hmn; fail).
      assert (minus_eq : forall x y, x <= y -> S y - x = S (y - x)). {
        clear; induction x; intros; try (induction y; simpl; eauto; fail).
        simpl. destruct y; try (inv H; eauto). apply IHx.
        apply le_S in H1. apply le_rev. assumption.
      } rewrite (minus_eq _ _ (le_rev _ _ Hmn)). apply le_prog. simpl.
      revert n y Hmn; induction z; intros; eauto. destruct n; eauto.
      inv Hmn.
      * replace (S n - S n) with 0 by (clear; induction n; eauto).
        replace (S n - (S z + S n)) with 0 by (
          clear; induction n; simpl_arith; eauto
        ). eauto.
      * replace (S n - (S z + y)) with (n - (z + y)) by eauto.
        rewrite (minus_eq _ _ (le_rev _ _ H0)).
        apply (le_trans _ (n - y)); try assumption; eauto.
    - intros Hc. apply sq_inc in H2. rewrite <- H0 in H2.
      rewrite Hc in H2. clear H0 Hc x k H. inv Hmn.
      * destruct (H1 eq_refl).
      * apply le_prog in H. remember (S m0) as m; clear Heqm m0. le_contra.
Qed.

Lemma is_sqaure_frefl : forall n, is_square n = false -> ~n 이 제곱수이다.
Proof.
  intros. unfold is_square in H.
  assert (n_Sn : S n > n - 0). {
    replace (n - 0) with n by (clear; induction n; eauto). eauto.
  } assert (FACT := is_square'_frefl (S n) n 0 0 n_Sn eq_refl H).
  intro Hc. destruct Hc as [x Heqx].
  eassert (x >= 0) by (clear; induction x; eauto). destruct (FACT x H0 Heqx).
Qed.

Theorem excluded_middle_square : 제곱수 는 극단적이야! .
Proof.
  (* FILL IN HERE *)
  intros x. destruct (is_square x) eqn: Heqx.
  + left. apply is_square_trefl; assumption.
  + right. apply is_sqaure_frefl; assumption.
Qed.

(* Subtask 3 *)

Fixpoint divides' (fuel : nat) (n : nat) (m : nat) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
    if Nat.ltb n m then match n with 0 => true | _ => false end
    else divides' fuel' (n - m) m
  end
.

Definition divides (n : nat) (m : nat) := divides' (S n) n m.

Lemma divides'_trefl : forall fuel n m,
  divides' fuel n m = true -> m 이 n 을 나눈다.
Proof.
  intro fuel; induction fuel; intros.
  + inv H.
  + simpl in H. destruct (Nat.ltb n m) eqn: Hnm; reflection.
    - destruct n; try (inv H; fail). exists 0; eauto.
    - apply IHfuel in H. destruct H as [x Heqx].
      assert (n = m * (S x)). {
        revert Hnm Heqx; clear; intros.
        assert (n - m + m = n). {
          clear x Heqx; revert m Hnm. induction n; intros.
          * inv Hnm. eauto.
          * destruct m; eauto. simpl. rewrite <- plus_n_Sm.
            apply le_rev in Hnm. rewrite (IHn _ Hnm). refl.
        } rewrite <- H. rewrite Heqx. rewrite add_comm. simpl_arith.
      } exists (S x); assumption.
Qed.

Lemma divides_trefl : forall n m, divides n m = true -> m 이 n 을 나눈다.
Proof.
  intros. eapply divides'_trefl; eassumption.
Qed.

Lemma divides'_frefl : forall fuel n m, m > 0 -> fuel > n ->
  divides' fuel n m = false -> ~m 이 n 을 나눈다.
Proof.
  intro fuel; induction fuel; intros.
  + inv H0.
  + simpl in H1. destruct (Nat.ltb n m) eqn: Hnm; reflection.
    - destruct n; inv H1. intro Hc.
      destruct Hc as [x Heqx]. destruct x; simpl_arith; try (inv Heqx; fail).
      rewrite Heqx in Hnm. unfold lt in Hnm.
      replace (S (m + m * x)) with (m + S (m * x)) in Hnm by simpl_arith.
      rewrite add_comm in Hnm; le_contra.
    - intro Hc. destruct Hc as [x Heqx]. destruct x.
      * simpl_arith. subst n. inv Hnm. inv H.
      * assert (m 이 n - m 을 나눈다). {
          exists x. subst. simpl_arith. rewrite add_comm.
          remember (m * x) as y; clear. revert y. induction m; intros;
          simpl_arith; induction y; eauto.
        } apply IHfuel in H2; try assumption; try (destruct (Heqx H2); fail).
        destruct m; try (inv H; fail). revert H0 Hnm; clear; intros.
        destruct n; try (inv Hnm; fail). simpl. apply le_rev in H0.
        clear Hnm. apply (le_trans _ (S n)); try assumption. apply le_prog.
        clear. revert n; induction m; intros; induction n; eauto.
Qed.

Lemma divides_frefl : forall n m, m > 0 ->
  divides n m = false -> ~m 이 n 을 나눈다.
Proof.
  intros. eapply divides'_frefl; try eassumption; eauto.
Qed.

Fixpoint is_prime' (n : nat) (m : nat) :=
  match m with
  | 0 => false
  | S m' => match m' with
    | 0 => true
    | S _ => if divides n m then false else is_prime' n m'
    end
  end
.

Definition is_prime (n : nat) :=
  match n with
  | 0 => false
  | S n' => is_prime' n n'
  end
.

Lemma is_prime'_trefl : forall n m,
  is_prime' n m = true -> forall x, 1 < x <= m -> ~x 가 n 을 나눈다.
Proof.
  intros n m; revert n. induction m; intros.
  + destruct H0; le_contra.
  + simpl in H. destruct m.
    - destruct H0; le_contra.
    - destruct (divides n (S (S m))) eqn: HnSSm; try (inv H; fail).
      destruct H0. inv H1.
      * apply divides_frefl; try assumption. clear; induction m; eauto.
      * apply IHm; try assumption. split; assumption.
Qed.

Lemma is_prime_trefl : forall n, is_prime n = true -> n 이 소수이다.
Proof.
  intros. unfold is_prime in H.
  destruct n; try destruct n.
  + inv H.
  + inv H.
  + split.
    - clear; induction n; eauto.
    - intros. apply (is_prime'_trefl _ (S n)); try assumption.
      destruct H0. split; try assumption. apply le_rev; assumption.
Qed.

Lemma is_prime'_frefl : forall n m,
  1 < m < n -> is_prime' n m = false -> ~n 이 소수이다.
Proof.
  intros n m; revert n. induction m; intros; destruct H; try le_contra.
  simpl in H0. destruct m; try le_contra.
  destruct (divides n (S (S m))) eqn: HnSSm.
  + apply divides_trefl in HnSSm. destruct HnSSm. intro Hc.
    unfold 소수 in Hc. destruct Hc as [_ Hc].
    specialize (Hc (S (S m)) (conj H H1)). apply Hc. eexists; eauto.
  + destruct m; try (inv H0; fail). apply IHm; try split.
    - clear. induction m; eauto.
    - eapply le_trans; try eassumption; eauto.
    - assumption.
Qed.

Lemma is_prime_frefl : forall n, is_prime n = false -> ~n 이 소수이다.
Proof.
  intros. unfold is_prime in H.
  destruct n; try destruct n.
  + clear. intro Hc. destruct Hc as [Hc _]. le_contra.
  + clear. intro Hc. destruct Hc as [Hc _]. le_contra.
  + eapply is_prime'_frefl; try eassumption; split; eauto.
    destruct n.
    - inv H.
    - clear; induction n; eauto.
Qed.

Theorem excluded_middle_prime : 소수 는 극단적이야! .
Proof.
  (* FILL IN HERE *)
  intros n. destruct (is_prime n) eqn: EQ.
  + left. apply is_prime_trefl; assumption.
  + right. apply is_prime_frefl; assumption.
Qed.
