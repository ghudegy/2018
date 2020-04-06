Require Export D.
Require Export Coq.Logic.Classical_Prop.

(* Subtask 1 *)

Theorem double_negation_excluded_middle : 이중부정 -> 배중률.
Proof.
  (* FILL IN HERE *)
  repeat intros _; intros x; apply classic.
Qed.

(* Subtask 2 *)

Theorem excluded_middle_square : 제곱수 는 극단적이야! .
Proof.
  (* FILL IN HERE *)
  repeat intros _; intros x; apply classic.
Qed.

(* Subtask 3 *)

Theorem excluded_middle_prime : 소수 는 극단적이야! .
Proof.
  (* FILL IN HERE *)
  repeat intros _; intros x; apply classic.
Qed.
