Require Export Ssreflect.ssreflect.
Require Export Ssreflect.ssrfun.
Require Export Ssreflect.ssrbool.
Require Export Ssreflect.eqtype.
Require Export Ssreflect.seq.
Require Export Ssreflect.ssrnat.
Require Export Ssreflect.fintype.

Lemma and_swap : forall x y z, [&& x, y & z] = [&& y, x & z].
Proof. by case; case; case. Qed.
