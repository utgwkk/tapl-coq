(* Chapter 8: Typed Arithmetic Expressions *)
Require Export UntypedArith.

Inductive ty :=
| Tbool : ty
| Tnat : ty
.

Inductive typed : term -> ty -> Prop :=
| T_True : typed ttrue Tbool
| T_False : typed tfalse Tbool
| T_If :
forall t1 t2 t3 T,
typed t1 Tbool -> typed t2 T -> typed t3 T
-> typed (tif t1 t2 t3) T
| T_Zero : typed tzero Tnat
| T_Succ : forall t1,
typed t1 Tnat -> typed (tsucc t1) Tnat
| T_Pred : forall t1,
typed t1 Tnat -> typed (tpred t1) Tnat
| T_IsZero : forall t1,
typed t1 Tnat -> typed (tiszero t1) Tbool
.

Notation "t |- T" := (typed t T) (at level 50).

Definition well_typed t :=
exists T, t |- T.

(* 8.2.3 Exercise *)
Lemma well_typed_subterm_succ :
forall t, well_typed (tsucc t) -> well_typed t.
Proof.
intros.
inversion H.
inversion H0; subst.
exists Tnat.
assumption.
Qed.

Lemma well_typed_subterm_pred :
forall t, well_typed (tpred t) -> well_typed t.
intros.
inversion H.
inversion H0; subst.
exists Tnat.
assumption.
Qed.

Lemma well_typed_subterm_iszero :
forall t, well_typed (tiszero t) -> well_typed t.
Proof.
intros.
inversion H.
inversion H0; subst.
exists Tnat.
assumption.
Qed.

Lemma well_typed_subterm_if :
forall t1 t2 t3,
well_typed (tif t1 t2 t3) ->
well_typed t1 /\ well_typed t2 /\ well_typed t3.
Proof.
intros.
inversion H.
inversion H0; subst.
split.
- exists Tbool.
  apply H4.
- split.
  + exists x.
    apply H6.
  + exists x.
    apply H7.
Qed.

(* Exercise 8.2.4 *)
Theorem uniq_types :
forall t T1 T2, t |- T1 -> t |- T2 -> T1 = T2.
Proof.
intro t.
induction t; intros.
- inversion H; subst.
  inversion H0; subst.
  reflexivity.
- inversion H; subst.
  inversion H0; subst.
  reflexivity.
- inversion H; subst.
  inversion H0; subst.
  reflexivity.
- inversion H; subst.
  inversion H0; subst.
  reflexivity.
- inversion H; subst.
  inversion H0; subst.
  reflexivity.
- inversion H; subst.
  inversion H0; subst.
  reflexivity.
- inversion H; subst.
  inversion H0; subst.
  apply IHt2.
  + apply H6.
  + apply H9.
Qed.

(* Lemma 8.3.1 *)
Lemma bool_value_is_true_or_false :
forall v,
value v -> v |- Tbool -> v = ttrue \/ v = tfalse.
Proof.
intros.
destruct H.
- inversion H; subst.
  + inversion H0.
  + inversion H0.
- destruct H.
  + left.
    reflexivity.
  + right.
    reflexivity.
Qed.

Lemma nat_value_is_zero_or_succ_nv :
forall v,
value v -> v |- Tnat ->
v = tzero \/ exists n, nv n /\ v = tsucc n.
Proof.
intros.
destruct H.
- destruct H.
  + left.
    reflexivity.
  + right.
    exists t.
    split.
    * assumption.
    * reflexivity.
- destruct H; inversion H0.
Qed.

Lemma nv_is_Tnat : forall t,
nv t -> t |- Tnat.
Proof.
intros.
induction H.
- apply T_Zero.
- apply T_Succ.
  apply IHnv.
Qed.

Lemma bv_is_Tbool : forall t,
bv t -> t |- Tbool.
Proof.
intros.
induction H.
- apply T_True.
- apply T_False.
Qed.

(* Theorem 8.3.2 *)
Theorem progress_reduction :
forall t, well_typed t ->
value t \/ exists t', t --> t'.
Proof.
intros.
destruct H.
induction H.
- left.
  right.
  apply BV_True.
- left.
  right.
  apply BV_False.
- right.
  destruct IHtyped1.
  + inversion H2.
    * inversion H3; subst.
      inversion H.
      inversion H.
    * inversion H3; subst.
      exists t2.
      apply E_IfTrue.
      exists t3.
      apply E_IfFalse.
  + destruct H2.
    exists (tif x t2 t3).
    apply E_If.
    apply H2.
- left.
  left.
  apply NV_Zero.
- destruct IHtyped.
  + inversion H0.
    * left.
      left.
      apply NV_Succ.
      apply H1.
    * inversion H1; subst; inversion H.
  + right.
    destruct H0.
    exists (tsucc x).
    apply E_Succ.
    apply H0.
- destruct IHtyped.
  + destruct H0.
    * inversion H0; subst.
      right.
      exists tzero.
      apply E_PredZero.
      right.
      exists t.
      apply E_PredSucc.
      apply H1.
    * inversion H0; subst; inversion H.
  + right.
    destruct H0.
    exists (tpred x).
    apply E_Pred.
    apply H0.
- destruct IHtyped.
  + destruct H0.
    * inversion H0; subst.
      right.
      exists ttrue.
      apply E_IsZeroZero.
      right.
      exists tfalse.
      apply E_IsZeroSucc.
      apply H1.
    * inversion H0; subst; inversion H.
  + right.
    destruct H0.
    exists (tiszero x).
    apply E_IsZero.
    apply H0.
Qed.

(* Theorem 8.3.3 *)
Theorem preserve_type :
forall t t' T, t |- T -> t --> t' -> t' |- T.
Proof.
intros.
generalize dependent t'.
induction H; intros.
- inversion H0.
- inversion H0.
- inversion H2; subst.
  + apply H0.
  + apply H1.
  + apply T_If.
    * apply IHtyped1.
      apply H7.
    * apply H0.
    * apply H1.
- inversion H0.
- inversion H0; subst.
  apply T_Succ.
  apply IHtyped.
  apply H2.
- inversion H0; subst.
  + apply T_Zero.
  + inversion H; subst.
    apply H3.
  + apply T_Pred.
    apply IHtyped.
    apply H2.
- inversion H0; subst.
  + apply T_True.
  + apply T_False.
  + apply T_IsZero.
    apply IHtyped.
    apply H2.
Qed.

(* Exercise 8.3.4 *)
Theorem preserve_type' :
forall t t' T, t |- T -> t --> t' -> t' |- T.
Proof.
intros.
generalize dependent T.
induction H0; intros.
- inversion H; subst.
  apply H5.
- inversion H; subst.
  apply H6.
- inversion H; subst.
  apply T_If.
  + apply IHeval.
    apply H4.
  + apply H6.
  + apply H7.
- inversion H; subst.
  apply T_Succ.
  apply IHeval.
  apply H2.
- inversion H; subst.
  apply T_Zero.
- inversion H0; subst.
  inversion H2; subst.
  apply H3.
- inversion H; subst.
  apply T_Pred.
  apply IHeval.
  apply H2.
- inversion H; subst.
  apply T_True.
- inversion H0; subst.
  apply T_False.
- inversion H; subst.
  apply T_IsZero.
  apply IHeval.
  apply H2.
Qed.

(* Exercise 8.3.6 *)
Theorem subject_expansion_counterex :
exists t t' T,
t --> t' -> t' |- T -> ~ t |- T.
Proof.
exists (tif ttrue tzero ttrue).
exists tzero.
exists Tnat.
intros.
intro.
inversion H1; subst.
inversion H8.
Qed.

(* Exercise 8.3.7 *)
Theorem preserve_big_eval :
forall t v T,
t |- T -> t ==> v -> v |- T.
Proof.
intros.
induction H0.
- apply H.
- inversion H; subst.
  apply IHbig_eval2.
  assumption.
- inversion H; subst.
  apply IHbig_eval2.
  assumption.
- inversion H; subst.
  apply T_Succ.
  apply IHbig_eval.
  assumption.
- inversion H; subst.
  apply T_Zero.
- inversion H; subst.
  apply nv_is_Tnat.
  apply H0.
- inversion H; subst.
  apply T_True.
- inversion H; subst.
  apply T_False.
Qed.

Theorem progress_big_eval :
forall t,
well_typed t -> exists v, t ==> v.
Proof.
intros.
destruct H.
induction H.
- exists ttrue.
  apply B_Value.
  right.
  apply BV_True.
- exists tfalse.
  apply B_Value.
  right.
  apply BV_False.
- destruct IHtyped1.
  assert (t1 ==> x). assumption.
  apply big_eval_to_value in H2.
  destruct H2.
  + apply preserve_big_eval with (v := x) in H.
    inversion H2; subst; inversion H.
    apply H3.
  + destruct H2.
    * destruct IHtyped2.
      exists x.
      apply B_IfTrue.
      apply big_eval_to_value in H2.
      apply H2.
      apply H3.
      apply H2.
    * destruct IHtyped3.
      exists x.
      apply B_IfFalse.
      apply big_eval_to_value in H2.
      apply H2.
      apply H3.
      apply H2.
- exists tzero.
  apply B_Value.
  left.
  apply NV_Zero.
- destruct IHtyped.
  exists (tsucc x).
  assert (t1 ==> x). assumption.
  apply preserve_big_eval with (T := Tnat) in H1.
  + apply B_Succ.
    apply big_eval_to_value in H0.
    inversion H0.
    * assumption.
    * inversion H2; subst; inversion H1.
    * assumption.
  + assumption.
- destruct IHtyped.
  assert (t1 ==> x). assumption.
  apply big_eval_to_value in H1.
  inversion H1.
  + inversion H2; subst.
    * exists tzero.
      apply B_PredZero.
      assumption.
    * exists t.
      apply B_PredSucc;
      assumption.
  + destruct H2.
    * apply preserve_big_eval with (v := ttrue) in H.
      inversion H.
      apply H0.
    * apply preserve_big_eval with (v := tfalse) in H.
      inversion H.
      apply H0.
- destruct IHtyped.
  assert (t1 ==> x). assumption.
  apply big_eval_to_value in H1.
  inversion H1.
  + inversion H2; subst.
    * exists ttrue.
      apply B_IsZeroZero.
      assumption.
    * exists tfalse.
      eapply B_IsZeroSucc.
      apply H3.
      assumption.
  + destruct H2.
    * apply preserve_big_eval with (v := ttrue) in H.
      inversion H.
      assumption.
    * apply preserve_big_eval with (v := tfalse) in H.
      inversion H.
      assumption.
Qed.

(* Exercise 8.3.8 *)
Module TypedArithWrong.
Require Export UntypedArithWrong.
Inductive ty :=
| Tbool : ty
| Tnat : ty
| Twrong : ty
.

Inductive typed : term -> ty -> Prop :=
| T_True : typed ttrue Tbool
| T_False : typed tfalse Tbool
| T_Wrong : typed twrong Twrong
| T_If :
forall t1 t2 t3 T,
typed t1 Tbool -> typed t2 T -> typed t3 T
-> typed (tif t1 t2 t3) T
| T_IfNat :
forall t1 t2 t3,
typed t1 Tnat -> typed (tif t1 t2 t3) Twrong
| T_IfWrong :
forall t1 t2 t3,
typed t1 Twrong -> typed (tif t1 t2 t3) Twrong
| T_Zero : typed tzero Tnat
| T_Succ : forall t1,
typed t1 Tnat -> typed (tsucc t1) Tnat
| T_SuccBool : forall t1,
typed t1 Tbool -> typed (tsucc t1) Twrong
| T_SuccWrong: forall t1,
typed t1 Twrong -> typed (tsucc t1) Twrong
| T_Pred : forall t1,
typed t1 Tnat -> typed (tpred t1) Tnat
| T_PredBool : forall t1,
typed t1 Tbool -> typed (tpred t1) Twrong
| T_PredWrong : forall t1,
typed t1 Twrong -> typed (tpred t1) Twrong
| T_IsZero : forall t1,
typed t1 Tnat -> typed (tiszero t1) Tbool
| T_IsZeroBool : forall t1,
typed t1 Tbool -> typed (tiszero t1) Twrong
| T_IsZeroWrong : forall t1,
typed t1 Twrong -> typed (tiszero t1) Twrong
.

Notation "t |- T" := (typed t T) (at level 50).

Definition well_typed t :=
exists T, t |- T.

Theorem progress_reduction :
forall t, well_typed t ->
value t \/ exists t', t -w-> t'.
Proof.
intros.
destruct H.
induction H.
- left.
  right.
  left.
  apply BV_True.
- left.
  right.
  left.
  apply BV_False.
- left.
  right.
  right.
  reflexivity.
- right.
  destruct IHtyped1.
  + destruct H2.
    * inversion H2; subst.
      inversion H.
      inversion H.
    * destruct H2.
      destruct H2.
      exists t2.
      apply E_IfTrue.
      exists t3.
      apply E_IfFalse.
      subst.
      exists twrong.
      apply E_IfWrong.
      apply BB_Wrong.
  + destruct H2.
    exists (tif x t2 t3).
    apply E_If.
    assumption.
- right.
  destruct IHtyped.
  + destruct H0.
    * exists twrong.
      apply E_IfWrong.
      apply BB_Nat.
      assumption.
    * destruct H0.
      destruct H0.
      exists t2.
      apply E_IfTrue.
      exists t3.
      apply E_IfFalse.
      subst.
      inversion H.
  + destruct H0.
    exists (tif x t2 t3).
    apply E_If.
    assumption.
- right.
  destruct IHtyped.
  + destruct H0.
    * exists twrong.
      apply E_IfWrong.
      apply BB_Nat.
      assumption.
    * destruct H0.
      destruct H0.
      inversion H.
      inversion H.
      subst.
      exists twrong.
      apply E_IfWrong.
      apply BB_Wrong.
  + destruct H0.
    exists (tif x t2 t3).
    apply E_If.
    assumption.
- left.
  left.
  apply NV_Zero.
- destruct IHtyped.
  + destruct H0.
    * left.
      left.
      apply NV_Succ.
      assumption.
    * destruct H0.
      right.
      exists twrong.
      apply E_SuccWrong.
      apply BN_Bool.
      assumption.
      subst.
      inversion H.
  + destruct H0.
    right.
    exists (tsucc x).
    apply E_Succ.
    assumption.
- destruct IHtyped.
  + destruct H0.
    destruct H0.
    inversion H.
    inversion H.
    destruct H0.
    * right.
      exists twrong.
      apply E_SuccWrong.
      apply BN_Bool.
      assumption.
    * subst.
      inversion H.
  + destruct H0.
    right.
    exists (tsucc x).
    apply E_Succ.
    assumption.
- destruct IHtyped.
  + destruct H0.
    left.
    left.
    apply NV_Succ.
    assumption.
    destruct H0.
    * destruct H0.
      inversion H.
      inversion H.
    * subst.
      right.
      exists twrong.
      apply E_SuccWrong.
      apply BN_Wrong.
  + right.
    destruct H0.
    exists (tsucc x).
    apply E_Succ.
    assumption.
- right.
  destruct IHtyped.
  + destruct H0.
    destruct H0.
    exists tzero.
    apply E_PredZero.
    exists t.
    apply E_PredSucc.
    assumption.
    destruct H0.
    * exists twrong.
      apply E_PredWrong.
      apply BN_Bool.
      assumption.
    * subst.
      inversion H.
  + destruct H0.
    exists (tpred x).
    apply E_Pred.
    assumption.
- right.
  destruct IHtyped.
  + destruct H0.
    * destruct H0;
      inversion H.
    * destruct H0.
      exists twrong.
      apply E_PredWrong.
      apply BN_Bool.
      assumption.
      subst.
      inversion H.
  + destruct H0.
    exists (tpred x).
    apply E_Pred.
    assumption.
- right.
  destruct IHtyped.
  + destruct H0.
    destruct H0.
    inversion H.
    exists t.
    apply E_PredSucc.
    assumption.
    destruct H0.
    * destruct H0;
      inversion H.
    * subst.
      exists twrong.
      apply E_PredWrong.
      apply BN_Wrong.
  + destruct H0.
    exists (tpred x).
    apply E_Pred.
    assumption.
- right.
  destruct IHtyped.
  + destruct H0.
    destruct H0.
    * exists ttrue.
      apply E_IsZeroZero.
    * exists tfalse.
      apply E_IsZeroSucc.
      assumption.
    * destruct H0.
      destruct H0;
      inversion H.
      subst.
      inversion H.
  + destruct H0.
    exists (tiszero x).
    apply E_IsZero.
    assumption.
- right.
  destruct IHtyped.
  + destruct H0.
    * destruct H0;
      inversion H.
    * destruct H0.
      exists twrong.
      apply E_IsZeroWrong.
      apply BN_Bool.
      assumption.
      subst.
      inversion H.
  + destruct H0.
    exists (tiszero x).
    apply E_IsZero.
    assumption.
- right.
  destruct IHtyped.
  + destruct H0.
    destruct H0.
    * inversion H.
    * exists tfalse.
      apply E_IsZeroSucc.
      assumption.
    * destruct H0.
      exists twrong.
      apply E_IsZeroWrong.
      apply BN_Bool.
      assumption.
      subst.
      exists twrong.
      apply E_IsZeroWrong.
      apply BN_Wrong.
  + destruct H0.
    exists (tiszero x).
    apply E_IsZero.
    assumption.
Qed.

Theorem preserve_type :
forall t T t',
t |- T -> t -w-> t' -> t' |- T.
Proof.
intros.
generalize dependent T.
induction H0; intros.
- inversion H; subst.
  + assumption.
  + inversion H4.
  + inversion H4.
- inversion H; subst.
  + assumption.
  + inversion H4.
  + inversion H4.
- inversion H; subst.
  + apply IHeval in H4.
    apply T_If; assumption.
  + apply T_IfNat.
    apply IHeval.
    assumption.
  + apply T_IfWrong.
    apply IHeval.
    assumption.
- inversion H; subst.
  + apply IHeval in H2.
    apply T_Succ.
    assumption.
  + apply T_SuccBool.
    apply IHeval.
    assumption.
  + apply T_SuccWrong.
    apply IHeval.
    assumption.
- inversion H; subst.
  + apply T_Zero.
  + inversion H1.
  + inversion H1.
- inversion H0; subst.
  + inversion H2; subst.
    assumption.
  + inversion H2.
  + inversion H; subst.
    inversion H2; subst.
    inversion H3.
    assumption.
    inversion H2; subst.
    inversion H4.
    assumption.
- inversion H; subst.
  + apply T_Pred.
    apply IHeval.
    assumption.
  + apply IHeval in H2.
    apply T_PredBool.
    assumption.
  + apply IHeval in H2.
    apply T_PredWrong.
    assumption.
- inversion H; subst.
  + apply T_True.
  + inversion H1.
  + inversion H1.
- inversion H0; subst.
  + apply T_False.
  + inversion H2.
  + induction H.
    * inversion H2.
      inversion H1.
      inversion H1.
    * apply IHnv.
      inversion H2; subst.
      apply T_IsZeroBool.
      assumption.
      apply T_IsZeroWrong.
      assumption.
      inversion H0; subst.
      inversion H3.
      inversion H3; subst.
      inversion H4.
      assumption.
- inversion H; subst.
  + apply T_IsZero.
    apply IHeval.
    assumption.
  + apply T_IsZeroBool.
    apply IHeval.
    assumption.
  + apply T_IsZeroWrong.
    apply IHeval.
    assumption.
- destruct H.
  + destruct H.
    * inversion H0; subst.
      inversion H3.
      apply T_Wrong.
      apply T_Wrong.
    * inversion H0; subst.
      inversion H4.
      apply T_Wrong.
      apply T_Wrong.
  + inversion H0; subst.
    * inversion H3.
    * inversion H4.
    * assumption.
- inversion H0; subst.
  + destruct H.
    * destruct H.
      inversion H2.
      inversion H2.
    * inversion H2.
  + apply T_Wrong.
  + apply T_Wrong.
- inversion H0; subst.
  + destruct H.
    * destruct H.
      inversion H2.
      inversion H2.
    * inversion H2.
  + apply T_Wrong.
  + apply T_Wrong.
- inversion H0; subst.
  + destruct H.
    * destruct H.
      inversion H2.
      inversion H2.
    * inversion H2.
  + apply T_Wrong.
  + apply T_Wrong.
Qed.

End TypedArithWrong.
