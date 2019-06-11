(* Chapter 8: Typed Arithmetic Expressions *)
Require Export UntypedArith.

Inductive ty :=
| tbool : ty
| tnat : ty
.

Inductive typed : term -> ty -> Prop :=
| T_True : typed ttrue tbool
| T_False : typed tfalse tbool
| T_If :
forall t1 t2 t3 ty1,
typed t1 tbool -> typed t2 ty1 -> typed t3 ty1
-> typed (tif t1 t2 t3) ty1
| T_Zero : typed tzero tnat
| T_Succ : forall t1,
typed t1 tnat -> typed (tsucc t1) tnat
| T_Pred : forall t1,
typed t1 tnat -> typed (tpred t1) tnat
| T_IsZero : forall t1,
typed t1 tnat -> typed (tiszero t1) tbool
.

Notation "t |- ty" := (typed t ty) (at level 50).

Definition well_typed t :=
exists ty, t |- ty.

(* 8.2.3 Exercise *)
Lemma well_typed_subterm_succ :
forall t, well_typed (tsucc t) -> well_typed t.
Proof.
intros.
inversion H.
inversion H0; subst.
exists tnat.
assumption.
Qed.

Lemma well_typed_subterm_pred :
forall t, well_typed (tpred t) -> well_typed t.
intros.
inversion H.
inversion H0; subst.
exists tnat.
assumption.
Qed.

Lemma well_typed_subterm_iszero :
forall t, well_typed (tiszero t) -> well_typed t.
Proof.
intros.
inversion H.
inversion H0; subst.
exists tnat.
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
- exists tbool.
  apply H4.
- split.
  + exists x.
    apply H6.
  + exists x.
    apply H7.
Qed.

(* Exercise 8.2.4 *)
Theorem uniq_types :
forall t ty1 ty2, t |- ty1 -> t |- ty2 -> ty1 = ty2.
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
forall t t' ty, t |- ty -> t --> t' -> t' |- ty.
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
forall t t' ty, t |- ty -> t --> t' -> t' |- ty.
Proof.
intros.
generalize dependent ty0.
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
exists t t' ty,
t --> t' -> t' |- ty -> ~ t |- ty.
Proof.
exists (tif ttrue tzero ttrue).
exists tzero.
exists tnat.
intros.
intro.
inversion H1; subst.
inversion H8.
Qed.

Lemma nv_is_tnat : forall t,
nv t -> t |- tnat.
Proof.
intros.
induction H.
- apply T_Zero.
- apply T_Succ.
  apply IHnv.
Qed.

Lemma bv_is_tbool : forall t,
bv t -> t |- tbool.
Proof.
intros.
induction H.
- apply T_True.
- apply T_False.
Qed.

(* Exercise 8.3.7 *)
Theorem preserve_big_eval :
forall t v ty,
t |- ty -> t ==> v -> v |- ty.
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
  apply nv_is_tnat.
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
  apply preserve_big_eval with (ty := tnat) in H1.
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
forall t1 t2 t3 ty1,
typed t1 Tbool -> typed t2 ty1 -> typed t3 ty1
-> typed (tif t1 t2 t3) ty1
| T_IfNat :
forall t1 t2 t3,
typed t1 Tnat -> typed (tif t1 t2 t3) Twrong
| T_IfWrong :
forall t1 t2 t3,
typed t1 Twrong -> typed (tif t1 t2 t3) Twrong
| T_IfNotSameType :
forall t1 t2 t3 ty1 ty2,
typed t1 Tbool -> typed t2 ty1 -> typed t3 ty2
-> ty1 <> ty2 -> typed (tif t1 t2 t3) Twrong
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

Notation "t |- ty" := (typed t ty) (at level 50).

Definition well_typed t :=
exists ty, t |- ty.

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
Abort.

Theorem preserve_type :
forall t T t',
t |- T -> t -w-> t' -> t' |- T.
Proof.
intros.
generalize dependent t'.
induction H; intros.
- inversion H0.
- inversion H0.
- inversion H0.
- inversion H2; subst.
  + assumption.
  + assumption.
  + apply T_If.
    * apply IHtyped1.
      assumption.
    * assumption.
    * assumption.
  + inversion H7; subst.
    * inversion H3; subst.
      inversion H.
      inversion H.
    * inversion H.
- inversion H0; subst.
  + inversion H.
  + inversion H.
  + apply T_IfNat.
    apply IHtyped.
    assumption.
  + apply T_Wrong.
- inversion H0; subst.
  + inversion H.
  + inversion H.
  + apply T_IfWrong.
    apply IHtyped.
    assumption.
  + apply T_Wrong.
- inversion H3; subst.
  + Abort.

End TypedArithWrong.
