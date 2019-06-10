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
induction t.
- exists tnat.
  apply T_Zero.
- exists tbool.
  apply T_True.
- exists tbool.
  apply T_False.
- exists tnat.
  inversion H.
  inversion H0; subst.
  assumption.
- exists tnat.
  inversion H.
  inversion H0; subst.
  assumption.
- exists tbool.
  inversion H.
  inversion H0; subst.
  inversion H2.
- inversion H.
  exists x.
  inversion H0; subst.
  apply H2.
Qed.

Lemma well_typed_subterm_pred :
forall t, well_typed (tpred t) -> well_typed t.
Proof. Admitted.

Lemma well_typed_subterm_iszero :
forall t, well_typed (tiszero t) -> well_typed t.
Proof. Admitted.

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
