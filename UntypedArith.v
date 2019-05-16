Definition relation (X:Type) := X -> X -> Prop.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
~ exists t', R t t'.

Inductive term : Type :=
| tzero : term
| ttrue : term
| tfalse : term
| tsucc : term -> term
| tpred : term -> term
| tiszero : term -> term
| tif : term -> term -> term -> term
.

Inductive bv : term -> Prop :=
| BV_True : bv ttrue
| BV_False : bv tfalse
.

Inductive nv : term -> Prop :=
| NV_Zero : nv tzero
| NV_Succ : forall (t : term), nv t -> nv (tsucc t)
.

Inductive eval : term -> term -> Prop :=
| E_IfTrue : forall (t2 t3 : term),
eval (tif ttrue t2 t3) t2
| E_IfFalse : forall (t2 t3 : term),
eval (tif tfalse t2 t3) t3
| E_If : forall (t1 t1' t2 t3 : term),
eval t1 t1'
-> eval (tif t1 t2 t3) (tif t1' t2 t3)
| E_Succ : forall (t1 t1' : term),
eval t1 t1' -> eval (tsucc t1) (tsucc t1')
| E_PredZero : eval (tpred tzero) tzero
| E_PredSucc : forall t,
nv t -> eval (tpred (tsucc t)) t
| E_Pred : forall t1 t1',
eval t1 t1' -> eval (tpred t1) (tpred t1')
| E_IsZeroZero : eval (tiszero tzero) ttrue
| E_IsZeroSucc : forall t,
nv t -> eval (tiszero (tsucc t)) tfalse
| E_IsZero : forall t1 t1',
eval t1 t1'
-> eval (tiszero t1) (tiszero t1')
.

Notation "t1 --> t2" := (eval t1 t2) (at level 60).

Lemma bv_is_nf : forall t,
bv t -> normal_form eval t.
Proof.
intros. unfold normal_form. unfold not.
induction H; intros; inversion H; inversion H0.
Qed.

Lemma nv_is_nf : forall t,
nv t -> normal_form eval t.
Proof.
intros. unfold normal_form. unfold not.
induction H.
- intros. inversion H. inversion H0.
- intros. destruct H0. destruct IHnv.
  inversion H0; subst. exists t1'. apply H2.
Qed.

(* 3.5.7 *)
Theorem value_is_nf : forall t,
nv t \/ bv t -> normal_form eval t.
Proof.
intros. destruct H.
- apply nv_is_nf. apply H.
- apply bv_is_nf. apply H.
Qed.

Lemma nv_succ_nv : forall t,
nv (tsucc t) -> nv t.
Proof.
intros. destruct t.
- apply NV_Zero.
- inversion H; subst. inversion H1.
- inversion H; subst. apply H1.
- inversion H; subst. apply H1.
- inversion H; subst. apply H1.
- inversion H; subst. apply H1.
- inversion H; subst. apply H1.
Qed.

Lemma value_is_disjoint : forall t,
~ (nv t /\ bv t).
Proof.
unfold not. intros.
destruct H.
inversion H; subst. inversion H0. inversion H0.
Qed.

(* 3.5.4, 3.5.14 *)
Theorem eval_deterministic : forall t t' t'',
t --> t' -> t --> t'' -> t' = t''.
Proof.
intros.
generalize dependent t''.
induction H; intros; inversion H0; subst.
- reflexivity.
- inversion H4.
- reflexivity.
- inversion H4.
- inversion H.
- inversion H.
- apply IHeval in H5. rewrite -> H5. reflexivity.
- apply IHeval in H2. rewrite -> H2. reflexivity.
- reflexivity.
- inversion H1.
- reflexivity.
- apply NV_Succ in H. apply nv_is_nf with (t := tsucc t) in H. unfold normal_form in H. unfold not in H. destruct H.
  exists t1'. apply H2.
- inversion H.
- apply NV_Succ in H2. apply nv_is_nf with (t := tsucc t'') in H2. unfold normal_form in H2. unfold not in H2. destruct H2.
  exists t1'. apply H.
- apply IHeval in H2. rewrite -> H2. reflexivity.
- reflexivity.
- inversion H1.
- reflexivity.
- apply NV_Succ in H. apply nv_is_nf with (t := tsucc t) in H. unfold normal_form in H. unfold not in H. destruct H.
  exists t1'. apply H2.
- inversion H.
- apply NV_Succ in H2. apply nv_is_nf with (t := tsucc t) in H2. unfold normal_form in H2. unfold not in H2. destruct H2.
  exists t1'. apply H.
- apply IHeval in H2. rewrite -> H2. reflexivity.
Qed.

Inductive meval : term -> term -> Prop :=
| ME_Eval : forall t1 t2, eval t1 t2 -> meval t1 t2
| ME_Refl : forall t1, meval t1 t1
| ME_Trans : forall t1 t2 t3,
meval t1 t2 -> meval t2 t3 -> meval t1 t3
.

Notation "t1 -->* t2" := (meval t1 t2) (at level 60).

Inductive meval' : term -> term -> Prop :=
| ME'_Eval : forall t1 t2, eval t1 t2 -> meval' t1 t2
| ME'_Refl : forall t1, meval' t1 t1
| ME'_OneMany : forall t1 t2 t3,
eval t1 t2 -> meval' t2 t3 -> meval' t1 t3
.

Definition transitive {X:Type} (R:relation X) : Prop :=
forall x y z, R x y -> R y z -> R x z.

Notation "t1 ~~>* t2" := (meval' t1 t2) (at level 60).

Lemma meval'_transitive : transitive meval'.
Proof.
unfold transitive. intros.
induction H.
- apply ME'_OneMany with (t1 := t1) in H0. apply H0. apply H.
- apply H0.
- apply IHmeval' in H0. apply ME'_OneMany with (t1 := t1) in H0.
  apply H0. apply H.
Qed.

Lemma meval_iff_meval' : forall t1 t2,
t1 ~~>* t2 <-> t1 -->* t2.
Proof.
intros. split.
- intros. induction H.
  + apply ME_Eval in H. apply H.
  + apply ME_Refl.
  + apply ME_Eval in H. apply ME_Trans with (t1 := t1) in IHmeval'. apply IHmeval'. apply H.
- intros. induction H; subst.
  + apply ME'_Eval in H. apply H.
  + apply ME'_Refl.
  + apply meval'_transitive with (y := t2). apply IHmeval1. apply IHmeval2.
Qed.

Theorem meval_deterministic : forall t1 t2 t3,
t1 -->* t2 -> t1 -->* t3 -> normal_form eval t2 -> normal_form eval t3 -> t2 = t3.
Proof.
intros.
apply meval_iff_meval' in H.
apply meval_iff_meval' in H0.
induction H.
- induction H0.
  + apply eval_deterministic with (t := t1).
    apply H. apply H0.
  + destruct H2. exists t2. apply H.
  + induction H3.
    * apply eval_deterministic with (t' := t0) in H.
      rewrite -> H in H3. destruct H1. exists t3. apply H3. apply H0.
    * apply eval_deterministic with (t := t1). apply H. apply H0.
    * apply eval_deterministic with (t' := t0) in H. rewrite <- H in H1.
      destruct H1. exists t3. apply H3. apply H0.
- induction H0.
  + destruct H1. exists t2. apply H.
  + reflexivity.
  + destruct H1. exists t2. apply H.
- induction H0.
  + apply eval_deterministic with (t' := t2) in H0.
    rewrite -> H0 in IHmeval'. destruct IHmeval'. apply ME'_Refl. apply H1. reflexivity. apply H.
  + destruct H2. exists t2. apply H.
  + apply eval_deterministic with (t' := t2) in H0.
    rewrite -> H0 in IHmeval'. destruct IHmeval'.
    apply H4. apply H1. reflexivity. apply H.
Qed.

Lemma meval_subterm_num : forall t1 t2,
t1 -->* t2 -> tsucc t1 -->* tsucc t2 /\ tpred t1 -->* tpred t2 /\ tiszero t1 -->* tiszero t2.
Proof.
intros. split.
- induction H.
  + apply ME_Eval. apply E_Succ. apply H.
  + apply ME_Refl.
  + apply ME_Trans with (t1 := tsucc t1) in IHmeval2. apply IHmeval2. apply IHmeval1.
- split.
  + induction H.
    * apply ME_Eval. apply E_Pred. apply H.
    * apply ME_Refl.
    * apply ME_Trans with (t1 := tpred t1) in IHmeval2. apply IHmeval2. apply IHmeval1.
  + induction H.
    * apply ME_Eval. apply E_IsZero. apply H.
    * apply ME_Refl.
    * apply ME_Trans with (t2 := tiszero t2). apply IHmeval1. apply IHmeval2.
Qed.

Lemma meval_subterm_if : forall t1 t1' t2 t3,
t1 -->* t1' -> tif t1 t2 t3 -->* tif t1' t2 t3.
Proof.
intros. induction H.
- apply ME_Eval. apply E_If. apply H.
- apply ME_Refl.
- apply ME_Trans with (t2 := tif t0 t2 t3).
  apply IHmeval1. apply IHmeval2.
Qed.

Definition stuck t := normal_form eval t /\ ~ (nv t \/ bv t).

Fact stuck_term : exists t, stuck t.
Proof.
exists (tsucc ttrue).
unfold stuck. split.
- unfold normal_form. unfold not. intros.
  destruct H.
  inversion H; subst. inversion H1.
- unfold not. intros.
  destruct H.
  + inversion H; subst. inversion H1.
  + inversion H.
Qed.