Require Export ReductionSystem.

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

Definition value t := nv t \/ bv t.

(* 3.5.7 *)
Theorem value_is_nf : forall t,
value t -> normal_form eval t.
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

Definition deterministic {X:Type} (R:relation X) :=
forall x y z, R x y -> R x z -> y = z.

(* 3.5.4, 3.5.14 *)
Theorem eval_deterministic :
forall t t' t'', t --> t' -> t --> t'' -> t' = t''.
Proof.
unfold deterministic.
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
- apply NV_Succ in H. apply nv_is_nf with (t := tsucc t) in H.
  unfold normal_form in H. unfold not in H. destruct H.
  exists t1'. apply H2.
- inversion H.
- apply NV_Succ in H2. apply nv_is_nf with (t := tsucc t'') in H2.
  unfold normal_form in H2. unfold not in H2. destruct H2.
  exists t1'. apply H.
- apply IHeval in H2. rewrite -> H2. reflexivity.
- reflexivity.
- inversion H1.
- reflexivity.
- apply NV_Succ in H. apply nv_is_nf with (t := tsucc t) in H.
  unfold normal_form in H. unfold not in H. destruct H.
  exists t1'. apply H2.
- inversion H.
- apply NV_Succ in H2. apply nv_is_nf with (t := tsucc t) in H2.
  unfold normal_form in H2. unfold not in H2. destruct H2.
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

(* 3.5.11 *)
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
    * apply eval_deterministic with (t' := t2) in H0.
      rewrite <- H0 in H3.
      destruct H1. exists t3. apply H3. apply H.
    * apply eval_deterministic with (t' := t0) in H. symmetry. apply H. apply H0.
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

Fixpoint size (t : term) : nat :=
match t with
| tzero => 1
| ttrue => 1
| tfalse => 1
| tsucc t => 1 + size t
| tpred t => 1 + size t
| tiszero t => 1 + size t
| tif t1 t2 t3 => 1 + size t1 + size t2 + size t3
end.

Require Import Coq.omega.Omega.

Lemma eval_decrease_size : forall t t',
t --> t' -> size t > size t'.
Proof.
intros.
induction H; simpl; omega.
Qed.

Lemma meval_decrease_size : forall t t',
t -->* t' -> size t >= size t'.
Proof.
intros. induction H.
- apply eval_decrease_size in H. omega.
- omega.
- omega.
Qed.

(* 3.5.12 *)
Theorem eval_termination :
forall t, exists t', (normal_form eval t' /\ t -->* t').
Proof.
intros. induction t.
- exists tzero. split.
  + intro. destruct H. inversion H.
  + apply ME_Refl.
- exists ttrue. split.
  + intro. destruct H. inversion H.
  + apply ME_Refl.
- exists tfalse. split.
  + intro. destruct H. inversion H.
  + apply ME_Refl.
- destruct IHt. destruct H.
  exists (tsucc x). split.
  + intro. destruct H1. inversion H1; subst.
    destruct H. exists t1'. assumption.
  + apply meval_subterm_num. assumption.
- destruct IHt. destruct H.
  destruct x.
  + exists tzero. split.
    assumption.
    apply meval_subterm_num in H0.
    destruct H0. destruct H1.
    apply ME_Trans with (t2 := tpred tzero).
    apply H1. apply ME_Eval. apply E_PredZero.
  + exists (tpred ttrue). split.
    intro. destruct H1. inversion H1; subst. inversion H3.
    apply meval_subterm_num in H0.
    destruct H0. destruct H1. apply H1.
  + exists (tpred tfalse). split.
    intro. destruct H1. inversion H1; subst. inversion H3.
    apply meval_subterm_num in H0.
    destruct H0. destruct H1. apply H1.
  + exists x. split.
    intro. destruct H1. destruct H.
    exists (tsucc x0). apply E_Succ. assumption.
    Abort.

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

Lemma nonvalue_nf_is_stuck : forall t, normal_form eval t -> ~ (nv t \/ bv t) -> stuck t.
Proof.
  intros.
  unfold stuck. split.
  - apply H.
  - apply H0.
Qed.

Lemma stuck_subterm_succ : forall t,
    stuck t -> stuck (tsucc t).
Proof.
  intros.
  unfold stuck.
  induction t.
  - split.
    + intro. destruct H0.
      inversion H0; subst.
      inversion H2.
    + intro. destruct H0.
      * destruct H. destruct H1.
        left. apply NV_Zero.
      * inversion H0.
  - split.
    + intro. destruct H0.
      inversion H0; subst.
      inversion H2.
    + intro. destruct H0.
      * inversion H0; subst. inversion H2.
      * inversion H0.
  - split.
    + intro. destruct H0.
      inversion H0; subst.
      inversion H2.
    + intro. destruct H0.
      inversion H0; subst.
      * inversion H2.
      * inversion H0.
  - split.
    + intro. destruct H0.
      inversion H0; subst.
      inversion H2; subst.
      destruct H. destruct H.
      exists (tsucc t1'0). apply H2.
    + intro. destruct H0.
      * inversion H0; subst.
        inversion H. destruct H3.
        left. apply H2.
      * inversion H0.
  - split.
    + intro. destruct H0.
      inversion H0; subst.
      destruct H. destruct H.
      exists t1'. apply H2.
    + intro. destruct H0.
      * inversion H0; subst. inversion H2.
      * inversion H0.
  - split.
    + intro. destruct H0.
      inversion H0; subst.
      destruct H. destruct H.
      exists t1'. apply H2.
    + intro. destruct H0.
      * inversion H0; subst. inversion H2.
      * inversion H0.
  - split.
    + intro. destruct H0.
      inversion H0; subst.
      destruct H. destruct H.
      exists t1'. apply H2.
    + intro. destruct H0.
      * inversion H0; subst. inversion H2.
      * inversion H0.
Qed.

Lemma stuck_succ : forall t,
stuck (tsucc t) -> stuck t.
Proof.
  intros.
  induction (tsucc t).
  - inversion H. destruct H1.
    left. apply NV_Zero.
  - inversion H. destruct H1.
    right. apply BV_True.
  - inversion H. destruct H1.
    right. apply BV_False.
  - destruct H.
    apply IHt0. apply nonvalue_nf_is_stuck.
    Abort.

Lemma stuck_subterm_iszero : forall t,
    stuck t -> stuck (tiszero t).
intros.
induction t.
  - unfold stuck. split.
    * unfold normal_form. unfold not. intro.
      destruct H0. inversion H0; subst.
      inversion H. unfold not in H2. destruct H2.
      left. apply NV_Zero. inversion H2.
    * unfold not. intro.
      destruct H0.
      inversion H. unfold not in H2.
      destruct H2.
      left. apply NV_Zero. inversion H0.
  - unfold stuck. split.
    * unfold stuck in H. destruct H.
      unfold normal_form. unfold not. intro.
      destruct H1. inversion H1; subst.
      inversion H3.
    * unfold not. intro.
      destruct H0.
      inversion H0; subst. inversion H0.
  - unfold stuck. split.
    * unfold normal_form. unfold not. intro.
      destruct H0. inversion H0; subst.
      inversion H2.
    * unfold not. intro.
      destruct H0.
      inversion H0; subst. destruct H0.
      inversion H. destruct H1. right. apply BV_False.
      inversion H. destruct H1. right. apply BV_False.
  - unfold stuck. split.
    * unfold normal_form. unfold not. intro.
      destruct H0. inversion H0; subst.
      unfold stuck in H. destruct H.
      unfold normal_form in H. unfold not in H.
      destruct H.
      destruct H1. left. apply NV_Succ. apply H2.
      inversion H2; subst. unfold stuck in H. destruct H.
      destruct H.
      exists (tsucc t1'0). apply H2.
    * unfold not. intro.
      destruct H0.
      inversion H0; subst.
      unfold stuck in H. destruct H.
      unfold not in H1.
      destruct H1. left. inversion H0.
  - unfold stuck. split.
    * unfold normal_form. unfold not. intro.
      destruct H0. inversion H0; subst.
      unfold stuck in H. destruct H.
      unfold normal_form in H. unfold not in H.
      destruct H.
      exists t1'. apply H2.
    * unfold not. intro.
      destruct H0.
      inversion H0; subst.
      unfold stuck in H. destruct H.
      unfold not in H1.
      destruct H1. left. destruct H. inversion H0.
  - unfold stuck. split.
    * unfold normal_form. unfold not. intro.
      destruct H0. inversion H0; subst.
      unfold stuck in H. destruct H.
      unfold normal_form in H. unfold not in H.
      destruct H.
      exists t1'. apply H2.
    * unfold not. intro.
      destruct H0.
      inversion H0; subst.
      unfold stuck in H. destruct H.
      unfold not in H1.
      destruct H1. right. inversion H0.
  - unfold stuck. split.
    * unfold normal_form. unfold not. intro.
      destruct H0. inversion H0; subst.
      unfold stuck in H. destruct H.
      unfold normal_form in H. unfold not in H.
      destruct H.
      exists t1'. apply H2.
    * unfold not. intro.
      destruct H0.
      inversion H0; subst.
      unfold stuck in H. destruct H.
      unfold not in H1.
      destruct H1. left. inversion H0.
Qed.

Lemma stuck_subterm_pred : forall t,
    stuck t -> stuck (tpred t).
Proof.
intros.
induction t.
  - unfold stuck. split.
    * unfold normal_form. unfold not. intro.
      destruct H0. inversion H0; subst.
      inversion H. destruct H2.
      left. apply NV_Zero. inversion H2.
    * unfold not. intro.
      destruct H0.
      inversion H. unfold not in H2.
      destruct H2.
      left. apply NV_Zero. inversion H0.
  - unfold stuck. split.
    * unfold stuck in H. destruct H.
      unfold normal_form. unfold not. intro.
      destruct H1. inversion H1; subst.
      inversion H3.
    * unfold not. intro.
      destruct H0.
      inversion H0; subst. destruct H0.
      inversion H. destruct H1. right. apply BV_True.
      inversion H. destruct H1. right. apply BV_True.
  - unfold stuck. split.
    * unfold normal_form. unfold not. intro.
      destruct H0. inversion H0; subst.
      inversion H2.
    * unfold not. intro.
      destruct H0.
      inversion H0; subst. inversion H0.
  - unfold stuck. split.
    * unfold normal_form. unfold not. intro.
      destruct H0. inversion H0; subst.
      unfold stuck in H. destruct H.
      unfold normal_form in H. unfold not in H.
      destruct H.
      destruct H1.
      left. apply NV_Succ. apply H2.
      destruct H. destruct H.
      exists t1'. apply H2.
    * unfold not. intro.
      destruct H0.
      inversion H0; subst.
      unfold stuck in H. destruct H.
      unfold not in H1.
      destruct H1. left. inversion H0.
  - unfold stuck. split.
    * unfold normal_form. unfold not. intro.
      destruct H0. inversion H0; subst.
      unfold stuck in H. destruct H.
      unfold normal_form in H. unfold not in H.
      destruct H.
      exists t1'. apply H2.
    * unfold not. intro.
      destruct H0.
      inversion H0; subst.
      unfold stuck in H. destruct H.
      unfold not in H1.
      destruct H1. left. destruct H.
      inversion H0.
  - unfold stuck. split.
    * unfold normal_form. unfold not. intro.
      destruct H0. inversion H0; subst.
      unfold stuck in H. destruct H.
      unfold normal_form in H. unfold not in H.
      destruct H.
      exists t1'. apply H2.
    * unfold not. intro.
      destruct H0.
      inversion H0; subst.
      inversion H0.
  - unfold stuck. split.
    * unfold normal_form. unfold not. intro.
      destruct H0. inversion H0; subst.
      unfold stuck in H. destruct H.
      unfold normal_form in H. unfold not in H.
      destruct H.
      exists t1'. apply H2.
    * unfold not. intro.
      destruct H0; inversion H0.
Qed.

Lemma stuck_subterm_if : forall t1 t2 t3,
    stuck t1 -> stuck (tif t1 t2 t3).
Proof.
  intros. induction t1; unfold stuck.
  - split.
    + inversion H. destruct H1.
      left. apply NV_Zero.
    + unfold not. intros.
      destruct H0.
      * inversion H0.
      * inversion H0.
  - split.
    + inversion H. destruct H1.
      right. apply BV_True.
    + unfold not. intros.
      destruct H0.
      * inversion H0.
      * inversion H0.
  - split.
    + inversion H. destruct H1.
      right. apply BV_False.
    + inversion H. destruct H1.
      right. apply BV_False.
  - split.
    + unfold normal_form. unfold not. intro.
      destruct H0. inversion H0; subst.
      inversion H; subst. destruct H1. exists t1'. apply H5.
    + unfold not. intro. destruct H0; inversion H0.
  - split.
    + unfold normal_form. unfold not. intro.
      destruct H0. inversion H0; subst.
      inversion H; subst. destruct H1. exists t1'. apply H5.
    + unfold not. intro. destruct H0; inversion H0.
  - split.
    + unfold normal_form. unfold not. intro.
      destruct H0. inversion H0; subst.
      inversion H; subst. destruct H1. exists t1'. apply H5.
    + unfold not. intro. destruct H0; inversion H0.
  - split.
    + unfold normal_form. unfold not. intro.
      destruct H0. inversion H0; subst.
      inversion H; subst. destruct H1. exists t1'. apply H5.
    + unfold not. intro. destruct H0; inversion H0.
Qed.

Inductive big_eval : term -> term -> Prop :=
| B_Value : forall t, value t -> big_eval t t
| B_IfTrue : forall t1 t2 t3 v2,
value v2 -> big_eval t1 ttrue -> big_eval t2 v2 -> big_eval (tif t1 t2 t3) v2
| B_IfFalse : forall t1 t2 t3 v3,
value v3 -> big_eval t1 tfalse -> big_eval t3 v3 -> big_eval (tif t1 t2 t3) v3
| B_Succ : forall t1 nv1,
nv nv1 -> big_eval t1 nv1 -> big_eval (tsucc t1) (tsucc nv1)
| B_PredZero : forall t1,
big_eval t1 tzero -> big_eval (tpred t1) tzero
| B_PredSucc : forall t1 nv1,
nv nv1 -> big_eval t1 (tsucc nv1) -> big_eval (tpred t1) nv1
| B_IsZeroZero : forall t1,
big_eval t1 tzero -> big_eval (tiszero t1) ttrue
| B_IsZeroSucc : forall t1 nv1,
nv nv1 -> big_eval t1 (tsucc nv1) -> big_eval (tiszero t1) (tfalse)
.

Notation "t ==> v" := (big_eval t v) (at level 60).

Lemma eval_value_big_eval : forall t v,
value v -> t --> v -> t ==> v.
Proof.
intros. induction H0.
- apply B_IfTrue.
  + apply H.
  + apply B_Value. right. apply BV_True.
  + apply B_Value. apply H.
- apply B_IfFalse.
  + apply H.
  + apply B_Value. right. apply BV_False.
  + apply B_Value. apply H.
- inversion H; inversion H1.
- apply B_Succ. inversion H. inversion H1; subst. apply H3. inversion H1.
  inversion H. inversion H1; subst.
apply or_introl with (B := bv t1') in H3. apply IHeval in H3. apply H3. inversion H1.
- apply B_PredZero. apply B_Value. left. apply NV_Zero.
- apply B_PredSucc. apply H0. apply B_Succ. apply H0. apply B_Value. apply H.
- destruct H; inversion H.
- apply B_IsZeroZero. apply B_Value. left. apply NV_Zero.
- apply B_IsZeroSucc with (nv1 := t). apply H0.
  apply B_Succ. apply H0. apply B_Value. left. apply H0.
- destruct H. inversion H. inversion H.
Qed.

Lemma nv_big_eval_nv : forall v v',
nv v -> v ==> v' -> nv v'.
Proof.
intros. inversion H0; subst; try assumption.
- inversion H.
- inversion H.
- apply NV_Succ. assumption.
- apply NV_Zero.
- inversion H.
- inversion H.
Qed.

Lemma value_big_eval_value : forall v v',
value v -> v ==> v' -> value v'.
Proof.
intros. inversion H0; subst; try assumption.
- left. apply NV_Succ. assumption.
- left. apply NV_Zero.
- left. assumption.
- right. apply BV_True.
- right. apply BV_False.
Qed.

Lemma big_eval_transitive : transitive big_eval.
Proof.
unfold transitive. intros.
generalize dependent z.
induction H.
- intros. assumption.
- intros. apply B_IfTrue.
  eapply value_big_eval_value.
  apply H. assumption. assumption. apply IHbig_eval2 in H2.
  assumption.
- intros. apply B_IfFalse.
  eapply value_big_eval_value.
  apply H. assumption. assumption. apply IHbig_eval2 in H2.
  assumption.
- intros. inversion H1; subst.
  apply B_Succ. assumption. assumption.
  apply IHbig_eval in H4. apply B_Succ. assumption. assumption.
- intros. inversion H0; subst.
  apply B_PredZero. assumption.
- intros. apply B_PredSucc.
  eapply nv_big_eval_nv. apply H. assumption.
  apply B_Succ in H1. apply IHbig_eval in H1.
  assumption.
  eapply nv_big_eval_nv. apply H. assumption.
- intros. inversion H0; subst.
  apply B_IsZeroZero. assumption.
- intros. inversion H1; subst.
  eapply B_IsZeroSucc. apply H. assumption.
Qed.

Lemma big_eval_value_value : forall t t',
t ==> t' -> value t -> value t' -> t = t'.
Proof.
intros.
induction H.
- reflexivity.
- inversion H0; inversion H4.
- inversion H0; inversion H4.
- destruct H0.
  inversion H0; subst.
  assert (value t1). left. assumption.
  apply IHbig_eval in H3. rewrite -> H3. reflexivity.
  left. inversion H; subst.
  apply NV_Zero.
  apply NV_Succ. assumption.
  inversion H0.
- inversion H0; inversion H2.
- inversion H0. inversion H3.
  inversion H3.
- inversion H0; inversion H2.
- inversion H0; inversion H3.
Qed.

Lemma big_eval_to_value : forall t t',
t ==> t' -> value t'.
Proof.
intros.
induction H; try assumption.
- left. apply NV_Succ. assumption.
- left. assumption.
- right. apply BV_True.
- right. apply BV_False.
Qed.

Theorem big_eval_deterministic : forall t t' t'',
t ==> t' -> t ==> t'' -> t' = t''.
Proof.
intros.
generalize dependent t''.
induction H.
- intros. assert (t ==> t''). assumption.
  apply value_big_eval_value in H0.
  apply big_eval_value_value. assumption. assumption. assumption.
  assumption.
- intros. induction H0.
  + Abort.

Lemma meval_value_big_eval : forall t v,
value v -> t -->* v -> t ==> v.
Proof.
intros.
apply meval_iff_meval' in H0.
induction t.
- inversion H0; subst.
  + inversion H1.
  + apply B_Value. assumption.
  + inversion H1.
- inversion H0; subst.
  + inversion H1.
  + apply B_Value. assumption.
  + inversion H1.
- inversion H0; subst.
  + inversion H1.
  + apply B_Value. assumption.
  + inversion H1.
- Abort.
