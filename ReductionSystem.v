Definition relation (X:Type) := X -> X -> Prop.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
~ exists t', R t t'.

Definition transitive {X:Type} (R:relation X) : Prop :=
forall x y z, R x y -> R y z -> R x z.
