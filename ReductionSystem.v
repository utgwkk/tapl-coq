Definition relation (X:Type) := X -> X -> Prop.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
~ exists t', R t t'.
