Require Export FunctionalExtensionality.

Axiom propositional_extensionality : forall P : Prop, P -> P = True.
Axiom propositional_extensionality_rev : forall P : Prop, P = True -> P.
Axiom proof_irrelevance : forall (P : Prop) (u v : P), u = v.
