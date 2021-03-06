Require Import List Omega.


Definition listToListList {A : Type} (l : list A) : list (list A) :=
  map (fun e:A => e::nil) l.

Definition hasLength {A : Type} (l : list A) (n: nat): bool :=
  beq_nat (Datatypes.length l) n.

Definition optionToList {A:Type} (o: option A) : list A :=
  match o with
  | Some a => a :: nil
  | None => nil
  end.

Definition optionList2List {A : Type} (l:list (option A)) : list A :=
  flat_map optionToList l.

Theorem optionList2List_In :
  forall (A:Type) (a: A) (l: list (option A)), (In a (optionList2List l)) -> (In (Some a) l).
Proof.
  intros.
  induction l.
  - inversion H.
  - destruct a0.
    + simpl in H.
      destruct H.
      * rewrite H.
        simpl.
        left.
        reflexivity.
      * simpl.
        right.
        apply IHl.
        assumption.
    + simpl in H.
      apply IHl in H.
      simpl.
      right.
      assumption.
Qed.

Definition singletons {A: Type} (l : list A) : list (list A) :=
  listToListList l.