Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.EqNat.
Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.  

Require Import core.utils.tTop.
Require Import core.Notations.
Require Import core.CoqTL.
Require Import core.Metamodel.
Require Import core.Model.

Require Import example.Class2Relational.
Require Import example.ClassMetamodel.
Require Import example.RelationalMetamodel.

Theorem Table_id_positive_by_surj :
  forall (cm : ClassModel) (rm : RelationalModel), 
    rm = execute Class2Relational cm (* transformation *) ->
      (forall (c1 : ClassMetamodel_EObject), In c1 (allModelElements cm) -> ClassMetamodel_getId c1 > 0) (* precondition *) ->
        (forall (t1 : RelationalMetamodel_EObject), In t1 (allModelElements rm) -> RelationalMetamodel_getId t1 > 0). (* postcondition *)
Proof.
  intros cm rm H Hpre t1 Hintm.  
  apply tr_surj with (t1:=t1) in H.
  Focus 2. assumption.
  Focus 1.
  destruct H as [sp]. destruct H as [tp]. destruct H as [r].
  destruct H as [Hinsm]. destruct H as [Hintp]. destruct H as [Hexec]. destruct H as [Hinclsp]. destruct H as [incltp].
  rename H into Hmatch.
  simpl in Hmatch.
  destruct sp eqn:sp_ca.
  - inversion Hmatch.
  - destruct l eqn:l_ca.
    Focus 2.
    + inversion Hmatch.
    Focus 1.
    + destruct c eqn:c_ca. 
      * destruct c0 eqn:c0_ca.
        ** simpl in Hmatch.
           inversion Hmatch.
           rewrite <- H0 in Hexec.
           unfold instantiateRuleOnPattern in Hexec. simpl in Hexec.
           rewrite <- Hexec in Hintp.
           simpl in Hintp.
           destruct Hintp.
           rewrite <- H.
           simpl.
           unfold incl in Hinclsp.
           assert (In c ([ClassMetamodel_BuildEObject ClassEClass c1])). {
             simpl. left. symmetry. assumption.
           }
           apply Hinclsp in H1. apply Hpre in H1.
           unfold ClassMetamodel_getId in H1.
           rewrite  c_ca in H1.
           assumption.
           contradiction H.
        ** simpl in Hmatch.
           destruct (getAttributeDerived c1) eqn:derived_ca.
           simpl in Hmatch.
           inversion Hmatch.
           simpl in Hmatch.
           inversion Hmatch.
           rewrite <- H0 in Hexec.
           unfold instantiateRuleOnPattern in Hexec. unfold executeRuleOnPattern in Hexec. simpl in Hexec. rewrite derived_ca in Hexec. simpl in Hexec.
           rewrite <- Hexec in Hintp.
           simpl in Hintp.
           destruct Hintp.
           rewrite <- H.
           simpl.
           unfold incl in Hinclsp.
           assert (In c ([ClassMetamodel_BuildEObject AttributeEClass c1])). {
             simpl. left. symmetry. assumption.
           }
           apply Hinclsp in H1. apply Hpre in H1.
           unfold ClassMetamodel_getId in H1.
           rewrite  c_ca in H1.
           assumption.
           contradiction H.
Qed.
