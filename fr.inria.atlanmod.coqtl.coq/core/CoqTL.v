Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.
Require Import Coq.Numbers.NaryFunctions.

Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Engine.
Require Import core.utils.tTop.
Require Import core.utils.tList.


Require Import example.ClassMetamodel.
Require Import example.RelationalMetamodel.

Set Implicit Arguments.



Section CoqTL.

  Variables (SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type)
            (smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference)
            (TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type)
            (tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference).
  
  Definition SourceModel := Model SourceModelElement SourceModelLink.
  Definition TargetModel := Model TargetModelElement TargetModelLink.
  
  (** ** Abstract Syntax **)
  
  (** * Rule **)

  Inductive Rule: Type :=
  | BuildRule :
      forall 
        (* Input Elem Type *) (InElTypes: list SourceModelClass),
        (* Genric guard function *) (SourceModel -> (nfun SourceModelElement (length InElTypes) bool)) -> 
        Rule.
  
  
  (** * Transformation **)
  
  Inductive Transformation : Type := 
    BuildTransformation :
      (* Source Metamodel *) Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference -> 
      (* Target Metamodel *) Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference ->
      (* Rules *) list Rule ->
      Transformation.


  
End CoqTL.

About BuildRule.

Arguments BuildRule : default implicits.

(* Help to understand what is a nary function of Coq *)
Check  (fun (x: nat) (y: nat) => x > 1 /\  y>1) : (nfun nat 2 Prop).

(* Reuse rule notation for testing *)
Notation "'[' r1 ; .. ; r2 ']'" := (cons r1 .. (cons r2 nil) ..) (right associativity, at level 9).

(* A test case *)
(* TODO think of syntac sugar for guard *)
Definition Class2Relational :=
  (BuildTransformation ClassMetamodel RelationalMetamodel
    [ (BuildRule [ClassEClass] (fun (m: ClassModel) (c: ClassMetamodel_EObject) => 
                                        match c with
                                          | ClassMetamodel_BuildEObject ClassEClass clazz => true
                                          | _ => false
                                        end) )  ;
      (BuildRule [AttributeEClass] (fun (m: ClassModel) (a: ClassMetamodel_EObject) => 
                                        match a with
                                          | ClassMetamodel_BuildEObject AttributeEClass attr => (negb (getAttributeDerived attr))
                                          | _ => false
                                        end))
    ])
  .
  
(*
  (** ** OutputPatternElementReference **)

  (* Build OutputPatternElementReference with :
      an ref_type
      an trg_instance
      and a ref_ends         
   *)
  Inductive OutputPatternElementReference : Type :=
  | BuildOutputPatternElementReference : forall (OutRefs: TargetModelReference),
      (option (denoteModelReference OutRefs))
      -> OutputPatternElementReference.

  Definition OutputPatternElementReferenceType (o :  OutputPatternElementReference) : TargetModelReference :=
    match o with BuildOutputPatternElementReference type link => type end.
                                                                                       
  Definition OutputPatternElementReferenceLink (o :  OutputPatternElementReference) : option TargetModelLink :=
    match o with
      (BuildOutputPatternElementReference type link) =>
      ml <- link;
      return toModelLink type ml
    end.
  
  Fixpoint getOutputPatternElementReferenceTargetModelLinks (l : list OutputPatternElementReference) : list TargetModelLink :=
    match l with
    | nil => nil
    | ope :: opel => match ope with
                    | BuildOutputPatternElementReference OutRefs x =>
                      match x with
                      | Some x => BuildModelLink OutRefs x :: getOutputPatternElementReferenceTargetModelLinks opel
                      | None => getOutputPatternElementReferenceTargetModelLinks opel
                      end
                    end
    end.

  (** ** OutputPatternElement **)

  (* Build OutputPatternElement with :
      an elem_type
      an elem_id
      an elem_def
      and a (elem_name->ref_def)
   *)
  Inductive OutputPatternElement : Type :=
  | BuildOutputPatternElement : forall (OutElType: TargetModelClass),
      string
      -> (denoteModelClass OutElType)
      -> ((denoteModelClass OutElType) -> list OutputPatternElementReference)
      -> OutputPatternElement.
  
  Definition getOutputPatternElementName (o :  OutputPatternElement) : string :=
    match o with BuildOutputPatternElement type name el refs => name end.

  Definition getOutputPatternElementType (o :  OutputPatternElement) : TargetModelClass :=
    match o with BuildOutputPatternElement type name el refs => type end.

  Definition getOutputPatternElementBindings (o :  OutputPatternElement) : ((denoteModelClass (getOutputPatternElementType o)) -> list OutputPatternElementReference) :=
    match o with BuildOutputPatternElement type name el refs => refs end.

  Definition getOutputPatternElementElementType (o :  OutputPatternElement) : Set :=
    match o with BuildOutputPatternElement type name el refs => denoteModelClass type end.

  Definition getOutputPatternElementElement (o :  OutputPatternElement) : getOutputPatternElementElementType o :=
    match o with BuildOutputPatternElement type name el refs => el end.
  
  Definition getOutputPatternElementTargetModelElement (o :  OutputPatternElement) : TargetModelElement :=
    match o with BuildOutputPatternElement OutElType x x0 x1 => toModelElement OutElType x0 end.

  Definition getOutputPatternElementTargetModelLinks (o :  OutputPatternElement): list TargetModelLink :=
    match o with BuildOutputPatternElement type name el refs => getOutputPatternElementReferenceTargetModelLinks (refs el) end.

  Definition getOutputPatternElementElementByType (o :  OutputPatternElement) (type: TargetModelClass) : option (denoteModelClass type).
  Proof.
    remember o as ope.
    destruct o.
    remember (eqModelClass_dec type OutElType) as equal.
    destruct equal.
    - rewrite e.
      exact (Some d).
    - exact None.
  Defined.

  Inductive Rule: Type :=
  | BuildMultiElementRule :
      forall (InElType: SourceModelClass),
        ((denoteModelClass InElType) -> Rule)
        -> Rule
  | BuildSingleElementRule :
      forall (InElType: SourceModelClass),
        ((denoteModelClass InElType) -> (bool * list OutputPatternElement))
        -> Rule.

  Definition Phase : Type := SourceModel -> list Rule.

  Definition Transformation : Type := Phase -> Phase.

  (** * Abstract Syntax **)

  Inductive OutputBindingExpressionA : Type :=
      BuildOutputBindingExpressionA :
        nat ->
        nat ->
        nat ->
        OutputBindingExpressionA.

  Definition OutputBindingExpressionA_getRule (x : OutputBindingExpressionA) : nat :=
    match x with BuildOutputBindingExpressionA y _ _ => y end.
  
  Definition OutputBindingExpressionA_getOutputPatternElement (x : OutputBindingExpressionA) : nat :=
    match x with BuildOutputBindingExpressionA _ y _ => y end.

  Definition OutputBindingExpressionA_getOutputBinding (x : OutputBindingExpressionA) : nat :=
    match x with BuildOutputBindingExpressionA _ _ y => y end.
  
  Inductive OutputPatternElementReferenceA : Type :=
      BuildOutputPatternElementReferenceA :
        TargetModelReference ->
        OutputBindingExpressionA -> 
        OutputPatternElementReferenceA.

  Definition OutputPatternElementReferenceA_getType (x : OutputPatternElementReferenceA) : TargetModelReference :=
    match x with BuildOutputPatternElementReferenceA y _ => y end. 
  
  Definition OutputPatternElementReferenceA_getOutputBindingExpression (x : OutputPatternElementReferenceA) : OutputBindingExpressionA :=
    match x with BuildOutputPatternElementReferenceA _ y => y end. 

  Inductive OutputPatternElementExpressionA : Type :=
    BuildOutputPatternElementExpressionA :
      nat ->
      nat ->
      OutputPatternElementExpressionA.

  Definition OutputPatternElementExpressionA_getRule (x : OutputPatternElementExpressionA) : nat :=
    match x with BuildOutputPatternElementExpressionA y _ => y end.

  Definition OutputPatternElementExpressionA_getOutputPatternElement (x : OutputPatternElementExpressionA) : nat :=
    match x with BuildOutputPatternElementExpressionA _ y => y end.
  
  Inductive OutputPatternElementA : Type := 
    BuildOutputPatternElementA :
      string ->
      TargetModelClass ->
      OutputPatternElementExpressionA ->
      list OutputPatternElementReferenceA -> OutputPatternElementA.

  Definition OutputPatternElementA_getName (x : OutputPatternElementA) : string :=
    match x with BuildOutputPatternElementA y _ _ _  => y end.

  Definition OutputPatternElementA_getType (x : OutputPatternElementA) : TargetModelClass :=
    match x with BuildOutputPatternElementA _ y _ _  => y end.

  Definition OutputPatternElementA_getOutputPatternElementExpression (x : OutputPatternElementA) : OutputPatternElementExpressionA :=
    match x with BuildOutputPatternElementA _ _ y _  => y end.

  Definition OutputPatternElementA_getOutputPatternElementReferences (x : OutputPatternElementA) : list OutputPatternElementReferenceA :=
    match x with BuildOutputPatternElementA _ _ _ y  => y end.

  Inductive GuardExpressionA : Type :=
    BuildGuardExpressionA :
      nat ->
      GuardExpressionA.

  Definition GuardExpressionA_getRule (x : GuardExpressionA) : nat :=
    match x with BuildGuardExpressionA y => y end.
  
  Inductive RuleA : Type := 
    BuildRuleA :
      list SourceModelClass ->
      GuardExpressionA ->
      list OutputPatternElementA -> RuleA.

  Definition RuleA_getInTypes (x : RuleA) : list SourceModelClass :=
    match x with BuildRuleA y _ _ => y end.

  Definition RuleA_getGuard (x : RuleA) : GuardExpressionA :=
    match x with BuildRuleA _ y _ => y end.

  Definition RuleA_getOutputPattern (x : RuleA) : list OutputPatternElementA :=
    match x with BuildRuleA _ _ y => y end.  
  
  Inductive TransformationA : Type := 
    BuildTransformationA :
      list RuleA ->
      Transformation ->
      TransformationA.

  Definition TransformationA_getTransformation (x : TransformationA) : Transformation :=
    match x with BuildTransformationA _ y => y end.

  Definition TransformationA_getRules (x : TransformationA) : list RuleA :=
    match x with BuildTransformationA y _ => y end.

  (** * Parser **)
  
  Definition parseOutputPatternElementReference (tr: Transformation) (r ope oper: nat) (o: OutputPatternElementReference) : OutputPatternElementReferenceA :=   
    match o with
    | BuildOutputPatternElementReference t _ =>
      BuildOutputPatternElementReferenceA t (BuildOutputBindingExpressionA r ope oper)
    end.

  Definition parseOutputPatternElement (tr: Transformation) (r ope: nat) (o: OutputPatternElement) : OutputPatternElementA :=   
    match o with
    | BuildOutputPatternElement t n _ f =>
      BuildOutputPatternElementA n t (BuildOutputPatternElementExpressionA r ope) (mapWithIndex (parseOutputPatternElementReference tr r ope) 0 (f (bottomModelClass t)))
    end.

  Fixpoint parseRuleOutput (tr: Transformation) (n: nat) (r: Rule) : list OutputPatternElementA :=
    match r with
    | BuildMultiElementRule iet f => parseRuleOutput tr n (f (bottomModelClass iet)) 
    | BuildSingleElementRule iet f => mapWithIndex (parseOutputPatternElement tr n) 0 (snd (f (bottomModelClass iet))) 
    end.    
  
  Fixpoint parseRuleTypes (r: Rule) : list SourceModelClass :=
    match r with
    | BuildMultiElementRule iet f => (cons iet (parseRuleTypes (f (bottomModelClass iet))))
    | BuildSingleElementRule iet f => iet::nil
    end.
  
  Definition parseRule (tr: Transformation) (n: nat) (r: Rule) : RuleA :=
    (BuildRuleA (parseRuleTypes r) (BuildGuardExpressionA n) (parseRuleOutput tr n r)).
  
  Definition parseTransformation (tr: Transformation) : TransformationA :=
    BuildTransformationA 
      (mapWithIndex (parseRule tr) 0 (tr (fun c:SourceModel => nil) (Build_Model nil nil) )) tr.

  Definition parsePhase (tr: Phase) : TransformationA :=
    parseTransformation (fun t: Phase => tr).

  (** * Expression Evaluation **)

  (* the expression is checked against the types in the concrete transformation, may cause problems in theorems *)
  Fixpoint evalOutputBindingExpressionFix (o : OutputBindingExpressionA) (r : Rule) (intypes: list SourceModelClass) (sm: SourceModel) (el: list SourceModelElement) (te: TargetModelElement) : option TargetModelLink :=
    match r, intypes, el with
    | BuildMultiElementRule s f, t::ts, e::els =>
      e' <- toModelClass s e;
        evalOutputBindingExpressionFix o (f e') ts sm els te
    | BuildSingleElementRule s f, t::nil, e::nil =>
      e' <- toModelClass s e;
        ope <- (nth_error (snd (f e')) (OutputBindingExpressionA_getOutputPatternElement o));
        te' <- toModelClass (getOutputPatternElementType ope) te;
        oper <- (nth_error ((getOutputPatternElementBindings ope) te') (OutputBindingExpressionA_getOutputBinding o));
        (OutputPatternElementReferenceLink oper)
    | _, _, _ => None
    end.
  
  Definition evalOutputBindingExpression (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) (te: TargetModelElement) (o : OutputBindingExpressionA) : option (TargetModelLink) :=
  r <- (nth_error ((TransformationA_getTransformation tr) ((TransformationA_getTransformation tr) (fun c:SourceModel => nil)) sm) (OutputBindingExpressionA_getRule o));
    ra <- (nth_error (TransformationA_getRules tr) (OutputBindingExpressionA_getRule o));
  evalOutputBindingExpressionFix o r (RuleA_getInTypes ra) sm sp te. 

  (* the expression is checked against the types in the concrete transformation, may cause problems in theorems *)
  Fixpoint evalOutputPatternElementExpressionFix (o : OutputPatternElementExpressionA) (r : Rule) (intypes: list SourceModelClass) (sm: SourceModel) (el: list SourceModelElement) : option TargetModelElement :=
    match r, intypes, el with
    | BuildMultiElementRule s f, t::ts, e::els =>
      e' <- toModelClass s e;
        evalOutputPatternElementExpressionFix o (f e') ts sm els
    | BuildSingleElementRule s f, t::nil, e::nil =>
      e' <- toModelClass s e;
        ope <- (nth_error (snd (f e')) (OutputPatternElementExpressionA_getOutputPatternElement o));
        return (getOutputPatternElementTargetModelElement ope)
    | _, _, _ => None
    end.
  
  Definition evalOutputPatternElementExpression (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) (o : OutputPatternElementExpressionA): option TargetModelElement :=
  r <- (nth_error ((TransformationA_getTransformation tr) (fun c:SourceModel => nil) sm) (OutputPatternElementExpressionA_getRule o));
    ra <- (nth_error (TransformationA_getRules tr) (OutputPatternElementExpressionA_getRule o));
  evalOutputPatternElementExpressionFix o r (RuleA_getInTypes ra) sm sp. 

  (* the expression is checked against the types in the concrete transformation, may cause problems in theorems *)
  Fixpoint evalGuardExpressionFix (r : Rule) (intypes: list SourceModelClass) (sm: SourceModel) (el: list SourceModelElement) : option bool :=
    match r, intypes, el with
    | BuildMultiElementRule s f, t::ts, e::els =>
      e' <- toModelClass s e;
        evalGuardExpressionFix (f e') ts sm els
    | BuildSingleElementRule s f, t::nil, e::nil =>
      e' <- toModelClass s e;
      return (fst (f e'))
    | _, _, _ => None
    end.
  
  Definition evalGuardExpression (o : GuardExpressionA) (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) : option bool :=
    r <- (nth_error ((TransformationA_getTransformation tr) (fun c:SourceModel => nil) sm) (GuardExpressionA_getRule o));
      ra <- (nth_error (TransformationA_getRules tr) (GuardExpressionA_getRule o));
  evalGuardExpressionFix r (RuleA_getInTypes ra) sm sp. 

  (** * Engine **)

  (** ** Rule application **)

  Inductive ModelFragment (ModelElement: Type) (ModelLink: Type): Type :=
    BuildModelFragment: list ModelElement -> list ModelLink -> ModelFragment ModelElement ModelLink.
  
  Definition instantiateRuleOnPattern (r: RuleA) (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    m <- evalGuardExpression (RuleA_getGuard r) tr sm sp;
      if m then 
        return optionList2List (map (evalOutputPatternElementExpression tr sm sp) (map OutputPatternElementA_getOutputPatternElementExpression (RuleA_getOutputPattern r)))
      else
        None.

  Definition applyOutputPatternReferencesOnPattern (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) (l: list OutputPatternElementReferenceA) (te: TargetModelElement) : list TargetModelLink :=
  optionList2List (map (evalOutputBindingExpression tr sm sp te) (map OutputPatternElementReferenceA_getOutputBindingExpression l)).

  Definition applyRuleOnPattern (r: RuleA) (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) (tes: list TargetModelElement): option (list TargetModelLink) :=
  return (concat (zipWith (applyOutputPatternReferencesOnPattern tr sm sp) 
                          (map OutputPatternElementA_getOutputPatternElementReferences (RuleA_getOutputPattern r)) tes)).

  (** ** Rule matching **)

  Fixpoint matchPatternFix (l: list RuleA) (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option RuleA :=
    match l with
    | r :: rs => match evalGuardExpression (RuleA_getGuard r) tr sm sp with
                | Some op => Some r
                | None => matchPatternFix rs tr sm sp
                end
    | nil => None
    end.

  Definition matchPattern (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option RuleA :=
    matchPatternFix (TransformationA_getRules tr) tr sm sp.
  
  Definition instantiatePattern (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    r <- matchPattern tr sm sp;
     instantiateRuleOnPattern r tr sm sp.

  Definition applyPattern (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelLink) :=
    r <- matchPattern tr sm sp;
      tes <- instantiateRuleOnPattern r tr sm sp;
        applyRuleOnPattern r tr sm sp tes.

  Definition transformPattern (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option (ModelFragment TargetModelElement TargetModelLink) :=
      tes <- instantiatePattern tr sm sp;
        tls <- applyPattern tr sm sp;
  return BuildModelFragment tes tls.

  (** ** Resolution **)

  Definition resolveFix (l: list RuleA) (tr: TransformationA) (sm : SourceModel) (name: string) (type: TargetModelClass) (sp: list SourceModelElement) : option (denoteModelClass type) :=
    r <- matchPattern tr sm sp;
      ope <- find (fun oel => beq_string (OutputPatternElementA_getName oel) name) (RuleA_getOutputPattern r);
      te <- evalOutputPatternElementExpression tr sm sp (OutputPatternElementA_getOutputPatternElementExpression ope);
      toModelClass type te.

  Definition resolve (tr: Phase) (sm:SourceModel) (name: string) (type: TargetModelClass) (sp: list SourceModelElement): option (denoteModelClass type) :=
    resolveFix (TransformationA_getRules (parsePhase tr)) (parsePhase tr) sm name type sp.
    
  Definition resolveAll (tr: Phase) (sm:SourceModel) (name: string) (type: TargetModelClass) (sps: list (list SourceModelElement)) : option (list (denoteModelClass type)) :=
    Some (optionList2List (map (resolve tr sm name type) sps)).

  (** ** Rule scheduling **)
  
  Definition maxArity (tr: TransformationA) : nat :=
    fold_left max (map (length (A:=SourceModelClass)) (map RuleA_getInTypes (TransformationA_getRules tr))) 0.
                                                     
  Definition allTuples (tr: TransformationA) (sm : SourceModel) :list (list SourceModelElement) :=
    tuples_up_to_n (@allModelElements _ _ sm) (maxArity tr).

  Definition execute (tr: TransformationA) (sm : SourceModel) : TargetModel :=
    Build_Model
      (concat (optionList2List (map (instantiatePattern tr sm) (allTuples tr sm))))
      (concat (optionList2List (map (applyPattern tr sm) (allTuples tr sm)))). 

(* Set Implicit Arguments Inference *)

Arguments Phase : default implicits.
Arguments BuildSingleElementRule : default implicits.
Arguments BuildMultiElementRule : default implicits.
Arguments BuildOutputPatternElement : default implicits.
Arguments BuildOutputPatternElementReference : default implicits.
Arguments resolve : default implicits.
Arguments execute : default implicits.
Arguments getOutputPatternElementTargetModelElement : default implicits.

*)
