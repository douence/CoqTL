Require Import String.
        
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.tTop.
Require Import core.Model.

Set Implicit Arguments.

Class TransformationEngineTypeClass (TransformationDef: Type) (RuleDef: Type) (OutputPatternElementDef: Type) (OutputPatternElementReferenceDef: Type) (SourceModelElement: Type) (SourceModelLink: Type) (SourceModel: Type) (TargetModelElement: Type) (TargetModelLink: Type) (TargetModel: Type) :=
  {
    allSourceModelElements: SourceModel -> list SourceModelElement;
    allSourceModelLinks: SourceModel -> list SourceModelLink;
    allTargetModelElements: TargetModel -> list TargetModelElement;
    allTargetModelLinks: TargetModel -> list TargetModelLink;

    getRulesFun: TransformationDef -> list RuleDef;
    getOutputPatternElementsFun: RuleDef -> list OutputPatternElementDef;
    getOutputPatternElementReferencesFun: OutputPatternElementDef -> list OutputPatternElementReferenceDef;

    executeFun: TransformationDef -> SourceModel -> TargetModel;
    
    matchPatternFun: TransformationDef -> list SourceModelElement -> SourceModel -> option RuleDef;
    instantiatePatternFun: TransformationDef -> SourceModel -> list SourceModelElement -> option (list TargetModelElement);
    applyPatternFun: TransformationDef -> SourceModel -> list SourceModelElement -> option (list TargetModelLink);

    matchRuleOnPatternFun:  RuleDef -> TransformationDef -> list SourceModelElement -> SourceModel -> option bool;
    instantiateRuleOnPatternFun: RuleDef -> TransformationDef -> list SourceModelElement -> SourceModel -> option (list TargetModelElement); 
    applyRuleOnPatternFun: RuleDef -> TransformationDef -> SourceModel -> list SourceModelElement -> list TargetModelElement -> option (list TargetModelLink);

    (* "Soundness" (everything in the target model is produced by a rule application)*)
    
    tr_surj_elements : 
    forall (tr: TransformationDef) (sm : SourceModel) (tm: TargetModel) (t1 : TargetModelElement),
      tm = executeFun tr sm -> In t1 (allTargetModelElements tm) ->
      (exists (sp : list SourceModelElement) (tp : list TargetModelElement) (r : RuleDef),
        In r (getRulesFun tr) /\
        In t1 tp /\
        instantiateRuleOnPatternFun r tr sp sm = Some tp /\
        incl sp (allSourceModelElements sm) /\
        incl tp (allTargetModelElements tm) /\
        matchPatternFun tr sp sm = Some r );

    tr_surj_links : 
    forall (tr: TransformationDef) (sm : SourceModel) (tm: TargetModel) (t1 : TargetModelLink),
      tm = executeFun tr sm -> In t1 (allTargetModelLinks tm) ->
      (exists (sp : list SourceModelElement) (tel : list TargetModelElement) (tpl : list TargetModelLink) (r : RuleDef),
        In r (getRulesFun tr) /\
        In t1 tpl /\
        applyRuleOnPatternFun r tr sm sp tel = Some tpl /\
        incl sp (allSourceModelElements sm) /\
        incl tpl (allTargetModelLinks tm) /\
        matchPatternFun tr sp sm = Some r );

    (* "Completeness" (if a rule matches, then its output is included in the target model) *)
    
    outp_incl_elements :
        forall (tr: TransformationDef) (sm : SourceModel) (tm: TargetModel) (sp : list SourceModelElement) (r: RuleDef) (tes: list TargetModelElement) (tls: list TargetModelLink),
          tm = executeFun tr sm -> In r (getRulesFun tr) -> incl sp (allSourceModelElements sm) ->
          instantiateRuleOnPatternFun r tr sp sm = Some tes ->
          incl tes (allTargetModelElements tm);

    outp_incl_links :
        forall (tr: TransformationDef) (sm : SourceModel) (tm: TargetModel) (sp : list SourceModelElement) (r: RuleDef) (tes: list TargetModelElement) (tls: list TargetModelLink),
          tm = executeFun tr sm -> In r (getRulesFun tr) -> incl sp (allSourceModelElements sm) ->
          instantiateRuleOnPatternFun r tr sp sm = Some tes ->
          applyRuleOnPatternFun r tr sm sp tes = Some tls ->
          incl tls (allTargetModelLinks tm);

    (* Correctness (the transformation does not generate dangling links) *)

    (* Convergence *)

    (* Additivity *)

    (* Well-formedness *)
    
    match_in :
        forall (tr: TransformationDef) (sm : SourceModel) (sp : list SourceModelElement) (r: RuleDef),
          matchPatternFun tr sp sm = Some r -> In r (getRulesFun tr);    

    (* Termination (implicit) *)
    
    (* Functionality (implicit) *)
    
    match_functional :
        forall (tr: TransformationDef) (sm : SourceModel) (sp : list SourceModelElement) (r1: RuleDef) (r2: RuleDef),
          matchPatternFun tr sp sm = Some r1 -> matchPatternFun tr sp sm = Some r2 -> r1 = r2;
    
  }.

Theorem match_functionality :  
  forall (TransformationDef RuleDef OutputPatternElementDef OutputPatternElementReferenceDef SourceModelElement SourceModelLink SourceModel TargetModelElement TargetModelLink TargetModel: Type) (eng: TransformationEngineTypeClass TransformationDef RuleDef OutputPatternElementDef OutputPatternElementReferenceDef SourceModelElement SourceModelLink SourceModel TargetModelElement TargetModelLink TargetModel)
    (tr: TransformationDef) (sm : SourceModel) (sp : list SourceModelElement) (r1: RuleDef) (r2: RuleDef),
          matchPatternFun tr sp sm  = Some r1 -> matchPatternFun tr sp sm = Some r2 -> r1 = r2.
Proof.
    intros.
    rewrite H in H0.
    inversion H0.
    reflexivity.
Qed.