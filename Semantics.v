Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps SpecCT.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".

(* Directives for forward-only semantics *)
Print direction.

Inductive directive : Set :=
| DStep : directive
| DForce: directive
| DLoad: string -> nat -> directive
| DStore: string -> nat -> directive
| DRollback: directive.

Definition dirs := list directive.

Inductive observation : Type :=
  | OBranch (b : bool)
  | OARead (a : string) (i : nat)
  | OAWrite (a : string) (i : nat)
  | ORollback.

Definition obs := list observation.

Lemma observation_eq_dec (o1 o2 : observation) :
    {o1 = o2} + {o1 <> o2}.
Proof.
    decide equality. 1, 2, 4: decide equality.
    all: apply string_dec.
Qed.

Inductive hd_ctxt : Type :=
  | CHole
  | CSeq (c1 : hd_ctxt) (c2 : com).

Fixpoint subst_hd ctxt c : com := match ctxt with 
                                  | CHole => c
                                  | CSeq ctxt' c2 => Seq (subst_hd ctxt' c) c2
                                  end.

Notation "C '<[' c ']>'" := (subst_hd C c).

Definition conf := (com * state * astate * bool)%type.

Reserved Notation
  "'<((' c , st , ast , b '•' cl '))>' '-->rb_' ds '^^' os '<((' ct , stt , astt , bt '•' clt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
st constr, ast constr, stt constr, astt constr at next level).

Inductive spec_rb_eval_small_step :
    list conf ->
    list conf -> dirs -> obs -> Prop :=
  | SpecRb_Asgn  : forall st ast b e n x cl,
      aeval st e = n ->
      <((x := e, st, ast, b • cl))> -->rb_[]^^[] <((skip, x !-> n; st, ast, b • cl))>
  | SpecRb_Seq : forall c1 st ast b ds os c1t stt astt bt c2 cl,
      <((c1, st, ast, b • cl))>  -->rb_ds^^os <((c1t, stt, astt, bt • cl))>  ->
      <(((c1;c2), st, ast, b • cl))>  -->rb_ds^^os <(((c1t;c2), stt, astt, bt • cl))>
  | SpecRb_Seq_Grow : forall c1 st ast b ds os c1t stt astt bt c1t' stt' astt' bt' c2 cl,
          <((c1, st, ast, b • cl))> -->rb_ds^^os <((c1t, stt, astt, bt • (c1t', stt', astt', bt') :: cl))> ->
          <(((c1; c2), st, ast, b • cl))> -->rb_ds^^os <(((c1t; c2), stt, astt, bt • (<{c1t'; c2}>, stt', astt', bt') :: cl))>
  | SpecRb_Seq_Skip : forall st ast b c2 cl,
      <(((skip;c2), st, ast, b • cl))>  -->rb_[]^^[] <((c2, st, ast, b • cl))>
  | SpecRb_If : forall be ct cf st ast b c' b' cl,
      b' = beval st be ->
      c' = (if b' then ct else cf) ->
      <((if be then ct else cf end, st, ast, b • cl))> -->rb_[DStep]^^[OBranch b'] <((c', st, ast, b • cl))>
  | SpecRb_If_F : forall be ct cf st ast b c' c'' b' cl,
      b' = beval st be ->
      c' = (if b' then cf else ct) ->
      c'' = (if b' then ct else cf) ->
      <((if be then ct else cf end, st, ast, b • cl))> -->rb_[DForce]^^[OBranch b'] <((c', st, ast, true • (c'', st, ast, b) :: cl ))>
  | SpecRb_While : forall be c st ast b cl,
      <((while be do c end, st, ast, b • cl))> -->rb_[]^^[]
      <((if be then c; while be do c end else skip end, st, ast, b • cl))>
  | SpecRb_ARead : forall x a ie st ast b i cl,
      aeval st ie = i ->
      i < length (ast a) ->
      <((x <- a[[ie]], st, ast, b • cl))> -->rb_[DStep]^^[OARead a i]
      <((skip, x !-> nth i (ast a) 0; st, ast, b • cl))>
  | SpecRb_ARead_U : forall x a ie st ast i a' i' cl,
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      <((x <- a[[ie]], st, ast, true • cl))> -->rb_[DLoad a' i']^^[OARead a i]
      <((skip, x !-> nth i' (ast a') 0; st, ast, true • cl))>
  | SpecRb_Write : forall a ie e st ast b i n cl,
      aeval st e = n ->
      aeval st ie = i ->
      i < length (ast a) ->
      <((a[ie] <- e, st, ast, b • cl))> -->rb_[DStep]^^[OAWrite a i]
      <((skip, st, a !-> upd i (ast a) n; ast, b • cl))>
  | SpecRb_Write_U : forall a ie e st ast i n a' i' cl,
      aeval st e = n ->
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      <((a[ie] <- e, st, ast, true • cl))> -->rb_[DStore a' i']^^[OAWrite a i]
      <((skip, st, a' !-> upd i' (ast a') n; ast, true • cl))>
  | SpecRb_Rollback : forall c st ast b c' st' ast' b' cl,
      <((c, st, ast, b • (c', st', ast', b') :: cl))> -->rb_[DRollback]^^[ORollback] <((c', st', ast', b' • cl))>
  where "<(( c , st , ast , b • cl ))> -->rb_ ds ^^ os  <(( ct ,  stt , astt , bt • clt ))>" :=
    (spec_rb_eval_small_step ((c, st, ast, b) :: cl) ((ct, stt, astt, bt) :: clt) ds os).

Reserved Notation
  "'<([' cl '])>' '-->rb*_' ds '^^' os '<([' cl' '])>'"
  (at level 40).

Inductive multi_spec_rb (cl: list conf) :
    list conf -> dirs -> obs -> Prop :=
  | multi_spec_rb_refl : <([cl])> -->rb*_[]^^[] <([cl])>
  | multi_spec_rb_trans (cl': list conf) (cl'': list conf) ds1 ds2 os1 os2:
      spec_rb_eval_small_step cl cl' ds1 os1 ->
      <([ cl' ])> -->rb*_ds2^^os2 <([ cl'' ])> ->
      <([ cl ])> -->rb*_(ds1++ds2)^^(os1++os2) <([cl''])>

  where "<([ cl ])> -->rb*_ ds ^^ os  <([ cl' ])>" :=
    (multi_spec_rb cl cl' ds os).

Reserved Notation
  "'<((' c , st , ast , b '))>' '-->fwd_' ds '^^' os '<((' ct , stt , astt , bt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive spec_fwd_eval_small_step :
    com -> state -> astate -> bool ->
    com -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | SpecFwd_Asgn  : forall st ast b e n x,
      aeval st e = n ->
      <((x := e, st, ast, b))> -->fwd_[]^^[] <((skip, x !-> n; st, ast, b))>
  | SpecFwd_Seq : forall c1 st ast b ds os c1t stt astt bt c2,
      <((c1, st, ast, b))>  -->fwd_ds^^os <((c1t, stt, astt, bt))>  ->
      <(((c1;c2), st, ast, b))>  -->fwd_ds^^os <(((c1t;c2), stt, astt, bt))>
  | SpecFwd_Seq_Skip : forall st ast b c2,
      <(((skip;c2), st, ast, b))>  -->fwd_[]^^[] <((c2, st, ast, b))>
  | SpecFwd_If : forall be ct cf st ast b c' b',
      b' = beval st be ->
      c' = (if b' then ct else cf) ->
      <((if be then ct else cf end, st, ast, b))> -->fwd_[DStep]^^[OBranch b'] <((c', st, ast, b))>
  | SpecFwd_If_F : forall be ct cf st ast b c' b',
      b' = beval st be ->
      c' = (if b' then cf else ct) ->
      <((if be then ct else cf end, st, ast, b))> -->fwd_[DForce]^^[OBranch b'] <((c', st, ast, true))>
  | SpecFwd_While : forall be c st ast b,
      <((while be do c end, st, ast, b))> -->fwd_[]^^[]
      <((if be then c; while be do c end else skip end, st, ast, b))>
  | SpecFwd_ARead : forall x a ie st ast b i,
      aeval st ie = i ->
      i < length (ast a) ->
      <((x <- a[[ie]], st, ast, b))> -->fwd_[DStep]^^[OARead a i]
      <((skip, x !-> nth i (ast a) 0; st, ast, b))>
  | SpecFwd_ARead_U : forall x a ie st ast i a' i',
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      <((x <- a[[ie]], st, ast, true))> -->fwd_[DLoad a' i']^^[OARead a i]
      <((skip, x !-> nth i' (ast a') 0; st, ast, true))>
  | SpecFwd_Write : forall a ie e st ast b i n,
      aeval st e = n ->
      aeval st ie = i ->
      i < length (ast a) ->
      <((a[ie] <- e, st, ast, b))> -->fwd_[DStep]^^[OAWrite a i]
      <((skip, st, a !-> upd i (ast a) n; ast, b))>
  | SpecFwd_Write_U : forall a ie e st ast i n a' i',
      aeval st e = n ->
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      <((a[ie] <- e, st, ast, true))> -->fwd_[DStore a' i']^^[OAWrite a i]
      <((skip, st, a' !-> upd i' (ast a') n; ast, true))>
  where "<(( c , st , ast , b ))> -->fwd_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" :=
    (spec_fwd_eval_small_step c st ast b ct stt astt bt ds os).

Reserved Notation
  "'<((' c , st , ast , b '))>' '-->fwd*_' ds '^^' os '<((' ct , stt , astt , bt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive multi_spec_fwd (c:com) (st:state) (ast:astate) (b:bool) :
    com -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | multi_spec_fwd_refl : <((c, st, ast, b))> -->fwd*_[]^^[] <((c, st, ast, b))>
  | multi_spec_fwd_trans (c':com) (st':state) (ast':astate) (b':bool)
                (c'':com) (st'':state) (ast'':astate) (b'':bool)
                (ds1 ds2 : dirs) (os1 os2 : obs) :
      <((c, st, ast, b))> -->fwd_ds1^^os1 <((c', st', ast', b'))> ->
      <((c', st', ast', b'))> -->fwd*_ds2^^os2 <((c'', st'', ast'', b''))> ->
      <((c, st, ast, b))> -->fwd*_(ds1++ds2)^^(os1++os2) <((c'', st'', ast'', b''))>

  where "<(( c , st , ast , b ))> -->fwd*_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" :=
    (multi_spec_fwd c st ast b ct stt astt bt ds os).

Ltac invert H := inversion H; subst.

Ltac cyclic H := apply (f_equal (@length conf)) in H; cbn in H; lia.

Require Import Coq.Program.Equality.

Lemma rb_fwd_same (c: com) (st: state) (ast: astate) (b: bool) (cl: list conf) (ds: dirs) (os: obs) (c': com) (st': state) (ast': astate) (b' : bool) (cl': list conf):
  ~(List.In DRollback ds) ->
  <([(c, st, ast, b) :: cl])> -->rb*_ds^^os <([(c', st', ast', b') :: cl' ])> ->
  <((c, st, ast, b))> -->fwd*_ds^^os <((c', st', ast', b'))>.
Proof.
intros Hnin Hrb.
dependent induction Hrb.
- constructor.
- destruct cl'0. 1: invert H.
  destruct c0 as [ [ [c0 st0] ast0 ] b0].
  apply (multi_spec_fwd_trans c st ast b c0 st0 ast0 b0).
  + clear IHHrb Hrb. dependent induction H; try now constructor.
    * constructor. eapply IHspec_rb_eval_small_step; try reflexivity. assumption.
    * constructor. eapply IHspec_rb_eval_small_step; try reflexivity. assumption.
    * cbn in Hnin. firstorder.
  + eapply IHHrb. 2, 3: reflexivity.
    intros Hin. now assert (In DRollback ds1 \/ In DRollback ds2) as Hin'%in_or_app by now right.
Qed.

Lemma rb_fwd_step_same (c: com) (st: state) (ast: astate) (b: bool) (cl: list conf) (ds: dirs) (os: obs) (c': com) (st': state) (ast': astate) (b' : bool) (cl': list conf):
    ~(In DRollback ds) ->
    <((c, st, ast, b • cl))> -->rb_ds^^os <((c', st', ast', b' • cl'))> ->
    <((c, st, ast, b))> -->fwd_ds^^os <((c', st', ast', b'))>.
Proof.
    intros Hnin Hrb.
    dependent induction Hrb; try now constructor.
    - constructor. eapply IHHrb; eauto.
    - constructor. eapply IHHrb; eauto.
    - firstorder.
Qed.

Lemma fwd_rb_same (c: com) (st: state) (ast : astate) (b : bool) (ds : dirs) (os : obs) (c' : com) (st' : state) (ast' : astate) (b' : bool) (cl: list conf):
  <((c, st, ast, b))> -->fwd*_ds^^os <((c', st', ast', b'))> ->
  exists cl', <([(c, st, ast, b) :: cl])> -->rb*_ds^^os<([ (c', st', ast', b') :: cl' ])>.
Proof.
intros Hfwd. revert cl.
dependent induction Hfwd.
- intros cl. exists cl. constructor.
- intros cl.
  assert (<(( c, st, ast, b • cl))> -->rb_ds1^^os1 <((c', st', ast', b' • cl))> \/ exists ci sti asti bi, <(( c, st, ast, b • cl))> -->rb_ds1^^os1 <((c', st', ast', b' • (ci, sti, asti, bi) :: cl))>) as Hrb.
  {
      clear Hfwd IHHfwd. dependent induction H; try (left; now constructor).
      - destruct (IHspec_fwd_eval_small_step cl) as [Hrb | (ci & sti & asti & bi & Hrb)].
        + left. now constructor.
        + right. exists <{ci ; c2}>, sti, asti, bi. now constructor.
      - right. subst. do 4 eexists; now constructor.
  }
  destruct Hrb as [Hrb | (? & ? & ? & ? & Hrb)].
  + specialize (IHHfwd cl) as [cl' IHHfwd]. exists cl'. econstructor; eassumption.
  + specialize (IHHfwd ((x, x0, x1, x2) :: cl)) as [cl' IHHfwd]. eexists. econstructor; eassumption.
Qed.

Lemma spec_rb_dirs_obs cl cl' ds os:
    spec_rb_eval_small_step cl cl' ds os ->
    ds = [] /\ os = [] \/ exists d o, ds = [d] /\ os = [o].
Proof.
    induction 1; eauto.
Qed.

Lemma multi_rb_dirs_obs_same_length cl cl' ds os:
    <([ cl ])> -->rb*_ds^^os <([ cl' ])> ->
    length ds = length os.
Proof.
    induction 1. 1: reflexivity.
    destruct (spec_rb_dirs_obs _ _ _ _ H) as [ [-> ->]| (d & o & -> & ->) ]; cbn; now rewrite IHmulti_spec_rb.
Qed.

Lemma rb_app_split cl cl' ds1 ds2 os:
    <([ cl ])> -->rb*_ds1++ds2^^os <([ cl' ])> ->
    exists cl'' os1 os2,
    <([ cl ])> -->rb*_ds1^^os1 <([ cl'' ])> /\
    <([ cl'' ])> -->rb*_ds2^^os2 <([ cl' ])> /\
    os = os1 ++ os2.
Proof.
    induction ds1 in cl, os|- *.
    - intros Hrb. exists cl, [], os.
      split. 
      + constructor.
      + easy.
    - intros Hrb. cbn in Hrb.
      dependent induction Hrb.
      specialize (IHHrb a ds1 ds2 IHds1).
      destruct (spec_rb_dirs_obs _ _ _ _ H) as [ [-> -> ]| (? & ? & -> & ->)].
      + cbn in x. destruct IHHrb as (cl1 & os1' & os2' & Hmulti1 & Hmulti2). 1: now rewrite x.
        exists cl1, os1', os2'. split. 2: easy.
        change (a :: ds1) with ([] ++ (a :: ds1)).
        change os1' with ([] ++ os1').
        econstructor; eassumption.
      + clear IHHrb.
        cbn in x. invert x.
        destruct (IHds1 _ _ Hrb) as (cl1 & os1' & os2' & Hmulti1 & Hmulti2 & ->).
        exists cl1, (x1 :: os1'), os2'. split. 2: easy.
        change (a :: ds1) with ([a] ++ ds1).
        change (x1 :: os1') with ([x1] ++ os1').
        econstructor; eassumption.
Qed.

Lemma multi_rb_app cl0 cl1 cl2 ds1 ds2 os1 os2:
    <([ cl0 ])> -->rb*_ds1^^os1 <([ cl1 ])> ->
    <([ cl1 ])> -->rb*_ds2^^os2 <([ cl2 ])> ->
    <([ cl0 ])> -->rb*_ds1++ds2^^os1++os2 <([ cl2 ])>.
Proof.
    intros Hrb1 Hrb2.
    dependent induction Hrb1.
    - exact Hrb2.
    - specialize (IHHrb1 Hrb2).
      do 2 rewrite <- app_assoc.
      econstructor; eassumption.
Qed.

Lemma multi_fwd_app c st ast b d o c' st' ast' b' d' o' c'' st'' ast'' b'':
    <((c, st, ast, b))> -->fwd*_d^^o <((c', st', ast', b'))> ->
    <((c', st', ast', b'))> -->fwd*_d'^^o' <((c'', st'', ast'', b''))> ->
    <((c, st, ast, b))> -->fwd*_d++d'^^o++o' <((c'', st'', ast'', b''))>.
Proof.
    intros Hfwd1 Hfwd2.
    dependent induction Hfwd1.
    - exact Hfwd2.
    - specialize (IHHfwd1 Hfwd2).
      do 2 rewrite <- app_assoc.
      econstructor; eassumption.
Qed.

Lemma list_nil_rcons {A: Type} (l: list A):
    l = [] \/ exists l' x, l = l' ++ [x].
Proof.
    induction l.
    - now left.
    - destruct IHl.
      + subst. right. now exists [], a.
      + destruct H as (l' & x & ->).
        right. exists (a :: l'), x.
        apply app_comm_cons.
Qed.

Lemma rb_rcons_split cl cl' ds d os o:
    <([ cl ])> -->rb*_ds ++ [d]^^os ++ [o] <([ cl'])> ->
    exists cl1 cl2,
    <([ cl ])> -->rb*_ds^^os <([ cl1 ])> /\
    spec_rb_eval_small_step cl1 cl2 [d] [o] /\
    <([ cl2 ])> -->rb*_[]^^[] <([ cl' ])>.
Proof.
    induction ds in cl, os |- *; intros Hrb.
    - cbn in Hrb.
      dependent induction Hrb.
      destruct (app_eq_unit _ _ x0) as [ [-> ->] | [-> ->] ].
      + destruct (spec_rb_dirs_obs _ _ _ _ H) as [ [_ ->] | (? & ? & Heq1 & Heq2)]. 2: congruence.
        cbn in x. destruct (IHHrb d os o) as (cl1 & cl2 & Hmulti1 & Hsingle & Hmulti2). 1: reflexivity. 1: now rewrite x.
        pose proof (multi_spec_rb_trans _ _ _ _ _ _ _ H Hmulti1). now exists cl1, cl2.
      + pose proof (multi_rb_dirs_obs_same_length _ _ _ _ Hrb) as Hlen. symmetry in Hlen. apply length_zero_iff_nil in Hlen. subst.
        rewrite app_nil_r in x.
        destruct (spec_rb_dirs_obs _ _ _ _ H) as [ [? ?] | (? & ? & _ & ->)]. 1: congruence.
        symmetry in x. apply elt_eq_unit in x as (<- & -> & _).
        exists cl, cl'. split. 2: easy.
        constructor.
    - change (a :: ds) with ([a] ++ ds) in Hrb. rewrite <- app_assoc in Hrb. apply rb_app_split in Hrb as (cl'' & os1 & os2 & Hrb1 & Hrb2 & Heq).
      assert (exists os2', os2 = os2' ++ [o] /\ os = os1 ++ os2') as [os2' [-> ->] ].
      {
          apply multi_rb_dirs_obs_same_length in Hrb2.
          rewrite length_app in Hrb2. cbn in Hrb2.
          pose proof (list_nil_rcons os2) as [? | (os2' & o' & ->)].
          { rewrite H in Hrb2. cbn in Hrb2. lia. }
          exists os2'.
          rewrite app_assoc in Heq.
          now apply app_inj_tail in Heq as [-> ->].
      }
      destruct (IHds _ _ Hrb2) as (cl1 & cl2 & Hmulti & Hrest).
      exists cl1, cl2. split. 2: assumption.
      change (a :: ds) with ([a] ++ ds).
      eapply multi_rb_app; eassumption.
Qed.

Lemma rb_step_nonempty cl cl' ds os:
    spec_rb_eval_small_step cl cl' ds os ->
    exists c st ast b cr c' st' ast' b' cr',
    cl = (c, st, ast, b) :: cr /\ cl' = (c', st', ast', b') :: cr'.
Proof.
    inversion 1; do 10 eexists; split; reflexivity.
Qed.

Lemma multi_rb_no_dirs_same_conf_stack c st ast b cl c' st' ast' b' cl':
    <([ (c, st, ast, b) :: cl ])> -->rb*_[]^^[] <([ (c', st', ast', b') :: cl' ])> ->
    cl = cl'.
Proof.
    intros Hmulti. dependent induction Hmulti.
    - reflexivity.
    - apply app_eq_nil in x as [-> ->], x0 as [-> ->].
      assert (exists c1 st1 ast1, cl'0 = (c1, st1, ast1, b) :: cl) as (?&?&?&->).
      { clear - H. dependent induction H; try (do 3 eexists; reflexivity).
          - specialize (IHspec_rb_eval_small_step _ _ _ _ _ (ltac: (reflexivity)) (ltac: (reflexivity)) (ltac: (reflexivity))) as (?&?&?&IH).
            invert IH. do 3 eexists; reflexivity. 
          - specialize (IHspec_rb_eval_small_step _ _ _ _ _ (ltac: (reflexivity)) (ltac: (reflexivity)) (ltac: (reflexivity))) as (?&?&?&IH).
            cyclic IH.
      }
      eapply IHHmulti; reflexivity.
Qed.

Lemma rb_no_force_no_rollback_same_conf_stack d os c st ast b cl c' st' ast' b' cl':
    d <> DForce -> d <> DRollback ->
    <(( c, st, ast, b • cl))> -->rb_[d]^^os <(( c', st', ast', b' • cl'))> -> 
    cl = cl'.
Proof.
    intros Hnf Hnr Hstep.
    dependent induction Hstep; try congruence.
    eapply IHHstep; try reflexivity. 1, 2: assumption.
    specialize (IHHstep _ _ _ _ _ _ _ _ _ _ _ Hnf Hnr (ltac: (reflexivity)) (ltac: (reflexivity)) (ltac: (reflexivity))).
    cyclic IHHstep.
    Unshelve. all: assumption. (*Remnants of eapply in the contradictory case, do not matter*)
Qed.

Lemma rb_rollback_pops_stack os c st ast b cl cl':
    spec_rb_eval_small_step ((c, st, ast, b) :: cl) cl' [DRollback] os ->
    cl = cl'.
Proof.
    intros Hstep.
    dependent induction Hstep.
    - specialize (IHHstep _ _ _ _ _ (ltac: (reflexivity)) (ltac: (reflexivity))). cyclic IHHstep.
    - specialize (IHHstep _ _ _ _ _ (ltac: (reflexivity)) (ltac: (reflexivity))). cyclic IHHstep.
    - reflexivity.
Qed.

Lemma rb_force_grows_stack os c st ast b cl c' st' ast' b' cl':
    <(( c, st, ast, b • cl))> -->rb_[DForce]^^os <(( c', st', ast', b' • cl'))> -> 
    exists C be ct cf, c = C<[<{if be then ct else cf end}>]> /\
    c' = C<[if (beval st be) then cf else ct]> /\ st' = st /\ ast' = ast /\ b' = true /\
    cl' = (C<[if (beval st be) then ct else cf]>, st, ast, b) :: cl /\
    os = [OBranch (beval st be)].
Proof.
    intro Hstep.
    dependent induction Hstep.
    - edestruct IHHstep as (? & ? & ? & ? & H ). 1-3: reflexivity.
      destruct H as (-> & -> & -> & -> & -> & H & _).
      cyclic H.
    - edestruct IHHstep as (C & be & ct & cf & H). 1-3: reflexivity.
      destruct H as (->&->&->&->&->&H&->). invert H; subst. cbn.
      exists (CSeq C c2), be, ct, cf. repeat split; try reflexivity.
    - exists CHole. do 3 eexists; repeat split; reflexivity.
Qed.

Lemma multi_rb_skip_rollback {c st1 st2 ast1 ast2 ds os c1' c2' st1' st2' ast1' ast2' b1' b2' cl1'  cl2' c1'' c2'' st1'' st2'' ast1'' ast2'' b1'' b2'' cl1'' cl2''}:
    ~ In DRollback ds ->
    <([ [(c, st1, ast1, false)] ])> -->rb*_ds^^os <([ (c1', st1', ast1', b1') :: cl1' ])> ->
    <(( c1', st1', ast1', b1' • cl1'))> -->rb_[DRollback]^^[ORollback] <(( c1'', st1'', ast1'', b1'' • cl1''))> ->
    <([ [(c, st2, ast2, false)] ])> -->rb*_ds^^os <([ (c2', st2', ast2', b2') :: cl2' ])> ->
    <(( c2', st2', ast2', b2' • cl2'))> -->rb_[DRollback]^^[ORollback] <(( c2'', st2'', ast2'', b2'' • cl2''))> ->
    exists ds' os', 
    <([ [(c, st1, ast1, false)] ])> -->rb*_ds'^^os' <([ (c1'', st1'', ast1'', b1'') :: cl1'' ])> /\
    <([ [(c, st2, ast2, false)] ])> -->rb*_ds'^^os' <([ (c2'', st2'', ast2'', b2'') :: cl2'' ])> /\
    ~ In DRollback ds' /\ length ds' <= length ds.
Proof.
    intros Hnin.
    induction ds in Hnin, os, c1', c2', st1', st2', ast1',  ast2', b1', b2', cl1', cl2' |- * using rev_ind.
    - intros Hmulti1 Hstep1 Hmulti2 Hstep2.
      clear Hmulti2 Hstep2.
      assert (os = []) as ->.
      {
          clear - Hmulti1.
          apply multi_rb_dirs_obs_same_length in Hmulti1. cbn in Hmulti1.
            now apply length_zero_iff_nil.
      }
      apply multi_rb_no_dirs_same_conf_stack in Hmulti1 as <-.
      exfalso.
      dependent induction Hstep1.
      + eapply IHHstep1; reflexivity.
      + eapply IHHstep1; reflexivity.
    - intros Hmulti1 Hstep1 Hmulti2 Hstep2.
      assert (exists os' o, os = os' ++ [o]) as (os' & o & ->).
      {
          apply multi_rb_dirs_obs_same_length in Hmulti1. clear - Hmulti1. rewrite length_app in Hmulti1. cbn in Hmulti1.
          assert (length os > 0) as H by lia. clear Hmulti1.
          induction os.
          - cbn in H. lia.
          - cbn in H. destruct os.
            + now exists [], a.
            + destruct IHos as (os' & o' & ->). 1: cbn; lia.
              exists (a :: os'), o'. reflexivity.
      }
      apply rb_rcons_split in Hmulti1 as (? & ? & Hmulti11 & Hstep1' & Hmulti12).
      apply rb_rcons_split in Hmulti2 as (? & ? & Hmulti21 & Hstep2' & Hmulti22).
      pose proof Hstep1' as Hstep1''. pose proof Hstep2' as Hstep2''.
      apply rb_step_nonempty in Hstep1'' as (?&?&?&?&?&?&?&?&?&?&->&->).
      apply rb_step_nonempty in Hstep2'' as (?&?&?&?&?&?&?&?&?&?&->&->).
      pose proof Hmulti12 as Hmulti12'. pose proof Hmulti22 as Hmulti22'.
      apply multi_rb_no_dirs_same_conf_stack in Hmulti12', Hmulti22'. subst.
      assert ((x <> DForce \/ x = DForce)) as [Hd | Hd] by (destruct x; try (now left); now right).
      + apply rb_no_force_no_rollback_same_conf_stack in Hstep1', Hstep2'. 2, 4: assumption. 2, 3: intros ->; apply Hnin; apply in_or_app; right; firstorder. subst.
        eapply IHds in Hmulti11. 2: intros Hin; apply Hnin; apply in_or_app; now left.
        3: eassumption.
        2: {
            clear - Hstep1. dependent destruction Hstep1.
            - exfalso. dependent induction Hstep1.
              + eapply IHHstep1; reflexivity.
              + cyclic x.
              + cyclic x.
            - exfalso. dependent induction Hstep1.
              + cyclic x.
              + eapply IHHstep1; reflexivity.
              + cyclic x.
            - constructor.
        }
        2: {
            clear - Hstep2. dependent destruction Hstep2.
            - exfalso. dependent induction Hstep2.
              + eapply IHHstep2; reflexivity.
              + cyclic x.
              + cyclic x.
            - exfalso. dependent induction Hstep2.
              + cyclic x.
              + eapply IHHstep2; reflexivity.
              + cyclic x.
            - constructor.
        }
        destruct Hmulti11 as (ds' & os'' & Hexec1 & Hexec2 & Hnin' & Hlen). exists ds', os''.
        firstorder.
        rewrite length_app. cbn. lia.
      + subst.
        apply rb_force_grows_stack in Hstep1' as (C1 & be1 & ct1 & cf1 & H1 & H2 & H3 & H4 & H5 & H6 & H7). invert H7. clear H7.
        apply rb_force_grows_stack in Hstep2' as (C2 & be2 & ct2 & cf2 & H1 & H2 & H3 & H4 & H5 & H6 & H7). invert H7. clear H7.
        exists (ds ++ [DStep]), (os' ++ [OBranch (beval x5 be1)]). repeat split.
        4: do 2 rewrite app_length; cbn; lia.
        3: {
            clear - Hnin.
            intros Hin%in_app_or. destruct Hin.
            - apply Hnin, in_or_app. now left.
            - cbn in H. firstorder. congruence.
        }
        * eapply multi_rb_app. 1: eassumption.
          change [DStep] with ([DStep] ++ []).
          change [OBranch (beval x5 be1)] with ([OBranch (beval x5 be1)] ++ []).
          apply rb_rollback_pops_stack in Hstep1. invert Hstep1. subst.
          econstructor. 2: constructor.
          clear.
          induction C1; cbn; now constructor.
        * eapply multi_rb_app. 1: eassumption.
          change [DStep] with ([DStep] ++ []).
          change [OBranch (beval x5 be1)] with ([OBranch (beval x5 be1)] ++ []).
            apply rb_rollback_pops_stack in Hstep2. invert Hstep2. subst.
            econstructor. 2: econstructor.
            rewrite H0.
            clear.
            induction C2; cbn; now constructor.
Qed.

Lemma rb_two_executions_skip_rolled_back_speculation c st1 st2 ast1 ast2 os ds c1' c2' st1' st2' ast1' ast2' b1' b2' cl1' cl2':
    <([ [(c, st1, ast1, false)] ])> -->rb*_ds^^os <([ (c1', st1', ast1', b1') :: cl1' ])> ->
    <([ [(c, st2, ast2, false)] ])> -->rb*_ds^^os <([ (c2', st2', ast2', b2') :: cl2' ])> ->
    exists ds' os',
    <([ [(c, st1, ast1, false)] ])> -->rb*_ds'^^os' <([ (c1', st1', ast1', b1') :: cl1' ])> /\
    <([ [(c, st2, ast2, false)] ])> -->rb*_ds'^^os' <([ (c2', st2', ast2', b2') :: cl2' ])> /\
    ~In DRollback ds'.
Proof.
    remember (length ds) as n.
    induction n as [| n IHn] in ds, Heqn, os, c1', c2', st1', st2', ast1', ast2', b1', b2', cl1', cl2' |- * using strong_induction_le.
    (*induction ds in os, c1', c2', st1', st2', ast1', ast2', b1', b2', cl1', cl2' |- * using rev_ind. [>TODO needs to be quantified<]*)
    - exists ds, os. split; [assumption|]. split; [assumption|].
      symmetry in Heqn.
      apply length_zero_iff_nil in Heqn. subst.
      firstorder.
    - intros Hrb1 Hrb2.
      assert (exists ds' d, ds = ds' ++ [d]) as (ds' & d & ->) by (destruct (list_nil_rcons ds); [apply length_zero_iff_nil in H; lia | exact H]).
      assert (exists os' o, os = os' ++ [o]) as (os' & o & ->) by (apply multi_rb_dirs_obs_same_length in Hrb1; destruct (list_nil_rcons os); [apply length_zero_iff_nil in H; lia | exact H]).
      apply rb_rcons_split in Hrb1 as (cl11 & cl21 & Hmulti11 & Hsingle1 & Hmulti21), Hrb2 as (cl42 & cl22 & Hmulti12 & Hsingle2 & Hmulti22).
      assert ((d <> DRollback) \/ d = DRollback) as [Hd | Hd] by (destruct d; try (now left); now right).
      + specialize (IHn (length ds')).
        assert (length ds' <= n) as Hlen.
        {
            rewrite length_app in Heqn. simpl in Heqn. lia.
        }
        pose proof Hsingle1 as Hsingle1'.
        apply rb_step_nonempty in Hsingle1' as (?&?&?&?&?&?&?&?&?&?&->&->).
        pose proof Hsingle2 as Hsingle2'.
        apply rb_step_nonempty in Hsingle2' as (?&?&?&?&?&?&?&?&?&?&->&->).
        specialize (IHn Hlen _ _ _ _ _ _ _ _ _ _ _ _ (ltac: (reflexivity)) Hmulti11 Hmulti12) as (dsIH & osIH & Hnew1 & Hnew2 & Hnin).
        exists (dsIH ++ [d]), (osIH ++ [o]). split; [|split].
        * eapply multi_rb_app. 1: exact Hnew1. change [d] with ([d] ++ []). change [o] with ([o] ++ []). econstructor; eassumption.
        * eapply multi_rb_app. 1: exact Hnew2. change [d] with ([d] ++ []). change [o] with ([o] ++ []). econstructor; eassumption.
        * intros [Hin1 | Hin2]%in_app_or; firstorder.
      + specialize (IHn (length ds')).
        assert (length ds' <= n) as Hlen.
        {
            rewrite length_app in Heqn. simpl in Heqn. lia.
        }
        pose proof Hsingle1 as Hsingle1'.
        apply rb_step_nonempty in Hsingle1' as (?&?&?&?&?&?&?&?&?&?&->&->).
        pose proof Hsingle2 as Hsingle2'.
        apply rb_step_nonempty in Hsingle2' as (?&?&?&?&?&?&?&?&?&?&->&->).
        specialize (IHn Hlen _ _ _ _ _ _ _ _ _ _ _ _ (ltac: (reflexivity)) Hmulti11 Hmulti12) as (dsIH & osIH & Hnew1 & Hnew2 & Hnin). subst.
        clear Heqn Hlen.
        assert (o = ORollback) as ->.
        {
            clear - Hsingle1.
            dependent induction Hsingle1.
            - eapply IHHsingle1; reflexivity.
            - eapply IHHsingle1; reflexivity.
            - reflexivity.
        }
        pose proof (multi_rb_skip_rollback Hnin Hnew1 Hsingle1 Hnew2 Hsingle2) as (dsnew & osnew & H1 & H2 & Hnin' & _).
        exists (dsnew ++ []), (osnew ++ []). repeat split.
        1, 2: eapply multi_rb_app; eassumption.
        intros Hin%in_app_or. firstorder.
Qed.

Lemma rb_same_directives_implies_fwd_same_directives {c st1 st2 ast1 ast2 os ds c1' c2' st1' st2' ast1' ast2' b1' b2' cl1' cl2'}:
    <([ [(c, st1, ast1, false)] ])> -->rb*_ds^^os <([ (c1', st1', ast1', b1') :: cl1' ])> ->
    <([ [(c, st2, ast2, false)] ])> -->rb*_ds^^os <([ (c2', st2', ast2', b2') :: cl2' ])> ->
    exists ds' os',
    <(( c, st1, ast1, false))> -->fwd*_ds'^^os' <((c1', st1', ast1', b1'))> /\
    <(( c, st2, ast2, false))> -->fwd*_ds'^^os' <((c2', st2', ast2', b2'))>.
Proof.
    intros Hrb1 Hrb2.
    eapply rb_two_executions_skip_rolled_back_speculation in Hrb1 as (ds' & os' & Hrb1' & Hrb2' & Hnin). 2: eassumption.
    exists ds', os'.
    split; eapply rb_fwd_same; eassumption.
Qed.

Lemma rb_leakage_common_prefix c st1 st2 ast1 ast2 ds os1 os2 c1' c2' st1' st2' ast1' ast2' b1' b2' cl1' cl2':
    <([ [(c, st1, ast1, false)] ])> -->rb*_ds^^os1 <([ (c1', st1', ast1', b1') :: cl1' ])> ->
    <([ [(c, st2, ast2, false)] ])> -->rb*_ds^^os2 <([ (c2', st2', ast2', b2') :: cl2' ])> ->
    os1 = os2 \/ exists dspre d dspost ospre c1i st1i ast1i b1i cl1i o1 c1it st1it ast1it b1it cl1it ospost1 c2i st2i ast2i b2i cl2i o2 c2it st2it ast2it b2it cl2it ospost2,
    <([ [(c, st1, ast1, false)] ])> -->rb*_dspre^^ospre <([ (c1i, st1i, ast1i, b1i) :: cl1i ])> /\
    <(( c1i, st1i, ast1i, b1i • cl1i ))> -->rb_d^^o1 <(( c1it, st1it, ast1it, b1it • cl1it ))> /\
    <([ (c1it, st1it, ast1it, b1it) :: cl1it ])> -->rb*_dspost^^ospost1 <([ (c1', st1', ast1', b1') :: cl1' ])> /\
    <([ [(c, st2, ast2, false)] ])> -->rb*_dspre^^ospre <([ (c2i, st2i, ast2i, b2i) :: cl2i ])> /\
    <(( c2i, st2i, ast2i, b2i • cl2i ))> -->rb_d^^o2 <(( c2it, st2it, ast2it, b2it • cl2it ))> /\
    <([ (c2it, st2it, ast2it, b2it) :: cl2it ])> -->rb*_dspost^^ospost2 <([ (c2', st2', ast2', b2') :: cl2' ])> /\
    o1 <> o2.
Proof.
    induction ds in os1, os2, c1', c2', st1', st2', ast1', ast2', b1', b2', cl1', cl2' |- * using rev_ind.
    - intros Hrb1 Hrb2. left.
      apply multi_rb_dirs_obs_same_length in Hrb1, Hrb2.
      destruct os1, os2; try (cbn in *; lia). reflexivity.
    - intros Hrb1 Hrb2.
      assert (exists os1' o1, os1 = os1' ++ [o1]) as (os1' & o1 & ->). { apply multi_rb_dirs_obs_same_length in Hrb1; rewrite length_app in Hrb1; destruct (list_nil_rcons os1); [apply length_zero_iff_nil in H ; cbn in *; lia| exact H]. }
      assert (exists os2' o2, os2 = os2' ++ [o2]) as (os2' & o2 & ->). { apply multi_rb_dirs_obs_same_length in Hrb2; rewrite length_app in Hrb2; destruct (list_nil_rcons os2); [apply length_zero_iff_nil in H ; cbn in *; lia| exact H]. }
      apply rb_rcons_split in Hrb1 as (? & ? & Hmulti11 & Hsingle1 & Hmulti21), Hrb2 as (? & ? & Hmulti12 & Hsingle2 & Hmulti22).
      pose proof (rb_step_nonempty _ _ _ _ Hsingle1) as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ->).
      pose proof (rb_step_nonempty _ _ _ _ Hsingle2) as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ->).
      specialize (IHds _ _ _ _ _ _ _ _ _ _ _ _ Hmulti11 Hmulti12).
      destruct IHds as [IHds | IHds].
      + destruct (observation_eq_dec o1 o2).
        * left. now subst.
        * right. exists ds, [x], [].
          subst.
          exists os2'. do 24 eexists. repeat split; try eassumption.
          now intros [=].
      + destruct IHds as (dspre&d&dpost&ospre&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&H1&H2&H3&H4&H5&H6&Hneq).
        right.
        exists dspre, d, (dpost ++ [x] ++ []), ospre.
        do 24 eexists. repeat split; try eassumption.
        * eapply multi_rb_app. 1: eassumption.
          econstructor; eassumption.
        * eapply multi_rb_app. 1: eassumption.
          econstructor; eassumption.
Qed.

Lemma drollback_produces_orollback: forall c st ast b cl os c' st' ast' b' cl',
    <(( c, st, ast, b • cl ))> -->rb_[DRollback]^^os <(( c', st', ast', b' • cl' ))> ->
    os = [ORollback].
Proof.
    intros.
    dependent induction H.
    - eapply IHspec_rb_eval_small_step; reflexivity.
    - eapply IHspec_rb_eval_small_step; reflexivity.
    - reflexivity.
Qed.

Lemma fwd_same_leakage_implies_rb_same_leakage c st1 st2 ast1 ast2:
    (forall ds c1' c2' st1' st2' ast1' ast2' b1' b2' os1 os2,
    <(( c, st1, ast1, false))> -->fwd*_ds^^os1 <((c1', st1', ast1', b1'))> ->
    <(( c, st2, ast2, false))> -->fwd*_ds^^os2 <((c2', st2', ast2', b2'))> ->
    os1 = os2) ->
    (forall ds c1' c2' st1' st2' ast1' ast2' b1' b2' cl1' cl2' os1 os2, 
    <([ [(c, st1, ast1, false)] ])> -->rb*_ds^^os1 <([ (c1', st1', ast1', b1') :: cl1' ])> ->
    <([ [(c, st2, ast2, false)] ])> -->rb*_ds^^os2 <([ (c2', st2', ast2', b2') :: cl2' ])> ->
    os1 = os2).
Proof.
    intros Hfwd_same ds c1' c2 st1' st2' ast1' ast2' b1' b2' cl1' cl2' os1 os2 Hrb1 Hrb2.
    eapply rb_leakage_common_prefix in Hrb2. 2: exact Hrb1.
    destruct Hrb2; [assumption|].
    clear Hrb1.
    destruct H as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&Hmulti1&Hstep1&_&Hmulti2&Hstep2&_&Hneq).
    pose proof (rb_same_directives_implies_fwd_same_directives Hmulti1 Hmulti2) as (ds' & os' & Hmulti1' & Hmulti2').
    assert (~ In DRollback x0).
    {
        pose proof Hstep1 as Hstep1'.
        apply spec_rb_dirs_obs in Hstep1' as [(-> & ->) | (d & o & -> & ->)].
        - firstorder.
        - intros Hin. cbn in Hin. destruct Hin; [|contradiction]. subst.
          apply drollback_produces_orollback in Hstep1 as [= ->], Hstep2 as ->.
          contradict Hneq. reflexivity.
    }
    apply rb_fwd_step_same in Hstep1, Hstep2. 2, 3: assumption.
    eapply multi_spec_fwd_trans in Hstep1, Hstep2. 2, 3: constructor.
    eapply multi_fwd_app in Hstep1, Hstep2. 2, 3: eassumption.
    eapply Hfwd_same in Hstep1. 2: exact Hstep2.
    contradict Hneq.
    clear - Hstep1.
    do 2 rewrite app_nil_r in *.
    induction os'; cbn in *.
    - now invert Hstep1.
    - apply IHos'. now invert Hstep1.
Qed.

Lemma rb_same_leakage_implies_fwd_same_leakage c st1 st2 ast1 ast2:
    (forall ds c1' c2' st1' st2' ast1' ast2' b1' b2' cl1' cl2' os1 os2, 
    <([ [(c, st1, ast1, false)] ])> -->rb*_ds^^os1 <([ (c1', st1', ast1', b1') :: cl1' ])> ->
    <([ [(c, st2, ast2, false)] ])> -->rb*_ds^^os2 <([ (c2', st2', ast2', b2') :: cl2' ])> ->
    os1 = os2)->
    (forall ds c1' c2' st1' st2' ast1' ast2' b1' b2' os1 os2,
    <(( c, st1, ast1, false))> -->fwd*_ds^^os1 <((c1', st1', ast1', b1'))> ->
    <(( c, st2, ast2, false))> -->fwd*_ds^^os2 <((c2', st2', ast2', b2'))> ->
    os1 = os2).
Proof.
    intros Hrb_same ds c1' c2' st1' st2' ast1' ast2' b1' b2' os1 os2 Hfwd1 Hfwd2.
    apply fwd_rb_same with (cl := []) in Hfwd1 as (cl1' & Hrb1), Hfwd2 as (cl2' & Hrb2).
    eapply Hrb_same; eassumption.
Qed.

