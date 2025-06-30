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
  | SpecRb_Seq : forall c1 st ast b ds os c1t stt astt bt c2 cl cl',
      <((c1, st, ast, b • cl))>  -->rb_ds^^os <((c1t, stt, astt, bt • cl'))>  ->
      <(((c1;c2), st, ast, b • cl))>  -->rb_ds^^os <(((c1t;c2), stt, astt, bt • cl'))>
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
  assert (exists cl', <(( c, st, ast, b • cl))> -->rb_ds1^^os1 <((c', st', ast', b' • cl'))>) as [cl' Hrb].
  {
      clear Hfwd IHHfwd. dependent induction H; try (eexists; now constructor).
      specialize (IHspec_fwd_eval_small_step cl) as [cl' IH].
      exists cl'. now constructor.
  }
  specialize (IHHfwd cl') as [cl'' IHHfwd].
  exists cl''. econstructor; eassumption.
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
      { clear - H. dependent induction H; try (do 3 eexists; reflexivity). specialize (IHspec_rb_eval_small_step _ _ _ _ _ (ltac: (reflexivity)) (ltac: (reflexivity)) (ltac: (reflexivity))) as (?&?&?&IH). invert IH. do 3 eexists; reflexivity. }
      eapply IHHmulti; reflexivity.
Qed.

Lemma rb_no_force_no_rollback_same_conf_stack d os c st ast b cl c' st' ast' b' cl':
    d <> DForce -> d <> DRollback ->
    <(( c, st, ast, b • cl))> -->rb_[d]^^os <(( c', st', ast', b' • cl'))> -> 
    cl = cl'.
Proof.
    intros Hnf Hnr Hstep.
    dependent induction Hstep; try congruence.
    eapply IHHstep; try reflexivity; assumption.
Qed.


Lemma multi_rb_skip_rollback c st ast ds os c' st' ast' b' cl' c'' st'' ast'' b'' cl'':
    <([ [(c, st, ast, false)] ])> -->rb*_ds^^os <([ (c', st', ast', b') :: cl' ])> ->
    <(( c', st', ast', b' • cl'))> -->rb_[DRollback]^^[ORollback] <(( c'', st'', ast'', b'' • cl''))> ->
    exists ds' os', 
    <([ [(c, st, ast, false)] ])> -->rb*_ds'^^os' <([ (c'', st'', ast'', b'') :: cl'' ])> /\
    length ds' <= length ds.
Proof.
    induction ds in os, c', st', ast', b', cl' |- * using rev_ind.
    - intros Hmulti Hstep.
      admit.
    - intros Hmulti Hstep.
      assert (exists os' o, os = os' ++ [o]) as (os' & o & ->) by admit.
      apply rb_rcons_split in Hmulti as (? & ? & Hmulti1 & Hstep' & Hmulti2).
      pose proof Hstep' as Hstep''.
      apply rb_step_nonempty in Hstep'' as (?&?&?&?&?&?&?&?&?&?&->&->).
      pose proof Hmulti2 as Hmulti2'.
      apply multi_rb_no_dirs_same_conf_stack in Hmulti2'. subst.
      assert ((x <> DForce \/ x = DForce)) as [Hd | Hd] by (destruct x; try (now left); now right).
      + apply rb_no_force_no_rollback_same_conf_stack in Hstep'. 2, 3: admit. subst.
        apply IHds in Hmulti1. 2: {
            clear - Hstep. dependent induction Hstep.
            - eapply IHHstep; admit. (* this case isn't really possible, but might have to prove this as its own lemma somehow somewhere *)
            - constructor.
        }
        destruct Hmulti1 as (ds' & os'' & Hexec & Hlen). exists ds', os''. split. 1: assumption.
        rewrite length_app. cbn. lia.
      + subst.
        clear IHds.
        dependent induction Hstep'.
        * admit.
        * exists (ds ++ [DStep]). exists (os' ++ [OBranch (beval x8 be)]). split. 2: do 2 rewrite app_length; cbn; lia.
          eapply multi_rb_app. 1: exact Hmulti1.
          (* TODO "invert" Hstep, to get equality*)
          change [DStep] with ([DStep] ++ []).
          change [OBranch (beval x8 be)] with ([OBranch (beval x8 be)] ++ []).
          admit. (* TODO *)
          
    (* This lemma would not be used as-is, but it currently serves as a draft for a part of the next proof, where we need to prove a similar statement for pairs of traces. *)

Admitted.

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
        (* The draft of the previous proof gives some idea how to proceed here, but is still highly unfinished. *)
Admitted.


(* This Lemma is in a "given-up-upon" state: It will be much easier to prove the lemma above, then use `rb_fwd_same` from above.
*)
Lemma rb_same_directives_implies_fwd_same_directives c st1 st2 ast1 ast2 os ds c1' c2' st1' st2' ast1' ast2' b1' b2' cl1' cl2':
    <([ [(c, st1, ast1, false)] ])> -->rb*_ds^^os <([ (c1', st1', ast1', b1') :: cl1' ])> ->
    <([ [(c, st2, ast2, false)] ])> -->rb*_ds^^os <([ (c2', st2', ast2', b2') :: cl2' ])> ->
    exists ds' os',
    <(( c, st1, ast1, false))> -->fwd*_ds'^^os' <((c1', st1', ast1', b1'))> /\
    <(( c, st2, ast2, false))> -->fwd*_ds'^^os' <((c2', st2', ast2', b2'))>.
Proof.
    remember (length ds) as n.
    induction n as [| n IHn] in ds, Heqn, os, c1', c2', st1', st2', ast1', ast2', b1', b2', cl1', cl2' |- * using strong_induction_le.
    (*induction ds in os, c1', c2', st1', st2', ast1', ast2', b1', b2', cl1', cl2' |- * using rev_ind. [>TODO needs to be quantified<]*)
    - symmetry in Heqn. apply length_zero_iff_nil in Heqn. subst.
      intros Hrb1 Hrb2. apply rb_fwd_same in Hrb1, Hrb2. 2, 3: easy.
      exists [], os. easy.
    - intros Hrb1 Hrb2.
      assert (exists ds' d, ds = ds' ++ [d]) as (ds' & d & ->) by (destruct (list_nil_rcons ds); [apply length_zero_iff_nil in H; lia | exact H]).
      assert (exists os' o, os = os' ++ [o]) as (os' & o & ->) by (apply multi_rb_dirs_obs_same_length in Hrb1; destruct (list_nil_rcons os); [apply length_zero_iff_nil in H; lia | exact H]).
      apply rb_rcons_split in Hrb1 as (cl11 & cl21 & Hmulti11 & Hsingle1 & Hmulti21), Hrb2 as (cl42 & cl22 & Hmulti12 & Hsingle2 & Hmulti22).
      assert ((d <> DRollback) \/ d = DRollback) as [Hd | Hd] by (destruct d; try (now left); now right).
      + assert (~In DRollback [d]) as Hnin by firstorder.
        pose proof Hsingle1 as Hsingle1'.
        apply rb_step_nonempty in Hsingle1' as (?&?&?&?&?&?&?&?&?&?&->&->).
        apply rb_fwd_step_same in Hsingle1. 2: assumption.
        pose proof Hsingle2 as Hsingle2'.
        apply rb_step_nonempty in Hsingle2' as (?&?&?&?&?&?&?&?&?&?&->&->).
        apply rb_fwd_step_same in Hsingle2. 2: assumption.
        specialize (IHn (length ds')).
        assert (length ds' <= n) as Hlen.
        {
            rewrite length_app in Heqn. simpl in Heqn. lia.
        }
        specialize (IHn Hlen _ _ _ _ _ _ _ _ _ _ _ _ (ltac: (reflexivity)) Hmulti11 Hmulti12) as (dsIH & osIH & Hfwd1 & Hfwd2).
        exists (dsIH ++ [d]), (osIH ++ [o]). split.
        * apply rb_fwd_same in Hmulti21. 2: firstorder.
          eapply multi_fwd_app. 1: exact Hfwd1. change [d] with ([d] ++ []). change [o] with ([o] ++ []). econstructor; eassumption.
        * apply rb_fwd_same in Hmulti22. 2: firstorder.
          eapply multi_fwd_app. 1: exact Hfwd2. change [d] with ([d] ++ []). change [o] with ([o] ++ []). econstructor; eassumption.
      + (* in the paper: by induction on the ds' obtained from IHds, in order to obtain only the part from before the latest force.
           easier in their version, because they don't have silent steps.
           Further, their fwd semantics still keeps a stack, whereas ours does not; currently unclear how we might obtain matching configurations therefore...

           Perhaps: prove this "undoing execution" part on rb semantics, before applying IHds. would require induction on length instead of directly on ds
        *)
        
Admitted.
