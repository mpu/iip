From stdpp Require Import base.
From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Import iprop own.
From iris.bi Require Import updates.
From iris.algebra Require Import ofe cmra gmap_view.
From iris.proofmode Require Import tactics.

Definition tag := positive.
Canonical Structure tagO : ofe := discreteO tag.

Definition loc := positive.

Inductive value : Set :=
  | IntV (n : Z)
  | LocV (ℓ : loc).

(* interpretation of types *)
Definition sem_typeO (Σ : gFunctors) : ofe := value -d> iPropO Σ.

Class sem_heapG (Σ : gFunctors) : Set := SemHeapG {
  sem_heapG_heap :> inG Σ (gmap_viewR loc (prodO tagO (laterO (sem_typeO Σ))));
}.

Inductive lang_ty := 
  | IntT
  | UnionT (A : lang_ty) (B : lang_ty)
  | ClassT (t : tag).
Canonical Structure lang_tyO : ofe := leibnizO lang_ty.

(* classe types have a single field, for now *)
Definition class_def := lang_ty.
Definition class_defs := gmap tag class_def.

Section proofs.
Context `{!sem_heapG Σ}.
Notation iProp := (iProp Σ).

(* assume a given set of class definitions *)
Context (Δ : class_defs).

(* the interpretation of types is simply given by
   the carrier set of the sem_typeO ofe *)
Notation interpO := (sem_typeO Σ).
Definition interp := ofe_car interpO.
Eval hnf in interp.

(* now, let's interpret some types *)

Definition interp_int : interp :=
  λ (v : value), ⌜∃ n, v = IntV n⌝%I.

Definition interp_union (iA : interp) (iB : interp) : interp :=
  λ (w : value), (iA w ∨ iB w)%I.

(* name for the semantic heap *)
Context (γ : gname).

Notation sem_heap_mapsto ℓ t iF :=
  (own γ (gmap_view_frag ℓ DfracDiscarded (t, Next iF))).

Notation ty_interpO := (lang_ty -d> interpO).

(* interpret a class type given the tag and the
   interpretation for the unique field type *)
Definition interp_class (t : tag) (rec : ty_interpO) : interp :=
  λ (w : value),
    (∃ ℓ fty, ⌜w = LocV ℓ ∧ Δ !! t = Some fty⌝ ∗
              sem_heap_mapsto ℓ t (rec fty))%I.

(* we use a blend of Coq/Iris recursion, the
   Coq recursion lets us handle simple structural
   cases, and we use Iris' recursion to deal with
   the more complicated case of class types *)
Definition interp_type_pre (rec : ty_interpO) : ty_interpO :=
  λ (ty : lang_ty),
    (fix go (ty : lang_ty) : interp :=
       match ty with
       | IntT => interp_int
       | UnionT A B => interp_union (go A) (go B)
       | ClassT t => interp_class t rec
       end) ty.

(* we cannot use solve_contractive out of the box
   because of the 'fix' combinator above *)
Local Instance interp_type_pre_contractive :
  Contractive interp_type_pre.
Proof.
  move=>????. elim=>*/=; solve_proper_core
      ltac:(fun _ => first [done | f_contractive | f_equiv]).
Qed.

(* the interpretation of types can now be
   defined as a fixpoint (because class types
   can be (mutually) recursive) *)
Definition interp_type := fixpoint interp_type_pre.

Lemma interp_type_unfold (ty : lang_ty) (v : value) :
  interp_type ty v ⊣⊢ interp_type_pre interp_type ty v.
Proof.
  rewrite {1}/interp_type.
  apply (fixpoint_unfold interp_type_pre ty v).
Qed.

Global Instance interp_type_persistent (ty : lang_ty) (v : value) :
  Persistent (interp_type ty v).
Proof.
  elim: ty => [].
  - rewrite interp_type_unfold. apply _.
  - move=>>. rewrite interp_type_unfold /=.
    rewrite /interp_union. rewrite -!interp_type_unfold.
    by apply bi.or_persistent.
  - move=>>. rewrite interp_type_unfold. apply _.
Qed.

(* that is a bit of an awkward lemma;
   I am not yet sure it "scales" *)
Lemma interp_type_loc_inversion ty ℓ :
  interp_type ty (LocV ℓ) -∗
  ∃ t, interp_type (ClassT t) (LocV ℓ).
Proof.
  rewrite interp_type_unfold. elim: ty => /=.
  - iIntros "%". naive_solver.
  - move=>? IH1 ? IH2. iIntros "[H|H]".
    by iApply IH1. by iApply IH2.
  - move=> t. iIntros "H". iExists t.
    by rewrite interp_type_unfold /=.
Qed.

(* language statics & semantics *)

Definition var := positive.

Inductive lang_expr : Type :=
  | VarE (v : var)
  | LitE (lit : Z)
  | OpE (op : Z → Z → Z)
        (lhs rhs : lang_expr).

Inductive lang_cmd : Type :=
  | LetC (v : var) (e : lang_expr)  (* local def *)
  | NewC (v : var) (t : tag)        (* allocation *)
  | GetC (v : var) (e : lang_expr)  (* field read *)
  | SetC (lhs rhs : lang_expr)      (* fiels store *)
  | SeqC (fstc sndc : lang_cmd)     (* sequence *)
  | CondC (cnd : lang_expr)
          (ifc elc : lang_cmd)      (* conditional *)
  | CondTagC (v : var) (t : tag)
             (cmd : lang_cmd)       (* tag test
                                       "if ($v is C) { ... }" *)
  | WhileC (cnd : lang_expr)
           (cmd : lang_cmd)         (* while loop *).

(* programs are a command and a 'return'
   expression *)
Record lang_prog : Type :=
  Prog { prog_body : lang_cmd;
         prog_ret : lang_expr }.

Definition local_tys := gmap var lang_ty.

Inductive expr_has_ty (lty : local_tys) :
    lang_expr → lang_ty → Prop :=
  | VarTy (v : var) (ty : lang_ty) :
      lty !! v = Some ty →
      expr_has_ty lty (VarE v) ty
  | LitTy (lit : Z) :
      expr_has_ty lty (LitE lit) IntT
  | OpTy (op : Z → Z → Z) (lhs rhs : lang_expr) :
      expr_has_ty lty lhs IntT →
      expr_has_ty lty rhs IntT →
      expr_has_ty lty (OpE op lhs rhs) IntT.

(* continuation-based typing for commands *)
Inductive cmd_has_ty :
    local_tys → lang_cmd → local_tys → Prop :=
  | LetTy lty v e ty :
      expr_has_ty lty e ty →
      cmd_has_ty lty (LetC v e) (<[v:=ty]> lty)
  | NewTy lty v t :
      cmd_has_ty lty (NewC v t) (<[v:=ClassT t]> lty)
  | GetTy lty v e t ty :
      Δ !! t = Some ty →
      expr_has_ty lty e (ClassT t) →
      cmd_has_ty lty (GetC v e) (<[v:=ty]> lty)
  | SetTy lty lhs rhs t ty :
      Δ !! t = Some ty →
      expr_has_ty lty lhs (ClassT t) →
      expr_has_ty lty rhs ty →
      cmd_has_ty lty (SetC lhs rhs) lty
  | SeqTy lty1 lty2 lty3 fstc sndc :
      cmd_has_ty lty1 fstc lty2 →
      cmd_has_ty lty2 sndc lty3 →
      cmd_has_ty lty1 (SeqC fstc sndc) lty3
  | CondTy lty1 lty2 cnd ifc elc :
      expr_has_ty lty1 cnd IntT →
      cmd_has_ty lty1 ifc lty2 →
      cmd_has_ty lty1 elc lty2 →
      cmd_has_ty lty1 (CondC cnd ifc elc) lty2
  | CondTagTy lty v t cmd :
      (* we do not care about v's type but it's
         got to have one! (i.e., be defined) *)
      is_Some (lty !! v) →
      cmd_has_ty (<[v:=ClassT t]> lty) cmd lty →
      cmd_has_ty lty (CondTagC v t cmd) lty
  | WhileTy lty cnd cmd :
      expr_has_ty lty cnd IntT →
      cmd_has_ty lty cmd lty →
      cmd_has_ty lty (WhileC cnd cmd) lty.

Inductive prog_has_ty : lang_prog → lang_ty → Prop :=
  | ProgTy lty ty body ret :
      cmd_has_ty ∅ body lty →
      expr_has_ty lty ret ty →
      prog_has_ty (Prog body ret) ty.

Definition local_env := gmap var value.

Inductive expr_eval (le : local_env) :
    lang_expr → value → Prop :=
  | VarEv v val :
      le !! v = Some val →
      expr_eval le (VarE v) val
  | LitEv lit :
      expr_eval le (LitE lit) (IntV lit)
  | OpEv op lhs rhs nl nr :
      expr_eval le lhs (IntV nl) →
      expr_eval le rhs (IntV nr) →
      expr_eval le (OpE op lhs rhs) (IntV (op nl nr)).

Definition value_trueish := λ v,
  match v with
  | IntV n => n <> 0
  | _ => True
  end.

Global Instance value_trueish_decision (v : value) :
  Decision (value_trueish v).
Proof. move: v => []; apply _. Defined.

Definition heap : Type := gmap loc (tag * value).

Definition tag_match (st : local_env * heap) v t :=
  ∃ l, st.1 !! v = Some (LocV l) ∧
       ∃ v, st.2 !! l = Some (t, v).

Global Instance tag_match_decision st v t:
    Decision (tag_match st v t).
Proof.
  move: st => [le h]. rewrite /tag_match /=.
  move: (le !! v) => [[]|];
    try (right; naive_solver).
  move=> l. case_eq (h !! l);
    last (right; naive_solver).
  move=> [t' ?] ?.
  destruct (decide (t = t')) as [->|];
    last (right; naive_solver).
  left. eauto.
Defined.

Inductive cmd_eval :
    (local_env * heap) → lang_cmd →
    (local_env * heap) → Prop :=
  | LetEv le h v e ve :
      expr_eval le e ve →
      cmd_eval (le, h) (LetC v e) (<[v:=ve]> le, h)
  | NewEv le h l v t :
      h !! l = None →
      Δ !! t = Some IntT →
      cmd_eval (le, h) (NewC v t)
               (<[v:=LocV l]> le, <[l:=(t,IntV 0)]> h)
  | GetEv le h v e l tl vl :
      expr_eval le e (LocV l) →
      h !! l = Some (tl, vl) →
      cmd_eval (le, h) (GetC v e) (<[v:=vl]> le, h)
  | SetEv le h lhs rhs l tl vr :
      expr_eval le lhs (LocV l) →
      (∃ vl, h !! l = Some (tl, vl)) →
      expr_eval le rhs vr →
      cmd_eval (le, h) (SetC lhs rhs) (le, <[l:=(tl,vr)]> h)
  | SeqEv st1 st2 st3 fstc sndc :
      cmd_eval st1 fstc st2 →
      cmd_eval st2 sndc st3 →
      cmd_eval st1 (SeqC fstc sndc) st3
  | Cond1Ev st1 st2 cnd vc ifc elc :
      expr_eval st1.1 cnd vc →
      value_trueish vc →
      cmd_eval st1 ifc st2 →
      cmd_eval st1 (CondC cnd ifc elc) st2
  | Cond2Ev st1 st2 cnd vc ifc elc :
      expr_eval st1.1 cnd vc →
      ¬value_trueish vc →
      cmd_eval st1 elc st2 →
      cmd_eval st1 (CondC cnd ifc elc) st2
  | CondTag1Ev st1 st2 v t cmd :
      tag_match st1 v t →
      cmd_eval st1 cmd st2 →
      cmd_eval st1 (CondTagC v t cmd) st2
  | CondTag2Ev st v t cmd :
      ¬tag_match st v t →
      cmd_eval st (CondTagC v t cmd) st
  | While1Ev st1 st2 st3 cnd vc cmd :
      expr_eval st1.1 cnd vc →
      value_trueish vc →
      cmd_eval st1 cmd st2 →
      cmd_eval st2 (WhileC cnd cmd) st3 →
      cmd_eval st1 (WhileC cnd cmd) st3
  | While2Ev st cnd vc cmd :
      expr_eval st.1 cnd vc →
      ¬value_trueish vc →
      cmd_eval st (WhileC cnd cmd) st.

Inductive prog_eval :
    lang_prog → value → Prop :=
  | ProgEv body le h ret val :
      cmd_eval (∅,∅) body (le,h) →
      expr_eval le ret val →
      prog_eval (Prog body ret) val.

(* heap models relation; the semantic heap does
   not appear because it is hidden in iProp  *)
Definition heap_models (h : heap) : iProp :=
  ∃ (sh : gmap loc (prodO tagO (laterO interpO))),
    own γ (gmap_view_auth 1 sh) ∗ ⌜dom (gset loc) sh = dom _ h⌝ ∗
    □ ∀ (ℓ : loc) (t : tag) (v : value),
      ⌜h !! ℓ = Some (t, v)⌝ -∗
        ∃ (iF : interp), sh !! ℓ ≡ Some (t, Next iF) ∗ ▷ iF v.

Definition interp_local_tys
    (lty : local_tys) (le : local_env) : iProp :=
  (∀ v ty, ⌜lty !! v = Some ty⌝ -∗
           ∃ val, ⌜le !! v = Some val⌝ ∗ interp_type ty val)%I.

Lemma expr_adequacy e lty le ty val :
  expr_eval le e val →
  expr_has_ty lty e ty →
  interp_local_tys lty le -∗
  interp_type ty val.
Proof.
  (* the language is this simple that no
     induction is necessary *)
  case.
  - move=> v val' ?. inversion_clear 1.
    iIntros "#Hlty".
    iDestruct ("Hlty" with "[//]") as (?) "[% H]".
    simplify_eq. done.
  - move=> lit. inversion_clear 1.
    iIntros "_". rewrite interp_type_unfold /=.
    rewrite /interp_int. by eauto.
  - move=> op lhs rhs nl nr _ _.
    inversion_clear 1.
    iIntros "_". rewrite interp_type_unfold /=.
    rewrite /interp_int. by eauto.
Qed.

Lemma interp_local_tys_update v lty le ty val :
  interp_local_tys lty le -∗
  interp_type ty val -∗
  interp_local_tys (<[v:=ty]>lty) (<[v:=val]>le).
Proof.
  iIntros "#Hi #?". iIntros (v' ty') "H".
  rewrite lookup_insert_Some.
  iDestruct "H" as %[[<- <-]|[??]].
  - iExists _. rewrite lookup_insert. by iSplit.
  - rewrite lookup_insert_ne; last done. by iApply "Hi".
Qed.

Lemma heap_models_lookup l h tl vl t :
  h !! l = Some (tl, vl) →
  heap_models h -∗
  interp_type (ClassT t) (LocV l) -∗
  ∃ fty, heap_models h ∗
         ⌜t = tl ∧ Δ !! t = Some fty⌝ ∗
         ▷ interp_type fty vl.
Proof.
  move=>?. iIntros "Hh Hc".
  rewrite interp_type_unfold /=.
  iDestruct "Hc" as (??) "[H H◯]".
  iDestruct "H" as %[[= <-]Hfty].
  iDestruct "Hh" as (sh) "(H●&%&#Hh)".
  iDestruct (own_valid_2 with "H● H◯") as "#Hv".
  rewrite gmap_view_both_validI.
  iDestruct "Hv" as "[_ HΦ]".
  iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
  iRewrite "H" in "HΦ".
  rewrite option_equivI prod_equivI /=.
  iDestruct "HΦ" as "[-> HΦ]".
  rewrite later_equivI.
  iExists fty.
  iSplitL. { iExists _. iFrame. by iSplit. }
  iSplitR; first done.
  iNext. rewrite discrete_fun_equivI.
  iSpecialize ("HΦ" $! vl).
  by iRewrite "HΦ" in "H▷".
Qed.

Lemma heap_models_update h l t v
      (Φ : interpO) `{∀ v, Persistent (Φ v)} :
  heap_models h -∗ (* ▷ *) Φ v -∗
  sem_heap_mapsto l t Φ -∗
  heap_models (<[l:=(t,v)]> h).
Proof.
  iIntros "Hh #HΦ #H◯".
  iDestruct "Hh" as (sh) "(H●&%&#Hh)".
  iDestruct (own_valid_2 with "H● H◯") as "#Hv".
  rewrite gmap_view_both_validI.
  iDestruct "Hv" as "[_ Hsh]".
  iExists sh. iFrame.
  iAssert ⌜is_Some (sh !! l)⌝%I as %?.
  { move: (sh !! l) => [>|].
    by iPureIntro; eauto.
    by rewrite option_equivI;
       iDestruct "Hsh" as "[]". }
  iSplitR.
  - iPureIntro.
    rewrite dom_insert_lookup_L; first done.
    apply (elem_of_dom (D:=gset loc)).
    by rewrite -H0 elem_of_dom.
  - iModIntro. iIntros (l' t' v') "H".
    rewrite lookup_insert_Some.
    iDestruct "H" as %[[<- [= <- <-]]|[??]].
    + iExists Φ. by iSplit.
    + by iApply "Hh".
Qed.

Notation "|=▷=>^ n Q" := (Nat.iter n (λ P, |==> ▷ P) Q)%I
  (at level 99, n at level 9, Q at level 200,
   format "|=▷=>^ n  Q") : bi_scope.

Lemma updN_zero (Q : iProp) : (|=▷=>^0 Q) ⊣⊢ Q.
Proof. done. Qed.

Lemma updN_S n (Q : iProp) :
  (|=▷=>^(S n) Q) ⊣⊢ |==> ▷ |=▷=>^n Q.
Proof. done. Qed.

Lemma updN_mono n (P Q : iProp) :
  (P -∗ Q) → (|=▷=>^n P) -∗ (|=▷=>^n Q).
Proof.
  elim: n => [//|n HI H].
  rewrite !updN_S.
  iApply bupd_mono.
  iApply bi.later_mono.
  by iApply HI.
Qed.

(* (* We may want something like that to improve the
      proof mode with the updN modality *)
Global Instance into_wand_updN n p q (R P Q : iProp) :
  IntoWand p q R P Q → IntoWand p q (|=▷=>^n R) (|=▷=>^n P) (|=▷=>^n Q).
Proof.
  rewrite /IntoWand /= => HR.
  by rewrite !later_intuitionistically_if_2 -later_wand HR.
Qed.
Global Instance into_wand_later_args p q R P Q :
  IntoWand p q R P Q → IntoWand' p q R (▷ P) (▷ Q).
Proof.   rewrite /IntoWand' /IntoWand /= => HR. 
           by rewrite !later_intuitionistically_if_2    
         (later_intro (□?p R)) -later_wand HR.
Qed.
*)

Lemma cmd_adequacy lty lty' st cmd st' :
  cmd_eval st cmd st' →
  cmd_has_ty lty cmd lty' →
  ∃ n,
    heap_models st.2 ∗ interp_local_tys lty st.1 -∗ |=▷=>^n
    heap_models st'.2 ∗ interp_local_tys lty' st'.1.
Proof.
  move=> E. move: lty lty'. elim: E.
  - move=>> ? /=. inversion_clear 1.
    exists 0. iIntros "[? #Hle]".
    rewrite updN_zero. iFrame.
    iDestruct (expr_adequacy with "Hle")
      as "#?"; try done.
    by iApply interp_local_tys_update.
  - move=>?? l v t ?? /=. inversion_clear 1.
    (* we need one modality to update the
       semantic heap *)
    exists 1. iIntros "[Hh #Hle]".
    rewrite updN_S updN_zero.
    iDestruct "Hh" as (sh) "(H●&Hdom&#Hh)".
    iDestruct "Hdom" as %Hdom.
    iMod (own_update with "H●") as "[H● H◯]".
    { apply (gmap_view_alloc _ l DfracDiscarded
        (t, Next (interp_type IntT)));
        last done.
    apply (not_elem_of_dom (D:=gset loc)).
    by rewrite Hdom not_elem_of_dom. }
    iIntros "!> !>". iDestruct "H◯" as "#H◯".
    iAssert (interp_type (ClassT t) (LocV l))
      with "[]" as "#Hl".
    { rewrite interp_type_unfold /=.
      iExists _, _. by iSplit. }
    iSplitL; last first.
    by iApply interp_local_tys_update.
    iExists _. iFrame. iSplit.
    by rewrite !dom_insert_L Hdom.
    iModIntro. iIntros (???) "Hlook".
    rewrite lookup_insert_Some.
    iDestruct "Hlook" as %[[<- [= <- <-]]|[Hℓ Hlook]].
    + iExists _. rewrite lookup_insert.
      iSplitR; first done.
      rewrite (interp_type_unfold IntT) /=.
      rewrite /interp_int. by eauto.
    + rewrite lookup_insert_ne; last done.
      by iApply "Hh".
  - move=>> ?? /=. inversion_clear 1.
    exists 1. iIntros "[Hh #Hle]".
    iModIntro. (* keep the later *)
    iDestruct (expr_adequacy with "Hle")
      as "#He"; try done.
    iDestruct (heap_models_lookup with "Hh He")
      as (fty) "(Hh&Ht&Hv)"; first done.
    rewrite H0. iDestruct "Ht" as %[?[=<-]].
    rewrite bi.later_sep.
    iSplitL "Hh"; first done.
    iNext. by iApply interp_local_tys_update.
  - move=>?? lhs rhs > ?[??]? /=.
    inversion_clear 1. exists 0.
    iIntros "[Hh #Hle]".
    rewrite updN_zero. iSplitL; last done.
    iDestruct (expr_adequacy lhs with "Hle")
      as "#Hlhs"; try done.
    iDestruct (expr_adequacy rhs with "Hle")
      as "#Hrhs"; try done.
    iDestruct (heap_models_lookup with "Hh Hlhs")
      as (fty) "(Hh&Ht&?)"; first done.
    rewrite H0. iDestruct "Ht" as %[[=<-][=<-]].
    rewrite interp_type_unfold.
    iDestruct "Hlhs" as (??) "(H&?)".
    rewrite H0. iDestruct "H" as %[[=<-][=<-]].
    iApply (heap_models_update with "Hh");
      try done. by intros; apply _.
  - move=>> ? Hfst ? Hsnd. inversion_clear 1.
    apply Hfst in H0. apply Hsnd in H1.
    clear Hfst Hsnd.
    destruct H0 as [n1 Hfst].
    destruct H1 as [n2 Hsnd].
    exists (n1 + n2).
    iIntros "H".
    iDestruct (Hfst with "H") as "H".
    iPoseProof (updN_mono with "H") as "H";
      first done.
    by rewrite Nat_iter_add.
  - move=>> ?? ? Hifc ??. inversion_clear 1.
    apply Hifc in H1. clear Hifc.
    destruct H1 as [n Hifc]. exists n.
    iIntros "H". iPoseProof (Hifc with "H") as "H".
    done.
  - move=>> ?? ? Helc ??. inversion_clear 1.
    apply Helc in H2. clear Helc.
    destruct H2 as [n Helc]. exists n.
    iIntros "H". iPoseProof (Helc with "H") as "H".
    done.
  - move=>[le1 h1] ? v t ? [l /= [? [v' ?]]] ? H.
    inversion_clear 1. apply H in H2. clear H.
    destruct H2 as [n Hcmd]. exists n.
    iIntros "H". iApply Hcmd. clear Hcmd n.
    (* now for some fun :) *)
    iDestruct "H" as "[Hh #Hlty]".
    destruct H1 as [ty Hvty].
    iDestruct ("Hlty" $! v with "[//]")
      as (?) "[Hlev Hv]".
    iDestruct "Hlev" as %Hlev.
    rewrite -> Hlev in *. simplify_eq.
    iDestruct (interp_type_loc_inversion with "Hv")
      as (t') "Hv'".
    iDestruct (heap_models_lookup with "Hh Hv'")
      as (fty) "(Hh&Ht&_)"; first done.
    iDestruct "Ht" as %[[=->]HΔ].
    iFrame. (* not quite interp_local_tys_update *)
    iIntros (??) "H". rewrite lookup_insert_Some.
    iDestruct "H" as %[[<- <-]|[??]].
    by iExists _; iSplit.
    by iApply "Hlty".
  - move=>> ?. inversion_clear 1.
    by exists 0.
  - (* this exactly the same thing as in the
       sequence case *)
    move=>> ??? Hitr_ ? Hcnt_. inversion 1; subst.
    move: (Hitr_ _ _ H5) => [n1 Hitr]. clear Hitr_.
    move: (Hcnt_ _ _ H) => [n2 Hcnt]. clear Hcnt_.
    exists (n1 + n2).
    iIntros "H".
    iDestruct (Hitr with "H") as "H".
    iPoseProof (updN_mono with "H") as "H";
      first done.
    by rewrite Nat_iter_add.
  - move=>> ???. inversion_clear 1.
    by exists 0.
Qed.

End proofs.
