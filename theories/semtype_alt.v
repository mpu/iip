From stdpp Require Import base strings gmap stringmap fin_maps.
From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Import iprop own.
From iris.algebra Require Import ofe cmra gmap_view.
From iris.proofmode Require Import tactics.

Definition tag := string.

Inductive ty :=
  | IntT
  | BoolT
  | NothingT
  | MixedT
  | ClassT (cname: tag)
  | NullT
  | NonNullT
  | UnionT (s t: ty)
  | InterT (s t: ty)
.

Record methodDef := {
  methodname: string;
  methodargs: list (string * ty)%type;
  methodrettype: ty;
  (* methodbody: comm; *)
}.

Record classDef := {
  classname: tag;
  superclass: option tag;
  classfields : stringmap ty;
  classmethods : stringmap methodDef;
}.

Definition loc := positive.

Global Instance loc_dec_eq (l l' : loc) : Decision (l = l') := _.

Inductive value : Set :=
  | IntV (z: Z)
  | BoolV (b: bool)
  | NullV
  | LocV (ℓ : loc).

Local Instance value_inhabited : Inhabited value := populate NullV.

Local Instance tag_equiv : Equiv tag := fun s0 s1 => String.eqb s0 s1 = true.
Local Instance tag_equivalence : Equivalence (≡@{tag}).
Proof.
  split.
  - now move => x; apply String.eqb_refl.
  - move => x y hxy.
    now rewrite /equiv /tag_equiv String.eqb_sym.
  - move => x y z.
    move => /String.eqb_eq hxy /String.eqb_eq hyz.
    now apply String.eqb_eq; transitivity y.
Qed.

(* Canonical Structure tagO : ofe := discreteO tag. *)
Canonical Structure tagO : ofe := discreteO tag.

(* interpretation of ty *)
Definition sem_typeO (Σ : gFunctors) : ofe := value -d> iPropO Σ.

Class sem_heapG (Σ : gFunctors) : Set := SemHeapG {
  sem_heapG_heap :> inG Σ (gmap_viewR loc (prodO tagO (gmapO string (laterO (sem_typeO Σ)))));
}.

Section proofs.
Context `{!sem_heapG Σ}.
Context (Δ: stringmap classDef).
Notation iProp := (iProp Σ).

Inductive extends (target: tag) : tag -> Prop :=
  | ERefl : extends target target
  | ESuper current super cdef :
      Δ !! current = Some cdef ->
      cdef.(superclass) = Some super ->
      extends target super ->
      extends target current
.

Hint Constructors extends : core.

Lemma extends_trans:
  forall A B C,
  extends B A -> extends C B -> extends C A.
Proof.
  intros A B C h; revert C.
  induction h as [ | current super cdef hin hsuper h hi]; intros C hC; first by done.
  econstructor; [ exact hin | exact hsuper | ].
  now apply hi.
Qed.

(* extends are chains: if A extends B and C, then either B extends C
 * or C extends B.
 *)
Lemma extends_is_chain:
  forall A B C,
  extends B A -> extends C A ->
  (extends B C \/ extends C B).
Proof.
  intros A B C h; revert C.
  induction h as [ | current super cdef hin hsuper h hi]; intros C hCA; first by right.
  destruct hCA as [ | current' super' cdef' hin' hsuper' h'].
  - left; econstructor; [ exact hin | exact hsuper | exact h].
  - rewrite hin in hin'; injection hin'; intro heq; subst; clear hin hin'.
    rewrite hsuper in hsuper'; injection hsuper'; intro heq; subst; clear hsuper hsuper'.
    destruct (hi C h') as [ hC | hC ]; first by left.
    by right.
Qed.

Inductive subtype : ty -> ty -> Prop :=
  | SubMixed : forall ty, subtype ty MixedT
  | SubNothing : subtype NothingT NothingT
  | SubInt : subtype IntT IntT
  | SubBool : subtype BoolT BoolT
  | SubNull : subtype NullT NullT
  | SubNonNull : subtype NonNullT NonNullT
  | SubClass : forall A B, extends B A -> subtype (ClassT A) (ClassT B)
  | SubUnionUpper1 : forall s t, subtype s (UnionT s t)
  | SubUnionUpper2 : forall s t, subtype t (UnionT s t)
  | SubUnionLeast : forall s t u, subtype s u -> subtype t u -> subtype (UnionT s t) u
  | SubInterLower1 : forall s t, subtype (InterT s t) s
  | SubInterLower2 : forall s t, subtype (InterT s t) t
  | SubInterGreatest: forall s t u, subtype u s -> subtype u t -> subtype u (InterT s t)
  (* I'd like to derive this rather than having it has a rule, but meh for now *)
  | SubTrans : forall s t u, subtype s t -> subtype t u -> subtype s u
.

Hint Constructors subtype : core.

Notation "s <: t" := (subtype s t) (at level 70, no associativity).

Lemma subtype_refl: forall s, s <: s.
Proof. 
  elim; move => //=.
  - now move => cname; constructor.
  - now move => s hs t ht; repeat constructor.
  - now move => s hs t ht; repeat constructor.
Qed.

Hint Resolve subtype_refl : core.

(* Not true, we need to introduce some "simplification/equivalence" for
 * unions and intersections, otherwise we have to prove things like
 * mixed ∨ S = mixed.
 *)
(* Lemma subtype_mixed_inv : forall s, MixedT <: s -> s = MixedT. *)
(* Proof. *)
(* assert (h: forall s t, s <: t -> s = MixedT -> t = MixedT); *)
(*   last by (intros s hs; now apply (h MixedT s)). *)
(* induction 1 as [ s | | | | | | A B hAB | s t | s t | s t u hsu hisu htu hitu | *)
(*     s t | s t | s t u hus hius hut hiut ]; move => hs //=. *)

(* Lemma subtype_trans: forall s t u, s <: t -> t <: u -> s <: u. *)
(* Proof. *)
(* move => s t u h; revert h u. *)
(* induction 1 as [ s | | | | | | A B hAB | s t | s t | s t u hsu hisu htu hitu | *)
(*     s t | s t | s t u hus hius hut hiut ]; move => w htw //=. *)


(* In case of conflict, keep the local field, not the parent *)
Definition merge_field (left right: option ty) : option ty :=
  match left, right with
  | Some l, _ => Some l
  | _, _ => right
  end
  .

Fixpoint get_fields (fuel:nat) (cname: tag) : stringmap ty :=
  match fuel with
  | O => ∅
  | S fuel =>
      match Δ !! cname with
      | None => ∅
      | Some cdef =>
          let from_parent :=
            match cdef.(superclass) with
            | None => ∅
            | Some parent => get_fields fuel parent
            end in
            merge merge_field cdef.(classfields) from_parent
      end
  end
.

(* Lemma get_fiels_fuel: forall n m, n <= m -> *)
(*   forall cname, get_fields n cname ⊆  get_fields m cname. *)
(* Proof. *)
(* induction n as [ | n hi]; move => m hle cname //=. *)
(* { now apply map_empty_subseteq. } *)
(* destruct m as [ | m]; first by lia. *)
(* simpl. *)
(* destruct (Δ !! cname) as [ [? super fields ? ]| ]; last by apply map_empty_subseteq. *)
(* simpl. *)
(* destruct super as [ super | ]; last by done. *)
(* Search merge. *)
(* Search map_subseteq. *)

(* the interpretation of types is simply given by
   the carrier set of the sem_typeO ofe *)
Notation interpO := (sem_typeO Σ).
Definition interp := ofe_car interpO.
Eval hnf in interp.
(* = value → iPropO Σ *)
(*      : Type *)

(* name for the semantic heap *)
Context (γ : gname).

Notation sem_heap_mapsto ℓ t iFs :=
  (own γ (gmap_view_frag ℓ DfracDiscarded (t, iFs))).

(* now, let's interpret some ty *)

Definition interp_null : interp :=
  λ (v : value), ⌜v = NullV⌝%I.

Definition interp_int : interp :=
  λ (v : value), (∃ z, ⌜v = IntV z⌝)%I.

Definition interp_bool : interp :=
  λ (v : value), (∃ b, ⌜v = BoolV b⌝)%I.

Definition interp_union (iA : interp) (iB : interp) : interp :=
  λ (v : value), (iA v ∨ iB v)%I.

Definition interp_inter (iA : interp) (iB : interp) : interp :=
  λ (v : value), (iA v ∧ iB v)%I.

Definition interp_nothing : interp :=
  λ (_: value), False%I.

Definition interp_mixed : interp :=
  λ (v : value),
    (⌜v = NullV⌝ ∨
     (∃ z, ⌜v = IntV z⌝) ∨
     (∃ b, ⌜v = BoolV b⌝) ∨
     (∃ ℓ t iFs, ⌜v = LocV ℓ⌝ ∗  sem_heap_mapsto ℓ t iFs))%I.

Definition interp_nonnull : interp :=
  λ (v : value),
     ((∃ z, ⌜v = IntV z⌝) ∨
     (∃ b, ⌜v = BoolV b⌝) ∨
     (∃ ℓ t iFs, ⌜v = LocV ℓ⌝ ∗  sem_heap_mapsto ℓ t iFs))%I.


Notation ty_interpO := (ty -d> interpO).

(* I need these two intermediate definition to make Coq/Type Classes instaces
 * happy.
 *)
Definition interp_ty_next (rec: ty_interpO) (typ: ty): laterO interpO :=
  Next (rec typ)
.

Definition interp_tys_next (rec: ty_interpO) (ftys: stringmap ty) : gmapO string (laterO interpO) :=
  (interp_ty_next rec) <$> ftys
.

(* interpret a class type given the tag and the
   interpretation of their fields *)
Definition interp_class (t : tag) (rec : ty_interpO) : interp :=
  λ (w : value),
    (∃ ℓ (cdef: classDef), ⌜w = LocV ℓ ∧ Δ !! t = Some cdef⌝ ∗
    sem_heap_mapsto ℓ t (interp_tys_next rec cdef.(classfields)))%I.

(* we use a blend of Coq/Iris recursion, the
   Coq recursion lets us handle simple structural
   cases, and we use Iris' recursion to deal with
   the more complicated case of class types *)
Definition interp_type_pre (rec : ty_interpO) : ty_interpO :=
  λ (typ : ty),
    (fix go (typ : ty) : interp :=
       match typ with
       | IntT => interp_int
       | BoolT => interp_bool
       | NothingT => interp_nothing
       | MixedT => interp_mixed
       | ClassT t => interp_class t rec
       | NullT => interp_null
       | NonNullT => interp_nonnull
       | UnionT A B => interp_union (go A) (go B)
       | InterT A B => interp_inter (go A) (go B)
       end) typ.

(* we cannot use solve_contractive out of the box
   because of the 'fix' combinator above *)
Local Instance interp_type_pre_contractive :
  Contractive interp_type_pre.
Proof.
move => n i0 i1 hdist.
elim => [ | | | | cname | | | A B | A B ] //=;
    [ (* ClassT *)
    | solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv])
    | solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv])
    ].
move => v; rewrite /interp_class.
apply bi.exist_ne; move => l.
apply bi.exist_ne; move => cdef.
apply bi.sep_ne; first by apply bi.pure_ne. 
apply own_ne.
apply gmap_view_frag_ne.
apply pair_ne; first by done.
rewrite /interp_tys_next /interp_ty_next.
(* *HERE* *)
(*
1 subgoal

Σ : gFunctors
sem_heapG0 : sem_heapG Σ
Δ : stringmap classDef
γ : gname
n : nat
i0, i1 : ty_interpO
hdist : dist_later n i0 i1
cname : tag
v : value
l : loc
cdef : classDef

========================= (1 / 1)

(λ typ : ty, Next (i0 typ)) <$> classfields cdef ≡{n}≡ 
(λ typ : ty, Next (i1 typ)) <$> classfields cdef
*)
Search dist.
f_equiv.
(* Not what I want
(λ typ : ty, Next (i0 typ)) = (λ typ : ty, Next (i1 typ))
*)

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

(* interpret a class type given the tag and
   the interpretation for the fields' type *)
Definition interp_class (cname : tag) (iFs: stringmap (laterO (sem_typeO Σ))) : interp :=
  λ (w : value), (∃ ℓ t, ⌜w = LocV ℓ /\ extends cname t⌝ ∗ sem_heap_mapsto ℓ t iFs)%I.

Fixpoint interp_type (fuel: nat) (typ : ty) : interp :=
  match fuel with
  | O => λ _, True%I
  | S fuel =>
      match typ with
      | IntT => interp_int
      | BoolT => interp_bool
      | NothingT => interp_nothing
      | MixedT => interp_mixed
      | ClassT cname =>
          let fields := get_fields fuel cname in
          let fields :=
            (fun typ => Next (interp_type fuel typ)) <$> fields in
            interp_class cname fields
      | NullT => interp_null
      | NonNullT => interp_nonnull
      | UnionT s t => interp_union (interp_type fuel s) (interp_type fuel t)
      | InterT s t => interp_inter (interp_type fuel s) (interp_type fuel t)
      end
  end
.

Lemma interp_type_true:
  forall n m, n <= m ->
  forall t v, interp_type m t v -∗ interp_type n t v.
Proof.
induction 1 as [ | m hm hi]; move => t v //=.
destruct t as [ | | | | cname | | |  A B | A B ].
- by iIntros "h"; destruct n as [ | n].
- by iIntros "h"; destruct n as [ | n].
- by iIntros "h".
- by iIntros "h"; destruct n as [ | n].
- iIntros "h"; destruct n as [ | n]; first by done.
  rewrite /= /interp_class.
  iDestruct "h" as (ℓ t) "[%h h1]".
  destruct h as [ -> hext ].
  iExists ℓ, t; iSplitR; first by done.
  iApply own_mono; last by iApply "h1".
  Locate "≼".
  Admitted.

Lemma interp_type_false: 
  forall n m, n <= m ->
  forall t v,
  (interp_type n t v -∗ False%I) -∗ interp_type m t v -∗ False%I.
Proof.
intros n m hne t v.
iIntros "hF hinterp".
iApply "hF".
iApply interp_type_true; first exact hne.
now done.
Qed.



induction 1 as [ | m hm hi]; move => t v //=.
iIntros "hFalse".
destruct t as [ | | | | cname | | |  A B | A B ].
- iIntros "h".
  destruct n as [ | n]; simpl in *; by iApply "hFalse".
- iIntros "h".
  destruct n as [ | n]; simpl in *; by iApply "hFalse".
- by done.
- iIntros "h".
  destruct n as [ | n]; simpl in *; by iApply "hFalse".
- iIntros "h".
  destruct n as [ | n]; simpl in *; first by iApply "hFalse".
  iApply "hFalse".




(* concrete heaps *)
Definition heap : Type := gmap loc (tag * stringmap value).

(* heap models relation; the semantic heap does
   not appear because it is hidden in iProp  *)
(* Helper defintion to state that fields are correctly modeled *)
Definition heap_models_fields
  (iFs: stringmap (laterO (sem_typeO Σ))) (vs: stringmap value) : iProp :=
  ⌜dom stringset vs = dom _ iFs⌝ ∗
  ∀ f iF,
  ⌜iFs !! f = Some iF⌝ -∗ ∃ v, (⌜vs !! f = Some v⌝ ∗ match iF with Next ϕ => ϕ v end).

Definition heap_models (h : heap) : iProp :=
  ∃ (sh: gmap loc (tag * stringmap (laterO (sem_typeO Σ)))),
    own γ (gmap_view_auth 1 sh) ∗ ⌜dom (gset loc) sh = dom _ h⌝ ∗
    ∀ (ℓ : loc) (t : tag) (vs : stringmap value),
      ⌜h !! ℓ = Some (t, vs)⌝ -∗
        ∃ (iFs : stringmap (laterO (sem_typeO Σ))),
        ⌜sh !! ℓ = Some (t, iFs)⌝  ∗ heap_models_fields iFs vs.


(* A <: B -> ΦA ⊂ ΦB *)
Theorem subtype_is_inclusion:
  forall A B, A <: B -> 
  forall fuel v,
  interp_type fuel A v -∗ interp_type fuel B v.
Proof.
induction 1; move => [ | fuel] v //.
- elim: ty0.
  + rewrite /interp_int /interp_mixed //=.
    iIntros "%h".
    now iRight; iLeft.
  + rewrite /interp_bool /interp_mixed //=.
    iIntros "%h".
    now iRight; iRight; iLeft.
  + now rewrite /interp_nothing; iIntros "%h".
  + by done.
  + rewrite /interp_mixed /interp_class //=.
    intros cname.
    iIntros "h".
    iDestruct "h" as (ℓ t) "[%h hr]".
    destruct h as [-> hext].
    iRight; iRight; iRight.
    iExists ℓ, t, _.
    iSplitR; done.
  + rewrite /interp_null /interp_mixed //=.
    iIntros "%h".
    now iLeft.
  + admit.
  + move => s hs t ht.
    iIntros "h".

 







  induction fuel as [ | fuel hi]; first by done.
  move => A B hAB v /=.
  rewrite /interp_class.
  iIntros "hA".
  iDestruct "hA" as (ℓ t) "[[-> %hcheck] hA]".
  iExists ℓ, t; iSplitR.
  { iPureIntro; split; first by done.
    now apply extends_trans with A. }

  induction 1 as [ | current super cdef hin hsuper h hi]; first by done.
  move => [ | fuel] v //=. 
  rewrite /interp_class.
  iIntros "hA".
  iDestruct "hA" as (ℓ t) "[[-> %hcheck] hA]".
  destruct (extends_is_chain _ _ _ hAB hcheck) as [hBt | hBt].
  - iExists ℓ, B.
    iSplitR.
    { iPureIntro; by split. }
   
   

Qed.

End proofs.

Section Examples.
Context `{!sem_heapG Σ}.
Notation iProp := (iProp Σ).
Context (γ : gname).
Notation sem_heap_mapsto ℓ t iFs :=
  (own γ (gmap_view_frag ℓ DfracDiscarded (t, iFs))).

(* the tag for a class C with a single Int field name foo*)
Definition tC : tag := "C".
Definition C : classDef := {|
  classname := tC;
  classmethods := ∅;
  superclass := None;
  classfields := <["foo" := IntT]>∅;
  |}.

Definition tD : tag := "D".
Definition D : classDef := {|
  classname := tD;
  classmethods := ∅;
  superclass := Some tC;
  classfields := <["rec" := ClassT tD]>∅;
  |}.

Definition classes: stringmap classDef :=
  <[tD := D]>(<[tC := C]>∅).

(* Sanity checks for get_fields and inheritance *)
Lemma check_fields_C :
  get_fields classes 1 tC !! "foo" = Some IntT /\
  forall n f, f <> "foo" -> get_fields classes n tC !! f = None.
Proof.
split.
- unfold classes; simpl; rewrite lookup_insert_ne; last by done.
  rewrite lookup_insert; simpl.
  by rewrite merge_empty_r //=.
- intros [ | n] f hf.
  { by simpl in *. }
  unfold classes; simpl; rewrite lookup_insert_ne; last by done.
  rewrite lookup_insert; simpl.
  rewrite merge_empty_r //=.
  rewrite omap_insert //=.
  rewrite lookup_insert_ne; last by done.
  now rewrite omap_empty.
Qed.

(* Sanity checks for get_fields and inheritance *)
Lemma check_fields_D :
  get_fields classes 2 tD !! "foo" = Some IntT /\
  get_fields classes 2 tD !! "rec" = Some (ClassT tD) /\
  forall n f, f <> "foo" -> f <> "rec" -> get_fields classes n tD !! f = None.
Proof.
split; [ | split].
- by unfold classes; simpl; rewrite lookup_insert //=.
- by unfold classes; simpl; rewrite lookup_insert //=.
- intros [ | n] f hf0 hf1.
  { by simpl in *. }
  unfold classes; simpl; rewrite lookup_insert //=.
  destruct n as [ | n].
  { simpl in *.
    rewrite merge_empty_r //=.
    rewrite omap_insert //=.
    rewrite lookup_insert_ne; last by done.
    now rewrite omap_empty. }
  simpl.
  rewrite lookup_insert_ne; last by done.
  rewrite lookup_insert //=.
  rewrite merge_empty_r //=.
  rewrite omap_insert //=.
  rewrite omap_empty //=.
  by rewrite lookup_merge !lookup_insert_ne //=.
Qed.

Definition fuel := 1.

Lemma alloc_unit_class_lemma (h : heap) (new : loc) :
  h !! new = None →
  heap_models γ h -∗ |==>
   heap_models γ (<[ new := (tC, <[ "foo" := IntV 0 ]> ∅) ]> h) ∗
   sem_heap_mapsto new tC (<[ "foo" := Next (interp_type classes γ fuel IntT)]>∅).
Proof.
  move=> Hnew. iIntros "Hm". iDestruct "Hm" as (sh) "[Hown [Hdom Hm]]".
  iDestruct "Hdom" as %Hdom.
  iMod (own_update with "Hown") as "[Hown Hfrag]".
  { apply (gmap_view_alloc _ new DfracDiscarded); last done.
    (* the typeclasses seem to be messed up below, I should be able
       to use not_elem_of_dom directly *) 
    move: Hnew. rewrite -!(@not_elem_of_dom _ _ (gset loc)).
    by move: Hdom => ->. }
  iIntros "!>". iFrame.
  iExists _. iFrame. iSplitR.
  { iPureIntro. rewrite !dom_insert_L.
    by move: Hdom => ->. }
  iIntros (ℓ t vs) "Hlook".
  rewrite lookup_insert_Some.
  iDestruct "Hlook" as %[[<- [= <- <-]]|[Hℓ Hlook]].
  - iExists _. rewrite lookup_insert.
    iSplitR; first done.
    (* BEGIN PROOF UPDATE *)
    (* was:
       by rewrite /= /interp_unit.
    *)
    rewrite /= /interp_int /heap_models_fields.
    iSplitR.
    { iPureIntro. by rewrite !dom_insert_L !dom_empty_L. }
    iIntros (f iF).
    rewrite !lookup_insert_Some.
    iIntros "Hf". iDestruct "Hf" as %[ [<- [= <-]]| [? [=]]].
    iExists (IntV 0); iSplit; first by done.
    by iExists 0.
    (* END PROOF UPDATE *)
  - iDestruct ("Hm" with "[]") as (iFs) "[% [%Hidom hisem]]"; first done.
    rewrite /heap_models_fields.
    iExists _. rewrite lookup_insert_ne; last done.
    (* BEGIN PROOF UPDATE *)
    (* was:
       by iSplitR.
    *)
    iSplitR; first by done.
    by iSplitR.
    (* END PROOF UPDATE *)
Qed.

End Examples.
