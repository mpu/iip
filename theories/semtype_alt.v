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

Notation "A '`extends`' B" := (extends B A) (at level 70, no associativity).

Lemma extends_trans:
  forall A B C,
  A `extends` B -> B `extends` C -> A `extends` C.
Proof.
  intros A B C h; revert C.
  induction h as [ | current super cdef hin hsuper h hi]; intros C hC; first by done.
  econstructor; [ exact hin | exact hsuper | ].
  now apply hi.
Qed.

(* Note useful, just for sanity check: extends are chains.
 * if A extends B and C, then either B extends C or C extends B.
 *)
Corollary extends_is_chain:
  forall A B C,
   A `extends` B -> A `extends` C->
  (C `extends` B \/ B `extends` C).
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

(* has_field fname cname checks if the class cname has a field name fname *)
Inductive has_field (fname: string) : tag -> Prop :=
  | HasField current cdef fty:
      Δ !! current = Some cdef ->
      cdef.(classfields) !! fname = Some fty ->
      has_field fname current
  | InheritsField current parent cdef:
      Δ !! current = Some cdef ->
      cdef.(classfields) !! fname = None ->
      cdef.(superclass) = Some parent ->
      has_field fname parent ->
      has_field fname current.

Hint Constructors has_field : core.

(* all fields of class cname are in the fnames set *)
(* TODO: We don't check types, change this to take a string set instead *)
Definition fields_incl (cname: tag) (fnames: stringmap ty) : Prop :=
  ∀ fname, has_field fname cname → fname ∈ dom stringset fnames.

Lemma has_field_extends: forall A B, A `extends` B ->
  forall fname, has_field fname B -> has_field fname A.
Proof.
move => A B.
elim => [ | current super cdef hcdef hsuper h hi]; first done.
move => fname hB.
case_eq (cdef.(classfields) !! fname) => [ ty | ] hfields.
{ by apply HasField with cdef ty. }
eapply InheritsField; [ done | done | done | ].
by apply hi.
Qed.

Lemma fields_incl_extends: forall A B, A `extends` B ->
  forall fields, fields_incl A fields -> fields_incl B fields.
Proof.
move => A B hext fields hsB fname hA.
apply hsB.
eapply has_field_extends; done.
Qed.

Inductive subtype : ty -> ty -> Prop :=
  | SubMixed : forall ty, subtype ty MixedT
  | SubClass : forall A B, A `extends` B -> subtype (ClassT A) (ClassT B)
  | SubMixed2: subtype MixedT (UnionT NonNullT NullT)
  | SubIntNonNull: subtype IntT NonNullT
  | SubBoolNonNull: subtype BoolT NonNullT
  | SubClassNonNull: forall A, subtype (ClassT A) NonNullT
  | SubUnionUpper1 : forall s t, subtype s (UnionT s t)
  | SubUnionUpper2 : forall s t, subtype t (UnionT s t)
  | SubUnionLeast : forall s t u, subtype s u -> subtype t u -> subtype (UnionT s t) u
  | SubInterLower1 : forall s t, subtype (InterT s t) s
  | SubInterLower2 : forall s t, subtype (InterT s t) t
  | SubInterGreatest: forall s t u, subtype u s -> subtype u t -> subtype u (InterT s t)
  | SubRefl: forall s, subtype s s
  | SubTrans : forall s t u, subtype s t -> subtype t u -> subtype s u
.

Hint Constructors subtype : core.

Notation "s <: t" := (subtype s t) (at level 70, no associativity).

(* Derived rules *)
Lemma subtype_union_comm : forall A B, (UnionT A B) <: (UnionT B A).
Proof.
by auto.
Qed.

Lemma subtype_inter_comm : forall A B, (InterT A B) <: (InterT B A).
Proof.
by auto.
Qed.

Lemma subtype_union_assoc:
  forall A B C, (UnionT (UnionT A B) C) <: (UnionT A (UnionT B C)).
Proof.
by eauto.
Qed.

Lemma subtype_inter_assoc:
  forall A B C, (InterT (InterT A B) C) <: (InterT A (InterT B C)).
Proof.
by eauto.
Qed.

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

Notation ty_interpO := (ty -d> interpO).

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

Definition interp_nonnull : interp :=
  λ (v : value),
     ((∃ z, ⌜v = IntV z⌝) ∨
     (∃ b, ⌜v = BoolV b⌝) ∨
     (∃ ℓ t iFs, ⌜v = LocV ℓ⌝ ∗  sem_heap_mapsto ℓ t iFs))%I.

Definition interp_mixed : interp :=
 λ (v: value), (interp_nonnull v ∨ interp_null v)%I.

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
Definition interp_class (cname : tag) (rec : ty_interpO) : interp :=
  λ (w : value),
    (∃ ℓ t fields, ⌜w = LocV ℓ ∧ extends cname t ∧ fields_incl t fields⌝ ∗
    sem_heap_mapsto ℓ t (interp_tys_next rec fields))%I.

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

Section gmap.
  Context {K: Type} {HKeqdec: EqDecision K} {HKcount: Countable K}.

  Lemma gmap_fmap_ext_ne 
    {A} {B : ofe} (f g : A → B) (m : gmap K A) n :
    (∀ x, f x ≡{n}≡ g x) → f <$> m ≡{n}≡ g <$> m.
  Proof.
    intros Hf k.
    induction m as [|i x m Hi IH] using map_ind; move => /=.
    - by rewrite !lookup_fmap !lookup_empty /=.
    - rewrite !lookup_fmap.
      destruct (HKeqdec k i) as [ -> | hne].
      + rewrite !lookup_insert /=.
        now apply Some_Forall2.
      + rewrite !lookup_insert_ne //=.
        by rewrite !lookup_fmap in IH.
  Qed.
End gmap.

(* we cannot use solve_contractive out of the box because of
 * the 'fix' combinator above
 *)
Local Instance interp_type_pre_contractive :
  Contractive interp_type_pre.
Proof.
move => n ???.
elim => * //=;
    [ (* ClassT *)
    | solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv])
    | solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv])
    ].
move => v; rewrite /interp_class.
do 3 (f_equiv; intro).
do 4 f_equiv.
rewrite /interp_tys_next /interp_ty_next.
apply gmap_fmap_ext_ne => typ.
f_contractive.
by destruct n.
Qed.

(* the interpretation of types can now be
   defined as a fixpoint (because class types
   can be (mutually) recursive) *)
Definition interp_type := fixpoint interp_type_pre.

Lemma interp_type_unfold (ty : ty) (v : value) :
  interp_type ty v ⊣⊢ interp_type_pre interp_type ty v.
Proof.
  rewrite {1}/interp_type.
  apply (fixpoint_unfold interp_type_pre ty v).
Qed.

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
  forall v,
  interp_type A v -∗ interp_type B v.
Proof.
induction 1 as [A | A B hext | | | | A | A B| A B | A B C h0 hi0 h1 hi1
  | A B | A B | A B C h0 hi0 h1 hi1 | A | A B C h0 hi0 h1 hi1 ]; move => v;
  rewrite !interp_type_unfold /=.
- rewrite /interp_mixed.
  elim: A => /=.
  + iIntros "h"; by repeat iLeft.
  + iIntros "h"; by iLeft; iRight; iLeft.
  + by rewrite /interp_nothing; iIntros "h".
  + done. 
  + rewrite /interp_class => cname.
    iIntros "h".
    iDestruct "h" as (ℓ t fields) "[%h0 h1]".
    destruct h0 as [-> [hext hfields]].
    iLeft.
    iRight.
    iRight.
    by iExists _, _, _; iFrame.
  + iIntros "h"; by iRight.
  + by iIntros "h"; iLeft.
  + move => s hs t ht.
    rewrite /interp_union.
    iIntros "h".
    iDestruct "h" as "[ h | h ]".
    by iApply hs.
    by iApply ht.
  + move => s hs t ht.
    rewrite /interp_inter.
    iIntros "h".
    iDestruct "h" as "[? _]"; by iApply hs.
- rewrite /interp_class.
  iIntros "h".
  iDestruct "h" as (ℓ t fields) "[%h hsem]".
  destruct h as [-> [hext2 hfields ]].
  iExists ℓ, t, fields.
  iSplit.
  { iPureIntro; split; first by done.
    split ; first by eapply extends_trans.
    done.
  }
  by iFrame.
- by rewrite /= /interp_mixed.
- iIntros "h"; by iLeft.
- iIntros "h"; by iRight; iLeft.
- rewrite /interp_class.
  iIntros "h"; iRight; iRight.
  iDestruct "h" as (ℓ t fields) "[%h0 h1]".
  destruct h0 as [-> [hext hfields]].
  by iExists _, _, _; iFrame.
- rewrite /interp_union.
  by iIntros "h"; iLeft.
- rewrite /interp_union.
  by iIntros "h"; iRight.
- rewrite /interp_union.
  rewrite -!interp_type_unfold.
  iIntros "[h | h]"; first by iApply hi0.
  by iApply hi1.
- rewrite /interp_inter.
  rewrite -!interp_type_unfold.
  by iIntros "[? _]".
- rewrite /interp_inter.
  rewrite -!interp_type_unfold.
  by iIntros "[_ ?]".
- rewrite /interp_inter.
  rewrite -!interp_type_unfold.
  iIntros "h".
  iSplit; first by iApply hi0.
  by iApply hi1.
- by rewrite -!interp_type_unfold.
- rewrite -!interp_type_unfold.
  iIntros "h".
  iApply hi1.
  by iApply hi0.
Qed.
End proofs.

Section Examples.
Context `{!sem_heapG Σ}.
Notation iProp := (iProp Σ).
Context (γ : gname).
Notation interpO := (sem_typeO Σ).

Definition sem_heap_mapsto ℓ t (iFs: gmapO string (laterO interpO)) :=
  (own γ (gmap_view_frag ℓ DfracDiscarded (t, iFs))).


(*
class C {
  int $foo;
}

class D extends C {
  D $rec;
}
*)
Definition C : classDef := {|
  classname := "C";
  classmethods := ∅;
  superclass := None;
  classfields := {["foo" := IntT]};
  |}.

Definition D : classDef := {|
  classname := "D";
  classmethods := ∅;
  superclass := Some "C";
  classfields := {["rec" := ClassT "D"]};
  |}.

Definition Δ: stringmap classDef :=
  <["D" := D]>{["C" := C]}.

Fact C_field : forall fname, has_field Δ fname "C" <-> fname = "foo".
Proof.
move => fname; split => [hf | ->].
- inversion hf; subst; clear hf.
  + rewrite /Δ /= lookup_insert_ne //= lookup_insert in H.
    injection H; intros <-; clear H.
    case_eq (string_eq_dec fname "foo") => [he | hne] ?; first by subst.
    by rewrite /C lookup_insert_ne //= in H0.
  + rewrite /Δ /= lookup_insert_ne //= lookup_insert in H.
    injection H; intros <-; clear H.
    by elim H1.
- econstructor; first by done.
  by rewrite /C lookup_insert //=.
Qed.

(* Sanity checks for fields and inheritance *)
Lemma check_fields_C : fields_incl Δ "C" {["foo" := IntT]}.
Proof.
move => fname h.
by apply C_field in h; subst.
Qed.

Lemma check_fields_D :
  fields_incl Δ "D" (<["foo" := IntT]>{["rec" := ClassT "D"]}).
Proof.
move => fname h.
inversion h; subst; clear h.
- case_eq (string_eq_dec fname "rec") => [hrec | hnrec] hdrec;
    first by subst.
  rewrite /Δ lookup_insert in H.
  injection H; intros <-; clear H.
  by rewrite lookup_insert_ne //= in H0.
- rewrite /Δ lookup_insert in H.
  injection H; intros <-; clear H.
  rewrite /D /= in H1.
  injection H1; intros <-; clear H1.
  by apply C_field in H2; subst.
Qed.

Lemma alloc_unit_class_lemma (h : heap) (new : loc) :
  h !! new = None →
  heap_models γ h -∗ |==>
   heap_models γ (<[ new := ("C", {[ "foo" := IntV 0 ]}) ]> h) ∗
   sem_heap_mapsto new "C" {[ "foo" := Next (interp_type Δ γ IntT)]}.
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
    rewrite /heap_models_fields.
    iSplitR.
    { iPureIntro. by rewrite !dom_insert_L !dom_empty_L. }
    iIntros (f iF).
    rewrite !lookup_insert_Some.
    iIntros "Hf". iDestruct "Hf" as %[ [<- [= <-]]| [? [=]]].
    iExists (IntV 0); iSplit; first by done.
    rewrite interp_type_unfold /= /interp_int.
    by iExists 0.
  - iDestruct ("Hm" with "[]") as (iFs) "[% [%Hidom hisem]]"; first done.
    rewrite /heap_models_fields.
    iExists _. rewrite lookup_insert_ne; last done.
    iSplitR; first by done.
    by iSplitR.
Qed.

End Examples.
