From stdpp Require Import base.
From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Import iprop own.
From iris.algebra Require Import ofe cmra gmap_view.
From iris.proofmode Require Import tactics.

Definition tag := positive.
Definition loc := positive.
Inductive value : Set :=
  | UnitV
  | LocV (ℓ : loc).
Canonical Structure valueO : ofe := leibnizO value.

Local Instance value_inhabited : Inhabited value := populate UnitV.

Canonical Structure tagO : ofe := discreteO tag.

(* interpretation of types *)
Definition sem_typeO (Σ : gFunctors) : ofe := value -d> iPropO Σ.

Class sem_heapG (Σ : gFunctors) : Set := SemHeapG {
  sem_heapG_heap :> inG Σ (gmap_viewR loc (prodO tagO (laterO (sem_typeO Σ))));
}.

Inductive lang_ty := 
  | UnitT
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

Definition interp_unit : interp :=
  λ (v : value), ⌜v = UnitV⌝%I.

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
       | UnitT => interp_unit
       | UnionT A B => interp_union (go A) (go B)
       | ClassT t => interp_class t rec
       end) ty.

(* we cannot use solve_contractive out of the box
   because of the 'fix' combinator above *)
Local Instance interp_type_pre_contractive :
  Contractive interp_type_pre.
Proof.
  move=>??? H. elim=>*/=; solve_proper_core
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

(* concrete heaps *)
Definition heap : Type := gmap loc (tag * value).

(* heap models relation; the semantic heap does
   not appear because it is hidden in iProp  *)
Definition heap_models (h : heap) : iProp :=
  ∃ sh,
    own γ (gmap_view_auth 1 sh) ∗ ⌜dom (gset loc) sh = dom _ h⌝ ∗
    ∀ (ℓ : loc) (t : tag) (v : value),
      ⌜h !! ℓ = Some (t, v)⌝ -∗
        ∃ (iF : interp), ⌜sh !! ℓ = Some (t, Next iF)⌝ ∗ iF v.

(* the tag for a class C with a single unit field *)
Definition tC : tag := 1%positive.

Lemma alloc_unit_class_lemma (h : heap) (new : loc) :
  h !! new = None →
  heap_models h -∗ |==>
   heap_models (<[ new := (tC, UnitV) ]> h) ∗
   sem_heap_mapsto new tC (interp_type UnitT).
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
  iIntros (ℓ t v) "Hlook".
  rewrite lookup_insert_Some.
  iDestruct "Hlook" as %[[<- [= <- <-]]|[Hℓ Hlook]].
  - iExists _. rewrite lookup_insert.
    iSplitR; first done.
    rewrite interp_type_unfold /=.
    by rewrite /interp_unit.
  - iDestruct ("Hm" with "[]") as (iF) "[% HiF]"; first done.
    iExists _. rewrite lookup_insert_ne; last done.
    by iSplitR.
Qed.

End proofs.
