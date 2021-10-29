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

Local Instance value_inhabited : Inhabited value := populate UnitV.

Canonical Structure tagO : ofe := discreteO tag.

(* interpretation of types *)
Definition sem_typeO (Σ : gFunctors) : ofe := value -d> iPropO Σ.

Class sem_heapG (Σ : gFunctors) : Set := SemHeapG {
  sem_heapG_heap :> inG Σ (gmap_viewR loc (prodO tagO (laterO (sem_typeO Σ))));
}.

Section proofs.
Context `{!sem_heapG Σ}.
Notation iProp := (iProp Σ).

Inductive langty := 
  | UnitT
  | UnionT (A : langty) (B : langty)
  | ClassT (t : tag) (F : langty).

(* the interpretation of types is simply given by
   the carrier set of the sem_typeO ofe *)
Definition interp := ofe_car (sem_typeO Σ).
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

(* interpret a class type given the tag and the
   interpretation for the unique field type *)
Definition interp_class (t : tag) (iF : interp) : interp :=
  λ (w : value), (∃ ℓ, ⌜w = LocV ℓ⌝ ∗ sem_heap_mapsto ℓ t iF)%I.

Fixpoint interp_type (ty : langty) : interp :=
  match ty with
  | UnitT => interp_unit
  | UnionT A B => interp_union (interp_type A) (interp_type B)
  | ClassT t F => interp_class t (interp_type F)
  end.

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
    by rewrite /= /interp_unit.
  - iDestruct ("Hm" with "[]") as (iF) "[% HiF]"; first done.
    iExists _. rewrite lookup_insert_ne; last done.
    by iSplitR.
Qed.

End proofs.
