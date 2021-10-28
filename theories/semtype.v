From stdpp Require Import base.
From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Import iprop own.
From iris.algebra Require Import ofe cmra gmap_view.

Definition tag := positive.
Definition loc := positive.
Inductive value : Set :=
  | UnitV
  | LocV (ℓ : loc).

Canonical Structure tagO : ofe := discreteO tag.

(* interpretation of types *)
Definition sem_typeO (Σ : gFunctors) : ofe := value -d> iPropO Σ.

Class sem_heapG (Σ : gFunctors) : Set := SemHeapG {
  sem_heapG_inv :> inG Σ (gmap_viewR loc (prodO tagO (laterO (sem_typeO Σ))))
}.

Section proofs.
Context `{sem_heapG Σ}.
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

(* interpret a class type given the tag and the
   interpretation for the unique field type *)
Definition interp_class (γ : gname) (t : tag) (iF : interp) : interp :=
  λ (w : value), (
    ∃ ℓ, ⌜w = LocV ℓ⌝ ∗ own γ (gmap_view_frag ℓ DfracDiscarded (t, Next iF))
  )%I.

From iris.proofmode Require Import tactics.

(* sanity check that the own assertion is persistent *)
Lemma frag_test (γ : gname) (ℓ : loc) x :
  own γ (gmap_view_frag ℓ DfracDiscarded x) -∗
  own γ (gmap_view_frag ℓ DfracDiscarded x) ∗
  own γ (gmap_view_frag ℓ DfracDiscarded x).
Proof.
  iStartProof. iIntros "#Hown". by iSplitL.
Qed.

Fixpoint interp_type (γ : gname) (ty : langty) : interp :=
  match ty with
  | UnitT => interp_unit
  | UnionT A B => interp_union (interp_type γ A) (interp_type γ B)
  | ClassT t F => interp_class γ t (interp_type γ F)
  end.

End proofs.
