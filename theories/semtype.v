From stdpp Require Import base.
From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Import iprop own.
From iris.algebra Require Import ofe cmra gmap_view.

Definition tag := positive.
Definition loc := positive.
Inductive value : Set :=
  | UnitV
  | LocV (ℓ : loc).

(* values need an equivalence relation to be lifted to an ofe;
   just use leibniz' equality *)
Local Instance value_equiv : Equiv value := (=@{value}).

Canonical Structure valueO : ofe := discreteO value.
Canonical Structure tagO : ofe := discreteO tag.

(* interpretation of types *)
Definition sem_typeO (Σ : gFunctors) : ofe :=
  valueO -n> laterO (iPropO Σ).

Class sem_heapG (Σ : gFunctors) : Set := SemHeapG {
  sem_heapG_inv :> inG Σ (gmap_viewR loc (prodO tagO (sem_typeO Σ)))
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
  λne (v : value), Next (⌜v = UnitV⌝)%I.

Definition interp_union (iA : interp) (iB : interp) : interp :=
  λne (w : value), Next (later_car (iA w) ∨
                         later_car (iB w))%I.

(* interpret a class type given the tag and the
   interpretation for the unique field type *)
Definition interp_class (γ : gname) (t : tag) (iF : interp) : interp :=
  λne (w : value), Next (
    ∃ ℓ, ⌜w = LocV ℓ⌝ ∗ own γ (gmap_view_frag ℓ (DfracOwn 1) (t, iF))
  )%I.

Fixpoint interp_type (γ : gname) (ty : langty) : interp :=
  match ty with
  | UnitT => interp_unit
  | UnionT A B => interp_union (interp_type γ A) (interp_type γ B)
  | ClassT t F => interp_class γ t (interp_type γ F)
  end.

End proofs.