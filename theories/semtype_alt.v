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

Canonical Structure tagO : ofe := leibnizO tag.

(* interpretation of ty *)
Definition sem_typeO (Σ : gFunctors) : ofe := value -d> iPropO Σ.

Class sem_heapG (Σ : gFunctors) : Set := SemHeapG {
  sem_heapG_heap :> inG Σ (gmap_viewR loc (prodO tagO (gmapO string (laterO (sem_typeO Σ)))));
}.

Section proofs.
Context `{!sem_heapG Σ}.
Context (Δ: stringmap classDef).
Notation iProp := (iProp Σ).

Inductive ancestor (target: tag) : tag -> Prop :=
  | ARefl : ancestor target target
  | ASuper current super cdef :
      Δ !! current = Some cdef ->
      cdef.(superclass) = Some super ->
      ancestor target super ->
      ancestor target current
.
Hint Constructors ancestor : core.

Local Notation "A '`inherits`' B" := (ancestor B A) (at level 70, no associativity).

Lemma inherits_trans:
  forall A B C,
  A `inherits` B -> B `inherits` C -> A `inherits` C.
Proof.
  intros A B C h; revert C.
  induction h as [ | current super cdef hin hsuper h hi]; intros C hC; first by done.
  econstructor; [ exact hin | exact hsuper | ].
  now apply hi.
Qed.

(* Note useful, just for sanity check: extends are chains.
 * if A extends B and C, then either B extends C or C extends B.
 *)
Corollary inherits_is_chain:
  forall A B C,
   A `inherits` B -> A `inherits` C->
  (C `inherits` B \/ B `inherits` C).
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

(* has_field fname ty cname checks if the class cname has a field named fname of type ty *)
Inductive has_field (fname: string) (typ: ty): tag -> Prop :=
  | HasField current cdef:
      Δ !! current = Some cdef ->
      cdef.(classfields) !! fname = Some typ ->
      has_field fname typ current
  | InheritsField current parent cdef:
      Δ !! current = Some cdef ->
      cdef.(classfields) !! fname = None ->
      cdef.(superclass) = Some parent ->
      has_field fname typ parent ->
      has_field fname typ current.

Hint Constructors has_field : core.

(* all fields of class cname are in the fnames set *)
Definition has_fields (cname: tag) (fnames: stringmap ty) : Prop :=
  ∀ fname typ, has_field fname typ cname ↔ fnames !! fname = Some typ.

Lemma has_fields_fun: forall c fs0 fs1,
  has_fields c fs0 -> has_fields c fs1 -> fs0 = fs1.
Proof.
move => c fs0 fs1 h0 h1.
apply map_eq => k.
destruct (fs0 !! k) as [ ty | ] eqn:hty.
- destruct (h1 k ty) as [hl1 hr1].
  rewrite hl1 //=.
  by apply h0.
- destruct (fs1 !! k) as [ ty | ] eqn:hty'; last done.
  destruct (h1 k ty) as [hl1 hr1].
  apply h0 in hr1; last done.
  by rewrite hty in hr1.
Qed.

Inductive subtype : ty -> ty -> Prop :=
  | SubMixed : forall ty, subtype ty MixedT
  | SubClass : forall A B, A `inherits` B -> subtype (ClassT A) (ClassT B)
  | SubMixed2: subtype MixedT (UnionT NonNullT NullT)
  | SubIntNonNull: subtype IntT NonNullT
  | SubBoolNonNull: subtype BoolT NonNullT
  | SubClassNonNull: forall A, subtype (ClassT A) NonNullT
  | SubUnionUpper1 : forall s t, subtype s (UnionT s t)
  | SubUnionUpper2 : forall s t, subtype t (UnionT s t)
  (* Do we need this one *)
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
    (∃ ℓ t (fields:stringmap ty),
    ⌜w = LocV ℓ ∧ t `inherits` cname ∧ has_fields t fields⌝ ∗
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

	Lemma gmap_fmap_ne_ext
	{A} {B : ofe} (f1 f2 : A → B) (m : gmap K A) n :
	(∀ (i: K) (x: A), m !! i = Some x -> f1 x ≡{n}≡ f2 x) →
	f1 <$> m ≡{n}≡ f2 <$> m.
	Proof.
		move => Hf i.
		rewrite !lookup_fmap.
		by destruct (m !! i) eqn:?; constructor; eauto.
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
apply gmap_fmap_ne_ext => k ty hin.
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

(* #hyp *)
Global Instance interp_type_persistent : forall t v, Persistent (interp_type t v).
Proof.
elim => [ | | | | cname | | |s hs t ht | s hs t ht] v;
  rewrite interp_type_unfold //=; try by apply _.
- rewrite /interp_union.
  by apply bi.or_persistent; rewrite -!interp_type_unfold.
- rewrite /interp_union.
  by apply bi.and_persistent; rewrite -!interp_type_unfold.
Qed.


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
    split ; first by eapply inherits_trans.
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

Lemma inherits_is_sub: forall C D, D `inherits` C -> (ClassT D) <: (ClassT C).
Proof.  by eauto. Qed.

Lemma interp_type_inherits (l : loc) (C D: tag):
  D `inherits` C ->
  interp_type (ClassT D) (LocV l) -∗
  interp_type (ClassT C) (LocV l).
Proof.
move => hDsubC.
iIntros "h".
iApply subtype_is_inclusion; first by apply inherits_is_sub.
done.
Qed.

(* concrete heaps *)
Definition heap : Type := gmap loc (tag * stringmap value).

(* heap models relation; the semantic heap does
   not appear because it is hidden in iProp  *)
(* Helper defintion to state that fields are correctly modeled *)
Definition heap_models_fields
  (iFs: stringmap (laterO (sem_typeO Σ))) (vs: stringmap value) : iProp :=
  ⌜dom (gset string) vs ≡ dom _ iFs⌝ ∗
  ∀ f (iF: interp),
  iFs !! f ≡ Some (Next iF) -∗ ∃ v, (⌜vs !! f = Some v⌝ ∗ ▷iF v).

Definition heap_models (h : heap) : iProp :=
  ∃ (sh: gmap loc (tag * stringmap (laterO (sem_typeO Σ)))),
    own γ (gmap_view_auth 1 sh) ∗ ⌜dom (gset loc) sh = dom _ h⌝ ∗
    □ ∀ (ℓ : loc) (t : tag) (vs : stringmap value),
      ⌜h !! ℓ = Some (t, vs)⌝ -∗
        ∃ (iFs : stringmap (laterO (sem_typeO Σ))),
        sh !! ℓ ≡ Some (t, iFs) ∗ heap_models_fields iFs vs.
End proofs.

(* Thank you Robbert. TODO: update iris to get it from it *)
Global Instance gmap_dom_ne n `{Countable K} {A : ofe}:
  Proper ((≡{n}@{gmap K A}≡) ==> (=)) (dom (gset K)).
Proof. intros m1 m2 Hm. apply set_eq=> k. by rewrite !elem_of_dom Hm. Qed.

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

Fact C_field : forall fname ty,
  has_field Δ fname ty "C" <-> (fname = "foo" /\ ty = IntT).
Proof.
move => fname typ; split => [hf | [-> ->]].
- inversion hf; subst; clear hf.
  + rewrite /Δ /= lookup_insert_ne //= lookup_insert in H.
    injection H; intros <-; clear H.
    destruct (string_eq_dec fname "foo") as [he | hne] eqn:?.
    { subst; split; first done.
      rewrite /C lookup_insert /= in H0.
      by injection H0.
    }
    by rewrite /C lookup_insert_ne //= in H0.
  + rewrite /Δ /= lookup_insert_ne //= lookup_insert in H.
    injection H; intros <-; clear H.
    by elim H1.
- econstructor; first by done.
  by rewrite /C lookup_insert //=.
Qed.

Fact D_field : forall fname typ,
  has_field Δ fname typ "D" <->
  ((fname = "foo" /\ typ = IntT) \/ (fname = "rec" /\ typ = ClassT "D")).
Proof.
move => f; split => [hf | [ [-> ->] | [-> ->]]].
- inversion hf; subst; clear hf.
  + rewrite /Δ //= lookup_insert in H.
    injection H; intros <-; clear H.
    destruct (string_eq_dec f "foo") as [-> | hne]; first by subst.
    destruct (string_eq_dec f "rec") as [-> | hne2].
    { right; split; first done.
      rewrite /D lookup_insert /= in H0.
      by injection H0.
    }
    by rewrite /C lookup_insert_ne //= in H0.
  + rewrite /Δ //= lookup_insert in H.
    injection H; intros <-; clear H.
    rewrite /D /= in H1.
    injection H1; intros <-; clear H1.
    apply C_field in H2; now subst; left.
- eapply InheritsField; [ done | done | done | by apply C_field].
- econstructor; first by done.
  by rewrite /C lookup_insert //=.
Qed.

(* Sanity checks for fields and inheritance *)
Lemma check_fields_C : has_fields Δ "C" {["foo" := IntT]}.
Proof.
move => f; split => [h | h].
- by apply C_field in h as [-> ->].
- by econstructor.
Qed.

Lemma check_fields_D :
  has_fields Δ "D" ({["foo" := IntT; "rec" := ClassT "D"]}).
Proof.
move => f; split => [h | ].
- inversion h; subst; clear h.
  + destruct (string_eq_dec f "rec") as [-> | hnrec] eqn:hdrec.
    { rewrite lookup_insert_ne //= lookup_insert.
      rewrite /Δ  lookup_insert in H.
      injection H; intros <-; clear H.
      by rewrite /D lookup_insert in H0.
    }
    rewrite /Δ lookup_insert in H.
    injection H; intros <-; clear H.
    by rewrite lookup_insert_ne //= in H0.
  + rewrite /Δ lookup_insert in H.
    injection H; intros <-; clear H.
    rewrite /D /= in H1.
    injection H1; intros <-; clear H1.
    by apply C_field in H2 as [-> ->].
- rewrite lookup_insert_Some => h.
  destruct h as [ [<- <-] | [hne h]].
  { apply D_field; by left. }
  by econstructor.
Qed.

Example alloc_unit_class_lemma (h : heap) (new : loc) :
  h !! new = None →
  heap_models γ h -∗ |==>
   heap_models γ (<[ new := ("C", {[ "foo" := IntV 0 ]}) ]> h) ∗
   sem_heap_mapsto new "C" {[ "foo" := Next (interp_type Δ γ IntT)]}.
Proof.
  move=> Hnew. iIntros "Hm". iDestruct "Hm" as (sh) "[Hown [Hdom #Hm]]".
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
  iModIntro.
  iIntros (ℓ t vs) "Hlook".
  rewrite lookup_insert_Some.
  iDestruct "Hlook" as %[[<- [= <- <-]]|[Hℓ Hlook]].
  - iExists _. rewrite lookup_insert.
    iSplitR; first done.
    rewrite /heap_models_fields.
    iSplitR.
    { iPureIntro. by rewrite !dom_insert_L !dom_empty_L. }
    iIntros (f iF).
    destruct (string_eq_dec f "foo") as [-> | hne]; last first.
    { rewrite !lookup_insert_ne //= !lookup_empty option_equivI.
      by iIntros "hfalse".
    }
    rewrite !lookup_insert option_equivI later_equivI.
    iIntros "Hf".
    iExists (IntV 0); iSplit; first done.
    iNext.
    rewrite discrete_fun_equivI /=.
    iSpecialize ("Hf" $! (IntV 0)).
    iRewrite -"Hf".
    rewrite interp_type_unfold /= /interp_int.
    by iExists 0.
  - iDestruct ("Hm" with "[]") as (iFs) "[Hin [hidom hisem]]"; first done.
    rewrite /heap_models_fields.
    iExists _. rewrite lookup_insert_ne; last done.
    iSplitR; first by done.
    by iSplitR.
Qed.

Remark inheritsD: forall t, ancestor Δ "D" t -> t = "D".
Proof.
move => t h.
inversion h; subst; clear h; first done.
destruct cdef as [classname superclass ? ?]; simpl in *.
destruct (string_eq_dec t "D") as [-> | hne]; first done.
destruct (string_eq_dec t "C") as [-> | hne2].
- rewrite lookup_insert_ne in H; last by done.
  simpl in *.
  rewrite lookup_insert /= in H.
  by injection H; intros; subst; clear H.
- by rewrite !lookup_insert_ne //= in H.
Qed.

Example alloc_unit_class_lemma_rec (h : heap) (l : loc) frag:
  h !! l = Some ("D", frag) →
  interp_type Δ γ (ClassT "D") (LocV l) -∗
  heap_models γ h -∗
  heap_models γ (<[ l := ("D", <["rec" := LocV l]>frag) ]> h).
Proof.
  move => hbefore.
  iIntros "#Hsem Hm".
  iDestruct "Hm" as (sh) "[H● [%Hdom #Hm]]".
  rewrite interp_type_unfold /= /interp_class.
  iDestruct "Hsem" as (???) "[%hh #H◯]".
  destruct hh as [[= <-] [hext hfields]].
  apply inheritsD in hext; subst.
  eapply has_fields_fun in hfields; last by apply check_fields_D.
  destruct (sh !! l)  as [ [t iFs] | ] eqn:Hsh; last first.
  {
    assert (hl : l ∈ dom (gset loc) h); first by apply elem_of_dom.
    assert (hl': l ∉ dom (gset loc) sh); first by apply not_elem_of_dom.
    rewrite Hdom in hl'.
    now elim hl'.
  }
  iDestruct (own_valid_2 with "H● H◯") as "#Hv".
  rewrite gmap_view_both_validI.
  iDestruct "Hv" as "[_ Hsh]".
  rewrite Hsh option_equivI prod_equivI /interp_tys_next /interp_ty_next /=.
  iDestruct "Hsh" as "#[%Heqt Heqi]".
  (* Hm needs to be persistent (hence the □) otherwise
     we would kill it here to get interp_type for l's
     field but we would also need it later to show
     heap_models *)
  iDestruct ("Hm" $! l "D" frag with "[//]") as (?) "[Hsh [%Hdom2 Hvs]]".
  rewrite Hsh option_equivI prod_equivI /=.
  iDestruct "Hsh" as "[%Hl Hr]".
  fold_leibniz.
  rewrite Hl in Hsh.
  clear t Heqt Hl.
  (* we now show heap_models of the new heap *)
  iExists sh. iFrame.
  have -> : dom (gset loc) (<[l:=("D", <["rec":=LocV l]>frag)]>h) = dom _ h.
  { by apply dom_insert_lookup_L. }
  iSplitL; first done.
  iModIntro. iIntros (???) "Hlook".
  rewrite lookup_insert_Some.
  iDestruct "Hlook" as %[[<- [= <- <-]]|[Hℓ Hlook]]; last by iApply "Hm".
  iExists iFs. 
  iSplitL; first by rewrite Hsh.
  rewrite /heap_models_fields.
  iSplit.
  {
    rewrite dom_insert Hdom2.
    iRewrite -"Hr".
    iRewrite "Heqi".
    iPureIntro.
    by set_solver.
  }
  iIntros (f iF) "hIF".
  destruct (string_eq_dec f "rec") as [-> | hf]; last first.
  - rewrite lookup_insert_ne //=.
    iApply "Hvs".
    iRewrite -"hIF".
    by iRewrite "Hr".
  - rewrite lookup_insert.
    iExists (LocV l); iSplitR; first done.
    rewrite gmap_equivI.
    iSpecialize ("Heqi" $! "rec").
    rewrite lookup_fmap.
    rewrite -hfields lookup_insert_ne //= lookup_insert /=.
    iRewrite "Heqi" in "hIF".
    rewrite !option_equivI later_equivI.
    iNext.
    rewrite discrete_fun_equivI.
    iSpecialize ("hIF" $! (LocV l)).
    iRewrite -"hIF".
    rewrite interp_type_unfold /= /interp_class /=.
    iExists _, _, _.
    iSplitR; last done.
    { iPureIntro.
      split; first done.
      split; first by constructor.
      by apply check_fields_D.
    }
Qed.

Definition one_shot_loop_sh : stringmap (laterO (sem_typeO Σ)) :=
  {[
    "foo" := Next (interp_type Δ γ IntT);
    "rec" := Next (interp_type Δ γ (ClassT "D"))
    ]}.

Example one_shot_loop (h : heap) (new : loc):
  h !! new = None →
  heap_models γ h -∗ |==>
      heap_models γ (<[ new := ("D", {[ "foo" := IntV 0; "rec" := LocV new]}) ]> h).
Proof.
  move=> Hl. iIntros "Hh".
  iDestruct "Hh" as (sh) "[H● [%Hdom #Hm]]".
  iMod (own_update with "H●") as "[H● H◯]".
  { apply (gmap_view_alloc _ new DfracDiscarded); last done.
    apply (not_elem_of_dom (D:=gset loc)).
    by rewrite Hdom not_elem_of_dom. }
  iDestruct "H◯" as "#H◯".
  iModIntro. iExists _. iFrame. iSplitR.
  { iPureIntro. rewrite !dom_insert_L.
    by rewrite Hdom. }
  iModIntro. iIntros (l' t' v) "H".
  rewrite lookup_insert_Some.
  iDestruct "H" as %[[<- [= <- <-]]|[??]].
  - iExists one_shot_loop_sh. rewrite lookup_insert.
    rewrite option_equivI /=.
    iSplitR; first done.
    rewrite /heap_models_fields.
    iSplitR; first by iPureIntro.
    iIntros (f iF) "hos".
    rewrite /one_shot_loop_sh.
    destruct (string_eq_dec f "foo") as [-> | hne0].
    { rewrite !lookup_insert /= option_equivI later_equivI.
      iExists (IntV 0); iSplitR; first by iPureIntro.
      iNext.
      rewrite discrete_fun_equivI.
      iSpecialize ("hos" $! (IntV 0)).
      iRewrite -"hos".
      rewrite interp_type_unfold /= /interp_int.
      now iExists 0.
    }
    destruct (string_eq_dec f "rec") as [-> | hne1].
    { rewrite lookup_insert_ne // lookup_insert.
      rewrite lookup_insert_ne // lookup_insert option_equivI later_equivI.
      iExists (LocV new); iSplitR; first by iPureIntro.
      iNext.
      rewrite discrete_fun_equivI.
      iSpecialize ("hos" $! (LocV new)).
      iRewrite -"hos".
      rewrite interp_type_unfold /= /interp_class.
      iExists new, "D", ({["foo" := IntT; "rec" := ClassT "D"]}).
      iSplitR.
      { iPureIntro; split; first done.
        split; first constructor.
        by apply check_fields_D.
      }
      rewrite /interp_tys_next /interp_ty_next /=.
      rewrite !fmap_insert fmap_empty.
      done.
    }
    rewrite !lookup_insert_ne //= lookup_empty.
    rewrite option_equivI.
    done.
  - iDestruct ("Hm" $! l' with "[//]") as (iF) "[??]".
    iExists _. rewrite lookup_insert_ne; last done.
    iSplit; eauto.
Qed.

End Examples.
