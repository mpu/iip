From stdpp Require Import base strings gmap stringmap fin_maps.
From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Import iprop own.
From iris.algebra Require Import ofe cmra gmap_view.
From iris.proofmode Require Import tactics.

Definition tag := string.

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

Definition loc := positive.
Global Instance loc_dec_eq (l l' : loc) : Decision (l = l') := _.

Inductive value : Set :=
  | IntV (z: Z)
  | BoolV (b: bool)
  | NullV
  | LocV (ℓ : loc).
Local Instance value_inhabited : Inhabited value := populate NullV.

(* interpretation of types *)
Definition sem_typeO (Σ : gFunctors) : ofe := value -d> iPropO Σ.

Class sem_heapG (Σ : gFunctors) : Set := SemHeapG {
  sem_heapG_heap :> inG Σ (gmap_viewR loc (prodO tagO (gmapO string (laterO (sem_typeO Σ)))));
}.

Definition tvar := string.

Inductive lang_ty :=
  | IntT
  | BoolT
  | NothingT
  | MixedT
  | ClassT (cname: tag)
  | NullT
  | NonNullT
  | UnionT (s t: lang_ty)
  | InterT (s t: lang_ty)
  | AppT (ty: lang_ty) (tv: tvar) (targ: lang_ty)
  | VarT (tv: tvar)
.
Canonical Structure lang_tyO : ofe := leibnizO lang_ty.

Definition var := string.
Global Instance var_dec_eq (l l' : var) : Decision (l = l') := _.

Inductive primop :=
  | PlusO | MinusO | TimesO | DivO | LeqO | GeqO | EqO
.

Inductive expr :=
  | IntE (z: Z)
  | BoolE (b: bool)
  | NullE
  | OpE (op: primop) (e1: expr) (e2: expr)
  | VarE (v: var)
.

Inductive cmd : Set :=
  | SkipC
  | SeqC (fstc: cmd) (sndc: cmd)
  | LetC (lhs: var) (e: expr)
  | IfC (cond: expr) (thn: cmd) (els: cmd)
  | CallC (lhs: var) (recv: expr) (name: string) (args: stringmap expr)
  | NewC (lhs: var) (class_name: tag) (args: stringmap expr)
  | GetC (lhs: var) (recv: expr) (name: string)
  | SetC (recv: expr) (fld: string) (rhs: expr)
.

Record methodDef := {
  methodname: string;
  methodargs: stringmap lang_ty;
  methodrettype: lang_ty;
  methodbody: cmd;
  methodret: expr;
}.

Record classDef := {
  classname: tag;
  superclass: option tag;
  classgenerics: list tvar; (* TODO: add constraints *)
  classfields : stringmap lang_ty;
  classmethods : stringmap methodDef;
}.

Section proofs.
Context `{!sem_heapG Σ}.
Notation iProp := (iProp Σ).

(* assume a given set of class definitions *)
Context (Δ: stringmap classDef).

(* the interpretation of types is simply given by
   the carrier set of the sem_typeO ofe *)
Notation interpO := (sem_typeO Σ).
Definition interp := ofe_car interpO.
Eval hnf in interp.
(* = value → iPropO Σ *)
(*      : Type *)

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

(* name for the semantic heap *)
Context (γ : gname).

Notation sem_heap_mapsto ℓ t iFs :=
  (own γ (gmap_view_frag ℓ DfracDiscarded (t, iFs))).

Notation ty_interpO := (lang_ty -d> interpO).


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
Definition interp_ty_next (rec: ty_interpO) (typ: lang_ty): laterO interpO :=
  Next (rec typ)
.

Definition interp_tys_next (rec: ty_interpO) (ftys: stringmap lang_ty) : gmapO string (laterO interpO) :=
  (interp_ty_next rec) <$> ftys
.

(* class A extends B *)
Definition extends (A B: tag) : Prop :=
  exists cdef,
  Δ !! A = Some cdef /\
  cdef.(superclass) = Some B
.

(* Refl trans closure of extends *)
Definition inherits := rtc extends.

(* Note useful, just for sanity check: inherits are chains.
 * if A inherits B and C, then either B inherits C or C inherits B.
 *)
Corollary inherits_is_chain:
  forall A B C,
   inherits A B -> inherits A C->
  (inherits C B \/ inherits B C).
Proof.
  intros A B C h; revert C.
  induction h as [ t | x y z hxy hyz hi]; move => c hc; first by right.
   destruct hxy as (cdef & hin & hs).
   destruct hc as [ t | u v w huv hvw].
   - left; econstructor; first by exists cdef. done.
   - destruct huv as (? & hin' & hs').
     rewrite hin' in hin.
     injection hin; intros ->; clear hin hin'.
     rewrite hs' in hs.
     injection hs; intros ->; clear hs hs'.
     apply hi in hvw as [h | h]; first by left.
     by right.
Qed.

(* has_field fname ty cname checks if the class cname has a field named fname of type ty *)
Inductive has_field (fname: string) (typ: lang_ty): tag -> Prop :=
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

(* A class cannot redeclare a field if it is present in
 * any of its parent definition.
 *)
Definition wf_cdef_fields cdef : Prop :=
  forall f fty super,
  cdef.(superclass) = Some super ->
  has_field f fty super ->
  cdef.(classfields) !! f = None.

Definition wf_cdefs (prog: stringmap classDef)  : Prop :=
  map_Forall (fun cname cdef => wf_cdef_fields cdef) prog.

(* all fields of class cname are in the fnames set *)
Definition has_fields (cname: tag) (fnames: stringmap lang_ty) : Prop :=
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

Ltac inv H := inversion H; subst; clear H.

Lemma has_fields_inherits : wf_cdefs Δ -> forall A B, inherits A B ->
  forall f fty, has_field f fty B -> has_field f fty A.
Proof.
move => wfΔ A B h.
induction h as [ t | x y z hxy hyz hi]; move => f fty hf; first done.
apply hi in hf.
destruct hxy as (cdef & hΔ & hs).
apply InheritsField with y cdef; move => //.
apply wfΔ in hΔ.
eapply hΔ; first done.
done.
Qed.

Corollary has_fields_inherits_lookup:
  wf_cdefs Δ ->
  forall A B cdef name fty fields,
  Δ !! B = Some cdef ->
  classfields cdef !! name = Some fty ->
  inherits A B ->
  has_fields A fields ->
  fields !! name = Some fty.
Proof.
  move => wfΔ A B cdef name fty fields hin hfields hinherits hf.
  destruct (hf name fty) as [hl hr].
  apply hl.
  eapply (has_fields_inherits wfΔ); first done.
  econstructor; first done.
  done.
Qed.

(* interpret a class type given the tag and the
   interpretation of their fields *)
Definition interp_class (cname : tag) (rec : ty_interpO) : interp :=
  λ (w : value),
    (∃ ℓ t (fields:stringmap lang_ty),
    ⌜w = LocV ℓ ∧ inherits t cname ∧ has_fields t fields⌝ ∗
    sem_heap_mapsto ℓ t (interp_tys_next rec fields))%I.

Definition interp_app (tyenv: gmap tvar interp) (go: gmap tvar interp → lang_ty → interp)
   (ty:lang_ty) (tv: tvar) (targ: lang_ty) : interp :=
   go (<[tv := go tyenv targ]>tyenv) ty
.

Definition interp_var (tyenv: gmap tvar interp) (tv: tvar) : interp :=
  match tyenv !! tv with
  | Some T => T
  | None => λ(_: value), False%I
  end
.

(* we use a blend of Coq/Iris recursion, the
   Coq recursion lets us handle simple structural
   cases, and we use Iris' recursion to deal with
   the more complicated case of class types *)
Definition interp_type_pre (tyenv: gmap tvar interp) (rec : ty_interpO) : ty_interpO :=
  λ (typ : lang_ty),
    (fix go (tyenv: gmap tvar interp) (typ : lang_ty) : interp :=
       match typ with
       | IntT => interp_int
       | BoolT => interp_bool
       | NothingT => interp_nothing
       | MixedT => interp_mixed
       | ClassT t => interp_class t rec
       | NullT => interp_null
       | NonNullT => interp_nonnull
       | UnionT A B => interp_union (go tyenv A) (go tyenv B)
       | InterT A B => interp_inter (go tyenv A) (go tyenv B)
       | AppT ty tv targ => interp_app tyenv go ty tv targ
       | VarT tv => interp_var tyenv tv
       end) tyenv typ.

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

Lemma interp_type_pre_contractive_env tyenv1 tyenv2 t:
  forall n,
  tyenv1 ≡{n}≡ tyenv2 →
  interp_type_pre tyenv1 t ≡{n}≡ interp_type_pre tyenv2 t.
Proof.
  move => n h ty.
  move: tyenv1 tyenv2 n h.
  elim : ty; intros => //=.
  - rewrite /interp_union => v.
    f_equiv.
    + by rewrite (H tyenv1 tyenv2 n h v).
    + by rewrite (H0 tyenv1 tyenv2 n h v).
  - rewrite /interp_inter => v.
    f_equiv.
    + by rewrite (H tyenv1 tyenv2 n h v).
    + by rewrite (H0 tyenv1 tyenv2 n h v).
  - apply H.
    f_equiv; first by apply H0.
    done.
  - rewrite /interp_var.
    destruct (tyenv1 !! tv) as [ a1 | ] eqn:h1.
    + destruct (tyenv2 !! tv) as [a2 | ] eqn:h2.
      * move:(h tv); rewrite h1 h2.
        by move/Some_dist_inj. 
      * move:(h tv); rewrite h1 h2.
        by inversion 1.
    + destruct (tyenv2 !! tv) as [a2 | ] eqn:h2; last by done.
      move:(h tv); rewrite h1 h2.
      by inversion 1.
Qed.

(* we cannot use solve_contractive out of the box because of
 * the 'fix' combinator above
 *)
Local Instance interp_type_pre_contractive tyenv:
  Contractive (interp_type_pre tyenv).
Proof.
move => n i1 i2 hdist.
move => ty.
move: tyenv.
elim : ty; intros => //=.
(*
    [ (* ClassT *)
    | solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv])
    | solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv])
    | (* VarT *)
    ].
 *)
{
move => v; rewrite /interp_class.
do 3 (f_equiv; intro).
do 4 f_equiv.
rewrite /interp_tys_next /interp_ty_next.
apply gmap_fmap_ne_ext => k ty hin.
f_contractive.
by destruct n.
}
- rewrite /interp_union => v.
  f_equiv.
  + by rewrite (H tyenv v).
  + by rewrite (H0 tyenv v).
- rewrite /interp_inter => v.
  f_equiv.
  + by rewrite (H tyenv v).
  + by rewrite (H0 tyenv v).
- specialize H0 with tyenv.
  transitivity (interp_type_pre (<[tv:=interp_type_pre tyenv i2 targ]> tyenv) i1 ty).
  + apply interp_type_pre_contractive_env.
    by f_equiv.
  + by apply H.
Qed.

Record TyEnv := {
  tvmap :> gmap tvar interp;
  _ : ∀ tv iF v, tvmap !! tv = Some iF → Persistent (iF v)
  }
.
(* the interpretation of types can now be
   defined as a fixpoint (because class types
   can be (mutually) recursive) *)
Definition interp_type (tyenv: TyEnv) := fixpoint (interp_type_pre tyenv).

Lemma interp_type_unfold tyenv (ty : lang_ty) (v : value) :
  interp_type tyenv ty v ⊣⊢ interp_type_pre tyenv (interp_type tyenv) ty v.
Proof.
  rewrite {1}/interp_type.
  apply (fixpoint_unfold (interp_type_pre tyenv) ty v).
Qed.

Lemma interp_type_pre_persistent : forall (P: ty_interpO)
  (_: forall t v, Persistent (P t v))
  t (tyenv:stringmap interp)  v,
  (∀ tv iF v, tyenv !! tv = Some iF → Persistent (iF v)) →
  Persistent (interp_type_pre tyenv P t v).
Proof.
  move => P hP.
  elim => [ | | | | cname | | |s hs t ht | s hs t ht | ty hty tv targ htarg| tv] tyenv v htyenv;
      try by apply _.
  - simpl.
    apply hty => tv0 iF w hin.
    rewrite -> lookup_insert_Some in hin.
    destruct hin as [[<- <-] | [hne hin]]; first by apply htarg.
    eapply htyenv.
    by apply hin.
  - rewrite /= /interp_var.
    destruct (tyenv !! tv) as [w | ] eqn:hw; rewrite hw; last by apply _.
    eapply htyenv.
    by apply hw.
Qed.

(* #hyp *)
Global Instance interp_type_persistent : forall tyenv t v,
  Persistent (interp_type tyenv t v).
Proof.
  move => [tyenv htyenv].
  rewrite /interp_type.
  apply fixpoint_ind.
  - move => x y hxy h t v.
    generalize (hxy t v).
    move => hh.
    by rewrite <- hh.
  - exists (λ (_: lang_ty) (_: value), True%I).
    by apply _.
  - move => x hx t v.
    by apply interp_type_pre_persistent.
  - apply limit_preserving_forall => ty.
    apply limit_preserving_forall => v.
    apply bi.limit_preserving_Persistent.
    move => n x y hxy.
    by move : (hxy ty v).
Qed.

(*
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
 *)

Lemma dom_interp_tys_next (tyenv: TyEnv) fields:
  dom stringset (interp_tys_next (interp_type tyenv) fields) ≡ dom _ fields.
Proof. by rewrite /interp_tys_next /interp_ty_next dom_fmap. Qed.

Inductive subtype : lang_ty -> lang_ty -> Prop :=
  | SubMixed : forall ty, subtype ty MixedT
  | SubClass : forall A B, inherits A B -> subtype (ClassT A) (ClassT B)
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


(* A <: B -> ΦA ⊂ ΦB *)
Theorem subtype_is_inclusion_aux:
  forall A B, A <: B →
  forall v tyenv tyenv',
  (forall tv iF, tyenv !! tv = Some iF → forall v, iF v -∗ interp_mixed v) →
  interp_type_pre tyenv (interp_type tyenv') A v -∗
  interp_type_pre tyenv (interp_type tyenv') B v.
Proof.
induction 1 as [A | A B hext | | | | A | A B| A B | A B C h0 hi0 h1 hi1
  | A B | A B | A B C h0 hi0 h1 hi1 | A | A B C h0 hi0 h1 hi1 ];
      move => v tyenv tyenv' htyenv /=.
- rewrite /interp_mixed.
  elim: A v tyenv tyenv' htyenv => /=.
  + move => v _ _ _; iIntros "h"; by repeat iLeft.
  + move => v _ _ _; iIntros "h"; by iLeft; iRight; iLeft.
  + move => v _ _ _; by rewrite /interp_nothing; iIntros "h".
  + done.
  + rewrite /interp_class => v cname tyenv tyenv' _.
    iIntros "h".
    iDestruct "h" as (ℓ t fields) "[%h0 h1]".
    destruct h0 as [-> [hext hfields]].
    iLeft.
    iRight.
    iRight.
    by iExists _, _, _; iFrame.
  + move => v _ _ _; iIntros "h"; by iRight.
  + move => v _ _ _; by iIntros "h"; iLeft.
  + move => s hs t ht v tyenv tyenv' htyenv.
    rewrite /interp_union.
    iIntros "h".
    iDestruct "h" as "[ h | h ]"; first by iApply hs.
    by iApply ht.
  + move => s hs t ht v tyenv tyenv' htyenv.
    rewrite /interp_inter.
    iIntros "h".
    iDestruct "h" as "[? _]"; by iApply hs.
  + move => ty hty tv targ htarg v tyenv tyenv' htyenv.
    rewrite /interp_app.
    iIntros "h".
    iApply hty; last by iApply "h".
    rewrite /interp_mixed => k iF hk w; iIntros "hiF".
    rewrite -> lookup_insert_Some in hk.
    destruct hk as [[<- <-] | [hne hin]]; first by iApply htarg.
    by iApply htyenv.
  + rewrite /interp_var => tv v tyenv _ htyenv.
    destruct (tyenv !! tv) as [ty | ] eqn:hty; last by iIntros.
    iIntros "h".
    by iApply htyenv.
- rewrite /interp_class.
  iIntros "h".
  iDestruct "h" as (ℓ t fields) "[%h hsem]".
  destruct h as [-> [hext2 hfields ]].
  iExists ℓ, t, fields.
  iSplit.
  { iPureIntro; split; first by done.
    split; last done.
    by eapply rtc_transitive.
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
  iIntros "[h | h]"; first by iApply hi0.
  by iApply hi1.
- rewrite /interp_inter.
  by iIntros "[? _]".
- rewrite /interp_inter.
  by iIntros "[_ ?]".
- rewrite /interp_inter.
  iIntros "h".
  iSplit; first by iApply hi0.
  by iApply hi1.
- done.
- iIntros "h".
  iApply hi1; first done.
  by iApply hi0.
Qed.

Theorem subtype_is_inclusion:
  forall A B, A <: B →
  forall v (tyenv: TyEnv),
  (forall tv iF, tvmap tyenv !! tv = Some iF → forall v, iF v -∗ interp_mixed v) →
  interp_type tyenv A v -∗ interp_type tyenv B v.
Proof.
  move => A B hAB v tyenv htyenv.
  rewrite !interp_type_unfold.
  by iApply subtype_is_inclusion_aux.
Qed.

(* language statics & semantics *)

Definition local_tys := stringmap lang_ty.

Inductive expr_has_ty (lty : local_tys) :
    expr → lang_ty → Prop :=
  | IntTy : forall z, expr_has_ty lty (IntE z) IntT
  | BoolTy: forall b, expr_has_ty lty (BoolE b) BoolT
  | NullTy: expr_has_ty lty NullE NullT
  | OpIntTy: forall op e1 e2,
      match op with
      | PlusO | MinusO | TimesO | DivO => True
          | _ => False
      end → 
      expr_has_ty lty e1 IntT →
      expr_has_ty lty e2 IntT →
      expr_has_ty lty (OpE op e1 e2) IntT
  | OpBoolTy: forall op e1 e2,
      match op with
      | LeqO | GeqO | EqO => True
      | _ => False
      end → 
      expr_has_ty lty e1 IntT →
      expr_has_ty lty e2 IntT →
      expr_has_ty lty (OpE op e1 e2) BoolT
  | VarTy: forall v ty,
      lty !! v = Some ty →
      expr_has_ty lty (VarE v) ty
.

(* continuation-based typing for commands *)
Inductive cmd_has_ty :
    local_tys → cmd → local_tys → Prop :=
  | SkipTy: forall lty, cmd_has_ty lty SkipC lty
  | SeqTy: forall lty1 lty2 lty3 fstc sndc,
      cmd_has_ty lty1 fstc lty2 →
      cmd_has_ty lty2 sndc lty3 →
      cmd_has_ty lty1 (SeqC fstc sndc) lty3
  | LetTy: forall lty lhs e ty,
      expr_has_ty lty e ty →
      cmd_has_ty lty (LetC lhs e) (<[lhs := ty]>lty)
  | IfTy: forall lty1 lty2 cond thn els,
      expr_has_ty lty1 cond BoolT →
      cmd_has_ty lty1 thn lty2 →
      cmd_has_ty lty1 els lty2 →
      cmd_has_ty lty1 (IfC cond thn els) lty2
  | GetTy: forall lty lhs recv t name cdef fty,
      expr_has_ty lty recv (ClassT t) →
      Δ !! t = Some cdef →
      cdef.(classfields) !! name = Some fty →
      cmd_has_ty lty (GetC lhs recv name) (<[lhs := fty]>lty)
  | SetTy: forall lty recv fld rhs fty t,
      expr_has_ty lty recv (ClassT t) →
      expr_has_ty lty rhs fty →
      has_field fld fty t → (* TODO: subtyping ? *)
      cmd_has_ty lty (SetC recv fld rhs) lty
  | NewTy: forall lty lhs t args fields,
      has_fields t fields →
      dom (gset string) fields = dom _ args →
      (forall f fty arg,
        fields !! f = Some fty →
        args !! f = Some arg →
        expr_has_ty lty arg fty) →
      cmd_has_ty lty (NewC lhs t args) (<[ lhs := ClassT t]>lty)
  | CallTy: forall lty1 lty2 lhs recv t name args cdef mdef,
      expr_has_ty lty1 recv (ClassT t) →
      Δ !! t = Some cdef →
      cdef.(classmethods) !! name = Some mdef →
      dom (gset string) mdef.(methodargs) = dom _ args →
      (forall x ty arg,
      mdef.(methodargs) !! x = Some ty →
      args !! x = Some arg →
      expr_has_ty lty1 arg ty) →
      cmd_has_ty lty1 mdef.(methodbody) lty2 →
      expr_has_ty lty2 mdef.(methodret) mdef.(methodrettype) →
      cmd_has_ty lty1 (CallC lhs recv name args) (<[ lhs := mdef.(methodrettype)]>lty1)
.

(* Big set reduction *)
Definition primop_eval (op: primop) : Z -> Z -> value :=
  match op with
  | PlusO => fun x y => IntV (x + y)
  | MinusO => fun x y => IntV (x - y)
  | TimesO => fun x y => IntV (x * y)
  | DivO => fun x y => IntV (x / y)
  | LeqO => fun x y => BoolV (Z.leb x y)
  | GeqO => fun x y => BoolV (Z.geb x y)
  | EqO => fun x y => BoolV (Z.eqb x y)
  end
.

Definition local_env := gmap var value.

Fixpoint expr_eval (le : local_env) (e: expr) : option value :=
  match e with
  | IntE z => Some (IntV z)
  | BoolE b => Some (BoolV b)
  | NullE => Some NullV
  | OpE op e1 e2 =>
      match expr_eval le e1, expr_eval le e2 with 
      | Some (IntV z1), Some (IntV z2) => Some (primop_eval op z1 z2)
      | _, _ => None
      end
  | VarE v => le !! v
  end
.

(* concrete heaps *)
Definition heap : Type := gmap loc (tag * stringmap value).

Definition map_args {A B: Type} (f: A → option  B) (m: stringmap A) : option (stringmap B) :=
  guard (map_Forall (λ _ x, is_Some (f x)) m); Some (omap f m)
.

Lemma dom_map_args: forall A B (f: A → option B)
  (m: stringmap A) (n: stringmap B),
  map_args f m = Some n -> 
  dom stringset n = dom _ m.
Proof.
  rewrite /map_args => A B f m n h.
  case_option_guard; last done.
  injection h; intros <-; clear h.
  rewrite -> map_Forall_lookup in H.
  apply set_eq => x; split; move/elem_of_dom => hx; apply elem_of_dom.
  - rewrite lookup_omap in hx.
    destruct hx as [v hv]; by apply bind_Some in hv as [a [-> ha]].
  - destruct hx as [v hv].
    rewrite lookup_omap hv.
    by apply H in hv.
Qed.

Lemma map_args_lookup: forall A B (f: A → option B) (m: stringmap A) n,
  map_args f m = Some n →
  forall k, n !! k = (m !! k) ≫= f.
Proof.
  rewrite /map_args => A B f m n h k.
  case_option_guard; last done.
  injection h; intros <-; clear h.
  rewrite -> map_Forall_lookup in H.
  by rewrite lookup_omap.
Qed.
  
Inductive cmd_eval:
    (local_env * heap) → cmd →
    (local_env * heap) → Prop :=
  | SkipEv : forall st, cmd_eval st SkipC st
  | LetEv: forall le h v e val,
      expr_eval le e = Some val →
      cmd_eval (le, h) (LetC v e) (<[v:=val]> le, h)
  | NewEv: forall le h lhs new t args vargs,
      h !! new = None →
      map_args (expr_eval le) args = Some vargs →
      cmd_eval (le, h) (NewC lhs t args) (<[lhs := LocV new]>le, <[new := (t, vargs)]>h)
  | GetEv: forall le h lhs recv name l t vs v,
      expr_eval le recv = Some (LocV l) →
      h !! l = Some (t, vs) →
      vs !! name = Some v →
      cmd_eval (le, h) (GetC lhs recv name) (<[lhs := v]>le, h)
  | SetEv: forall le h recv fld rhs l v t vs vs',
      expr_eval le recv = Some (LocV l) →
      expr_eval le rhs = Some v →
      h !! l = Some (t, vs) →
      vs' = <[ fld := v ]>vs →
      cmd_eval (le, h) (SetC recv fld rhs) (le, <[l := (t, vs')]> h)
  | SeqEv: forall st1 st2 st3 fstc sndc,
      cmd_eval st1 fstc st2 →
      cmd_eval st2 sndc st3 →
      cmd_eval st1 (SeqC fstc sndc) st3
  | IfTrueEv: forall st1 st2 cond thn els,
      expr_eval st1.1 cond = Some (BoolV true) →
      cmd_eval st1 thn st2 →
      cmd_eval st1 (IfC cond thn els) st2
  | IfFalseEv: forall st1 st2 cond thn els,
      expr_eval st1.1 cond = Some (BoolV false) →
      cmd_eval st1 els st2 →
      cmd_eval st1 (IfC cond thn els) st2
  | CallEv: forall le h h' lhs recv l t vs name args vargs cdef mdef
      run_env run_env' ret,
      expr_eval le recv = Some (LocV l) →
      map_args (expr_eval le) args = Some vargs →
      h !! l = Some (t, vs) →
      Δ !! t = Some cdef →
      cdef.(classmethods) !! name = Some mdef →
      <["$this" := LocV l]>vargs = run_env →
      cmd_eval (run_env, h) mdef.(methodbody) (run_env', h') →
      expr_eval run_env' mdef.(methodret) = Some ret →
      cmd_eval (le, h) (CallC lhs recv name args) (<[lhs := ret]>le, h')
.

(* heap models relation; the semantic heap does
   not appear because it is hidden in iProp  *)
(* Helper defintion to state that fields are correctly modeled *)
Definition heap_models_fields
  (iFs: gmapO string (laterO (sem_typeO Σ))) (vs: stringmap value) : iProp :=
  ⌜dom (gset string) vs ≡ dom _ iFs⌝ ∗
  ∀ f (iF: interp),
  iFs !! f ≡ Some (Next iF) -∗ ∃ v, (⌜vs !! f = Some v⌝ ∗ ▷iF v).

Lemma heap_models_fields_ext_L: forall iFs iFs' vs,
  iFs ≡ iFs' -∗ heap_models_fields iFs vs -∗ heap_models_fields iFs' vs.
Proof.
  move => iFs iFs' vs.
  iIntros "heq h".
  rewrite /heap_models_fields.
  iDestruct "h" as "[%hdom h]".
  iSplit.
  { rewrite gmap_equivI.
    fold_leibniz.
    rewrite set_eq hdom.
    iIntros (s).
    rewrite !elem_of_dom.
    by iRewrite ("heq" $! s).
  }
  iIntros (f iF) "hiF".
  iApply "h".
  by iRewrite "heq".
Qed.

Definition heap_models (h : heap) : iProp :=
  ∃ (sh: gmap loc (prodO tagO (gmapO string (laterO (sem_typeO Σ))))),
    own γ (gmap_view_auth 1 sh) ∗ ⌜dom (gset loc) sh = dom _ h⌝ ∗
    □ ∀ (ℓ : loc) (t : tag) (vs : stringmap value),
      ⌜h !! ℓ = Some (t, vs)⌝ -∗
        ∃ (iFs : gmapO string (laterO (sem_typeO Σ))),
        sh !! ℓ ≡ Some (t, iFs) ∗ heap_models_fields iFs vs.

Definition interp_local_tys
  tyenv (lty : local_tys) (le : local_env) : iProp :=
  (∀ v ty, ⌜lty !! v = Some ty⌝ -∗
           ∃ val, ⌜le !! v = Some val⌝ ∗ interp_type tyenv ty val)%I.

(*
Lemma expr_typ_inv e le lty (h: heap) l t t0 vs:
  (* missing link between le lty *)
  expr_eval le e = Some (LocV l) →
  h !! l = Some (t, vs) →
  expr_has_ty lty e (ClassT t0) →
  inherits t t0.
Proof.
  case: e => [z | b | | op e1 e2 | v] //=.
  - destruct (expr_eval le e1) as [[z1| ? | | ?] | ] eqn:h1; move => //=.
    destruct (expr_eval le e2) as [[z2| ? | | ?] | ] eqn:h2; move => //=.
    move => [= hl] hh hexpr.
    by inv hexpr.
  - move => hle hh hexpr.
    inv hexpr.
 *)


Lemma expr_adequacy tyenv e lty le ty val :
  expr_eval le e = Some val →
  expr_has_ty lty e ty →
  interp_local_tys tyenv lty le -∗
  interp_type tyenv ty val.
Proof.
  (* the language is this simple that no
     induction is necessary *)
  case: e => [z | b | | op e1 e2 | v] /=.
  - move => [= <-] hexpr.
    inv hexpr.
    iIntros "_"; rewrite interp_type_unfold.
    by iExists _.
  - move => [= <-] hexpr.
    inv hexpr.
    iIntros "_"; rewrite interp_type_unfold.
    by iExists _.
  - move => [= <-] hexpr.
    inv hexpr.
    iIntros "_"; by rewrite interp_type_unfold.
  - destruct (expr_eval le e1) as [[z1| ? | | ?] | ] eqn:h1; move => //=.
    destruct (expr_eval le e2) as [[z2| ? | | ?] | ] eqn:h2; move => //=.
    move => [= <-] hexpr.
    inv hexpr.
    + iIntros "hty".
      rewrite interp_type_unfold /= /interp_int.
      destruct op; by eauto.
    + iIntros "hty".
      rewrite interp_type_unfold /= /interp_bool.
      destruct op; by eauto.
  - move => hle hexpr.
    inv hexpr.
    iIntros "#Hlty". (* CHECKPOINT *)
    iDestruct ("Hlty" with "[//]") as (?) "[% H]".
    rewrite hle in H; injection H; intros <-; clear H.
    done.
Qed.

Lemma interp_local_tys_update tyenv v lty le ty val :
  interp_local_tys tyenv lty le -∗
  interp_type tyenv ty val -∗
  interp_local_tys tyenv (<[v:=ty]>lty) (<[v:=val]>le).
Proof.
  iIntros "#Hi #?". iIntros (v' ty') "H".
  rewrite lookup_insert_Some.
  iDestruct "H" as %[[<- <-]|[??]].
  - iExists _. rewrite lookup_insert. by iSplit.
  - rewrite lookup_insert_ne; last done. by iApply "Hi".
Qed.

Lemma heap_models_lookup tyenv l h A vs t :
  h !! l = Some (t, vs) →
  heap_models h -∗
  interp_type tyenv (ClassT A) (LocV l) -∗
  ∃ fields, heap_models h ∗
    ⌜inherits t A ∧ has_fields t fields⌝ ∗
    ∀ f fty, ⌜fields !! f = Some fty⌝ → 
    ∃ v, ⌜vs !! f = Some v⌝ ∗
    ▷ interp_type tyenv fty v.
Proof.
  move => hheap.
  iIntros "hmodels hl".
  rewrite interp_type_unfold /= /interp_class.
  iDestruct "hl" as (???) "[%H H◯]".
  destruct H as [[= <-] [hinherits hf]].
  iDestruct "hmodels" as (sh) "(H● & % & #Hh)".
  iDestruct (own_valid_2 with "H● H◯") as "#Hv".
  rewrite gmap_view_both_validI.
  iDestruct "Hv" as "[_ HΦ]".
  iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
  iRewrite "H" in "HΦ".
  rewrite option_equivI prod_equivI /=.
  iDestruct "HΦ" as "[-> HΦ]".
  iExists fields.
  iSplitL. { iExists _. iFrame. by iSplit. }
  iSplitR; first by rewrite H0.
  iIntros (f fty) "%hfield".
  iDestruct "H▷" as "[%hdf h]".
  rewrite gmap_equivI.
  iSpecialize ("HΦ" $! f).
  rewrite /interp_tys_next /interp_ty_next lookup_fmap hfield /=.
  iAssert (⌜is_Some (iFs !! f)⌝)%I as "%hiFs".
  { destruct (iFs !! f) eqn:hh; first done.
    by rewrite hh option_equivI.
  }
  destruct hiFs as [[iF] hIF].
  iDestruct ("h" $! f iF with "[]") as (v) "[%hv hl]"; first by rewrite hIF.
  iExists v; iSplitR; first done.
  rewrite hIF option_equivI later_equivI discrete_fun_equivI.
  iNext.
  iSpecialize ("HΦ" $! v).
  by iRewrite -"HΦ".
Qed.

Lemma heap_models_fields_update iFs vs f v (Φ : interpO)
  `{∀ v, Persistent (Φ v)} :
  iFs !! f = Some (Next Φ) ->
  heap_models_fields iFs vs -∗
  Φ v -∗
  heap_models_fields iFs (<[ f := v]>vs).
Proof.
  move => hf.
  iIntros "hm hΦ".
  iDestruct "hm" as "[%hdom h]".
  rewrite /heap_models_fields.
  iSplitR.
  { iPureIntro.
    rewrite dom_insert_lookup //.
    by rewrite -elem_of_dom hdom elem_of_dom hf.
  }
  iIntros (f' iF) "hf".
  destruct (decide (f = f')) as [-> | hne].
  - rewrite lookup_insert.
    iExists v; iSplitR; first done.
    rewrite hf option_equivI later_equivI discrete_fun_equivI.
    iNext.
    iSpecialize ("hf" $! v).
    by iRewrite -"hf".
  - rewrite lookup_insert_ne //.
    by iApply "h".
Qed.

Lemma heap_models_update tyenv h l t t0 vs f v fty:
  wf_cdefs Δ ->
  h !! l = Some (t, vs) ->
  has_field f fty t0 ->
  inherits t t0 ->
  heap_models h -∗
  interp_type tyenv (ClassT t0) (LocV l) -∗
  interp_type tyenv fty v -∗
  heap_models (<[l:=(t, (<[f := v]>vs))]> h).
Proof.
  move => wfΔ hheap hf hinherits.
  iIntros "hmodels #hl #hv".
  iDestruct "hmodels" as (sh) "[hown [%hdom #h]]".
  iExists sh.
  rewrite interp_type_unfold /= /interp_class.
  iDestruct "hl" as (?? fields) "[%H hsem]".
  destruct H as [[= <-] [ hinherits' hfields]].
  iDestruct (own_valid_2 with "hown hsem") as "#Hv".
  rewrite gmap_view_both_validI.
  iDestruct "Hv" as "[_ Hv]".
  iSplitL; first by iFrame.
  iSplitR.
  { iPureIntro.
    by rewrite hdom dom_insert_lookup_L.
  }
  iModIntro.
  iIntros (ℓ t' vs') "%Heq".
  destruct (decide (l = ℓ)) as [-> | hne].
  - rewrite lookup_insert in Heq.
    injection Heq; intros <- <-; clear Heq.
    iAssert (t1 ≡ t)%I as "%Ht".
    { iSpecialize ("h" $! ℓ t vs with "[//]").
      iDestruct "h" as (iFs) "[hsh hmodels]".
      iRewrite "Hv" in "hsh".
      rewrite !option_equivI prod_equivI /=.
      by iDestruct "hsh" as "[? ?]".
    }
    iExists _; iSplitR.
    { rewrite Ht.
      by iRewrite "Hv".
    }
    iApply heap_models_fields_update; first by apply interp_type_persistent.
    + rewrite /interp_tys_next /interp_ty_next lookup_fmap.
      destruct (hfields f fty) as [h0 h1].
      rewrite h0; first by done.
      by apply has_fields_inherits with t0.
    + iSpecialize ("h" $! ℓ t vs with "[//]").
      iDestruct "h" as (iFs) "[hsh hmodels]".
      iRewrite "Hv" in "hsh".
      rewrite !option_equivI prod_equivI /=.
      iDestruct "hsh" as "[? h]".
      iApply heap_models_fields_ext_L; first by iRewrite "h".
      done.
    + done.
  - iApply "h".
    iPureIntro.
    by rewrite lookup_insert_ne // in Heq.
Qed.

Notation "|=▷^ n Q" := (Nat.iter n (λ P, |==> ▷ P) Q)%I
  (at level 99, n at level 9, Q at level 200,
   format "|=▷^ n  Q") : bi_scope.

Lemma updN_zero (Q : iProp) : (|=▷^0 Q) ⊣⊢ Q.
Proof. done. Qed.

Lemma updN_S n (Q : iProp) :
  (|=▷^(S n) Q) ⊣⊢ |==> ▷ |=▷^n Q.
Proof. done. Qed.

Lemma updN_mono n (P Q : iProp) :
  (P -∗ Q) → (|=▷^n P) -∗ (|=▷^n Q).
Proof.
  elim: n => [//|n HI H].
  rewrite !updN_S.
  iApply bupd_mono.
  iApply bi.later_mono.
  by iApply HI.
Qed.

Lemma cmd_adequacy tyenv lty lty' st cmd st' :
  wf_cdefs Δ →
  cmd_eval st cmd st' →
  cmd_has_ty lty cmd lty' →
  ∃ n,
    heap_models st.2 ∗ interp_local_tys tyenv lty st.1 -∗ |=▷^n
    heap_models st'.2 ∗ interp_local_tys tyenv lty' st'.1.
Proof.
  move=> wfΔ E. move: lty lty'. elim: E.
  - move => ? lty lty' hty.
    inv hty.
    by exists 0.
  - move=> le h lhs recv val hrecv /=.
    exists 0. iIntros "[? #Hle]".
    rewrite updN_zero. iFrame.
    inv H.
    iDestruct (expr_adequacy with "Hle") as "#?"; try done.
    by iApply interp_local_tys_update.
  - move => le h lhs new t args vargs hnew hargs lty lty' hc /=.
    inv hc.
    exists 1. iIntros "[Hh #Hle]".
    (* we need one modality to update the
       semantic heap *)
    rewrite updN_S updN_zero.
    iDestruct "Hh" as (sh) "(H●&Hdom&#Hh)".
    iDestruct "Hdom" as %Hdom.
    iMod (own_update with "H●") as "[H● H◯]".
    { apply (gmap_view_alloc _ new DfracDiscarded
        (t, interp_tys_next (interp_type tyenv) fields)); last done.
      apply (not_elem_of_dom (D:=gset loc)).
      by rewrite Hdom not_elem_of_dom. }
    iIntros "!> !>". iDestruct "H◯" as "#H◯".
    iAssert (interp_type tyenv (ClassT t) (LocV new))
      with "[]" as "#Hl".
    { rewrite interp_type_unfold /=.
      iExists _, _, _. by iSplit. }
    iSplitL; last first.
    by iApply interp_local_tys_update.
    iExists _. iFrame. iSplit.
    by rewrite !dom_insert_L Hdom.
    iModIntro. iIntros (???) "Hlook".
    rewrite lookup_insert_Some.
    iDestruct "Hlook" as %[[<- [= <- <-]]|[Hℓ Hlook]].
    + iExists _. rewrite lookup_insert.
      iSplitR; first done.
      rewrite /heap_models_fields.
      iSplitR.
      { 
        apply dom_map_args in hargs.
        by rewrite dom_interp_tys_next hargs H5.
      }
      iIntros (f iF) "hiF".
      iAssert (⌜f ∈ dom stringset fields⌝)%I as "%hf".
      {
        rewrite -(dom_interp_tys_next tyenv) elem_of_dom.
        rewrite /interp_tys_next /interp_ty_next.
        rewrite !lookup_fmap.
        by iRewrite "hiF".
      }
      assert (h0: is_Some (args !! f)).
      {
        apply elem_of_dom.
        by rewrite -H5.
      }
      destruct h0 as [a0 ha0].
      assert (h1: is_Some (vargs !! f)).
      {
        apply elem_of_dom.
        apply dom_map_args in hargs.
        by rewrite hargs -H5.
      }
      destruct h1 as [v0 hv0].
      assert (h2: is_Some (fields !! f)) by (by apply elem_of_dom).
      destruct h2 as [fty hty].
      iExists v0; iSplitR; first done.
      rewrite /interp_tys_next /interp_ty_next lookup_fmap.
      assert (heval0: expr_eval le a0 = Some v0).
      { rewrite (map_args_lookup _ _ _ args vargs hargs f) in hv0.
        by rewrite ha0 in hv0.
      }
      assert (hty0: expr_has_ty lty a0 fty) by (by apply H6 with f).
      rewrite hty /= option_equivI later_equivI.
      iNext.
      rewrite discrete_fun_equivI.
      iSpecialize ("hiF" $! v0).
      iRewrite -"hiF".
      by iDestruct (expr_adequacy tyenv a0 with "Hle") as "#Ha0".
    + rewrite lookup_insert_ne; last done.
      by iApply "Hh".
  - move => le h hls recv name l t vs v hle hh hvs lty lty' hc.
    inv hc.
    exists 1. iIntros "[Hh #Hle]". simpl.
    iModIntro. (* keep the later *)
    iDestruct (expr_adequacy with "Hle") as "#He"; try done.
    iDestruct (heap_models_lookup with "Hh He") as (fields) "(Hh&Ht&Hv)"; first done.
    iDestruct "Ht" as %[? ?].
    rewrite bi.later_sep.
    iSplitL "Hh"; first done.
    assert (hf: fields !! name = Some fty) by (by apply (has_fields_inherits_lookup wfΔ) with t t0 cdef).
    iDestruct ("Hv" $! name fty hf) as (w) "[%hw hi]".
    rewrite hvs in hw; injection hw; intros ->; clear hw.
    iNext. by iApply interp_local_tys_update.
  - move => le h recv fld rhs l v t vs vs' hrecv hrhs hh -> lty lty' hcmd.
    inv hcmd.
    exists 0.
    iIntros "[Hh #Hle]".
    rewrite updN_zero /=. iSplitL; last done.
    iDestruct (expr_adequacy tyenv recv with "Hle") as "#Hrecv" => //.
    iDestruct (expr_adequacy tyenv rhs with "Hle") as "#Hrhs" => //.
    iDestruct (heap_models_lookup with "Hh Hrecv") as (fields) "(Hh&Ht&?)"; first done.
    iDestruct "Ht" as %[? ?].
    by iApply (heap_models_update with "Hh").
  - move => st1 st2 st3 fstc sndc hcfst hfst hcsnd hsnd lty lty' h.
    inv h.
    apply hfst in H2. apply hsnd in H4.
    clear hfst hsnd.
    destruct H2 as [n1 Hfst].
    destruct H4 as [n2 Hsnd].
    exists (n1 + n2).
    iIntros "H".
    iDestruct (Hfst with "H") as "H".
    iPoseProof (updN_mono with "H") as "H";
      first done.
    by rewrite Nat_iter_add.
  - move => st1 st2 cond thn els hexpr hcthn hi hcels hels h.
    inv h.
    apply hi in H5. clear hi.
    destruct H5 as [n Hifc]. exists n.
    iIntros "H". iPoseProof (Hifc with "H") as "H".
    done.
  - move => st1 st2 cond thn els hexpr hcthn hi hcels hels h.
    inv h.
    apply hi in H6. clear hi.
    destruct H6 as [n Helc]. exists n.
    iIntros "H". iPoseProof (Helc with "H") as "H".
    done.
  - move => le h h' lhs recv l t vs name args vargs cdef mdef run_env
    run_env' ret hrecv hargs hh hΔ hcdef <- hbody hi hret lty lty' hc.
    inv hc.
    (* t should inherits t0 *)
    (* WIP *)
    (* Need stuff about methods like we did properties (override, ...) *)
    admit.
Admitted.
    
(* Thank you Robbert. TODO: update iris to get it from it *)
Global Instance gmap_dom_ne n `{Countable K} {A : ofe}:
  Proper ((≡{n}@{gmap K A}≡) ==> (=)) (dom (gset K)).
Proof. intros m1 m2 Hm. apply set_eq=> k. by rewrite !elem_of_dom Hm. Qed.

Print Assumptions cmd_adequacy.
