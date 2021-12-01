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

(* Naive method lookup: methods are unique *)
Inductive has_method (mname: string) (mdef: methodDef): tag -> Prop :=
  | HasMethod current cdef:
      Δ !! current = Some cdef →
      cdef.(classmethods) !! mname = Some mdef →
      has_method mname mdef current
  | InheritsMethod current parent cdef:
      Δ !! current = Some cdef →
      cdef.(classmethods) !! mname = None →
      cdef.(superclass) = Some parent →
      has_method mname mdef parent →
      has_method mname mdef current
.

Hint Constructors has_method : code.

Lemma has_method_from m mdef A:
  has_method m mdef A →
  ∃B cdef, Δ !! B = Some cdef ∧ cdef.(classmethods) !! m = Some mdef ∧
  inherits A B.
Proof.
  induction 1 as [ current cdef hΔ hm | current parent cdef hΔ hm hs h hi];
      first by exists current, cdef.
  destruct hi as (B & cdef' & hΔ' & hm' & hinherits). 
  exists B, cdef'; repeat split => //.
  econstructor; last by apply hinherits.
  by exists cdef.
Qed.

(* A class cannot redeclare a field if it is present in
 * any of its parent definition.
 *)
Definition wf_cdef_fields cdef : Prop :=
  forall f fty super,
  cdef.(superclass) = Some super ->
  has_field f fty super ->
  cdef.(classfields) !! f = None.

Definition wf_cdef_methods cdef : Prop :=
  forall m mdef super,
  cdef.(superclass) = Some super →
  has_method m mdef super →
  cdef.(classmethods) !! m = None.

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

Definition has_methods (cname: tag) (mdefs: stringmap methodDef) : Prop :=
  ∀ mname mdef, has_method mname mdef cname ↔ mdefs !! mname = Some mdef.

Ltac inv H := inversion H; subst; clear H.

Lemma has_method_fun: forall c name mdef0 mdef1,
  has_method name mdef0 c → has_method name mdef1 c → mdef0 = mdef1.
Proof.
move => c name mdef0 mdef1 h; move: mdef1.
induction h as [ current cdef hΔ hm | current parent cdef hΔ hm hs hp hi ].
- move => mdef1 h1; inv h1.
  + rewrite hΔ in H; injection H; intros; subst; clear hΔ H.
    rewrite hm in H0; by injection H0.
  + rewrite hΔ in H; injection H; intros; subst; clear hΔ H.
    rewrite hm in H0; discriminate H0.
- move => mdef1 h1; inv h1.
  + rewrite hΔ in H; injection H; intros; subst; clear hΔ H.
    rewrite hm in H0; discriminate H0.
  + rewrite hΔ in H; injection H; intros; subst; clear hΔ H.
    rewrite hs in H1; injection H1; intros; subst; clear hs H1.
    by apply hi.
Qed.

Lemma has_methods_fun: forall c mdef0 mdef1,
  has_methods c mdef0 → has_methods c mdef1 → mdef0 = mdef1.
Proof.
move => c mdef0 mdef1 h0 h1.
apply map_eq => k.
destruct (mdef0 !! k) as [ ty | ] eqn:hty.
- destruct (h1 k ty) as [hl1 hr1].
  rewrite hl1 //=.
  by apply h0.
- destruct (mdef1 !! k) as [ ty | ] eqn:hty'; last done.
  destruct (h1 k ty) as [hl1 hr1].
  apply h0 in hr1; last done.
  by rewrite hty in hr1.
Qed.

Lemma has_field_inherits : map_Forall (fun _ => wf_cdef_fields) Δ -> forall A B, inherits A B ->
  forall f fty, has_field f fty B -> has_field f fty A.
Proof.
move => wfΔ A B h.
induction h as [ t | x y z hxy hyz hi]; move => f fty hf; first done.
apply hi in hf.
destruct hxy as (cdef & hΔ & hs).
apply InheritsField with y cdef; move => //.
apply wfΔ in hΔ.
by eapply hΔ.
Qed.

Corollary has_fields_inherits_lookup:
  map_Forall (fun _ => wf_cdef_fields) Δ →
  forall A B name fty fields,
  has_field name fty B →
  inherits A B →
  has_fields A fields →
  fields !! name = Some fty.
Proof.
  move => wfΔ A B name fty fields hfields hinherits hf.
  destruct (hf name fty) as [hl hr].
  apply hl.
  by eapply (has_field_inherits wfΔ).
Qed.

Lemma has_method_inherits : map_Forall (fun _ => wf_cdef_methods) Δ -> forall A B, inherits A B ->
  forall m mdef, has_method m mdef B -> has_method m mdef A.
Proof.
move => wfΔ A B h.
induction h as [ t | x y z hxy hyz hi]; move => m mdef hf; first done.
apply hi in hf.
destruct hxy as (cdef & hΔ & hs).
apply InheritsMethod with y cdef; move => //.
apply wfΔ in hΔ.
by eapply hΔ.
Qed.

Corollary has_methods_inherits_lookup:
  map_Forall (fun _ => wf_cdef_methods) Δ →
  forall A B name mdef methods,
  has_method name mdef B →
  inherits A B →
  has_methods A methods →
  methods !! name = Some mdef.
Proof.
  move => wfΔ A B name fty methods hmethods hinherits hf.
  destruct (hf name fty) as [hl hr].
  apply hl.
  by eapply (has_method_inherits wfΔ).
Qed.

(* interpret a class type given the tag and the
   interpretation of their fields *)
Definition interp_class (cname : tag) (rec : ty_interpO) : interp :=
  λ (w : value),
    (∃ ℓ t (fields:stringmap lang_ty),
    ⌜w = LocV ℓ ∧ inherits t cname ∧ has_fields t fields⌝ ∗
    sem_heap_mapsto ℓ t (interp_tys_next rec fields))%I.

(* we use a blend of Coq/Iris recursion, the
   Coq recursion lets us handle simple structural
   cases, and we use Iris' recursion to deal with
   the more complicated case of class types *)
Definition interp_type_pre (rec : ty_interpO) : ty_interpO :=
  λ (typ : lang_ty),
    (fix go (typ : lang_ty) : interp :=
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
Local Instance interp_type_pre_contractive:
  Contractive (interp_type_pre).
Proof.
move => n i1 i2 hdist.
move => ty.
elim : ty; intros => //=;
    [ (* ClassT *)
    | solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv])
    | solve_proper_core ltac:(fun _ => first [done | f_contractive | f_equiv])
    ].
{
move => v; rewrite /interp_class.
do 3 (f_equiv; intro).
do 4 f_equiv.
rewrite /interp_tys_next /interp_ty_next.
apply gmap_fmap_ne_ext => k ty hin.
f_contractive.
by destruct n.
}
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

Lemma dom_interp_tys_next fields:
  dom stringset (interp_tys_next interp_type fields) ≡ dom _ fields.
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
  forall v,
  interp_type_pre interp_type A v -∗
  interp_type_pre interp_type B v.
Proof.
induction 1 as [A | A B hext | | | | A | A B| A B | A B C h0 hi0 h1 hi1
  | A B | A B | A B C h0 hi0 h1 hi1 | A | A B C h0 hi0 h1 hi1 ];
      move => v /=.
- rewrite /interp_mixed.
  elim: A v => /=.
  + move => v; iIntros "h"; by repeat iLeft.
  + move => v; iIntros "h"; by iLeft; iRight; iLeft.
  + move => v; by rewrite /interp_nothing; iIntros "h".
  + done.
  + rewrite /interp_class => v cname.
    iIntros "h".
    iDestruct "h" as (ℓ t fields) "[%h0 h1]".
    destruct h0 as [-> [hext hfields]].
    iLeft.
    iRight.
    iRight.
    by iExists _, _, _; iFrame.
  + move => v; iIntros "h"; by iRight.
  + move => v; by iIntros "h"; iLeft.
  + move => s hs t ht v.
    rewrite /interp_union.
    iIntros "h".
    iDestruct "h" as "[ h | h ]"; first by iApply hs.
    by iApply ht.
  + move => s hs t ht v.
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
  iApply hi1.
  by iApply hi0.
Qed.

Theorem subtype_is_inclusion:
  forall A B, A <: B →
  forall v,
  interp_type A v -∗ interp_type B v.
Proof.
  move => A B hAB v.
  rewrite !interp_type_unfold.
  by iApply subtype_is_inclusion_aux.
Qed.

(* language statics & semantics *)

Definition local_tys := stringmap lang_ty.

Definition is_bool_op op : bool :=
  match op with
  | LeqO | GeqO | EqO => true
  | PlusO | MinusO | TimesO | DivO => false
  end
.

Inductive expr_has_ty (lty : local_tys) :
    expr → lang_ty → Prop :=
  | IntTy : forall z, expr_has_ty lty (IntE z) IntT
  | BoolTy: forall b, expr_has_ty lty (BoolE b) BoolT
  | NullTy: expr_has_ty lty NullE NullT
  | OpIntTy: forall op e1 e2,
      is_bool_op op = false →
      expr_has_ty lty e1 IntT →
      expr_has_ty lty e2 IntT →
      expr_has_ty lty (OpE op e1 e2) IntT
  | OpBoolTy: forall op e1 e2,
      is_bool_op op = true →
      expr_has_ty lty e1 IntT →
      expr_has_ty lty e2 IntT →
      expr_has_ty lty (OpE op e1 e2) BoolT
  | VarTy: forall v ty,
      lty !! v = Some ty →
      expr_has_ty lty (VarE v) ty
  | ESubTy: forall e s t,
      expr_has_ty lty e s →
      s <: t →
      expr_has_ty lty e t
.

(* Inversion lemmas *)
Lemma inv_expr_has_ty_int lty z T: expr_has_ty lty (IntE z) T → IntT <: T.
Proof.
assert(hgen: ∀ lty e T, expr_has_ty lty e T → ∀ z, e = IntE z → IntT <: T).
{
  clear lty z T.
  move => lty e T.
  elim => [ z | | | | | | expr A B h hi hsub ] w hw //=.
  apply hi in hw.
  by apply SubTrans with A.
}
move => h; eapply hgen; first by apply h.
reflexivity.
Qed.

Lemma inv_expr_has_ty_bool lty b T: expr_has_ty lty (BoolE b) T → BoolT <: T.
Proof.
assert(hgen: ∀ lty e T, expr_has_ty lty e T → ∀ b, e = BoolE b → BoolT <: T).
{
  clear lty b T.
  move => lty e T.
  elim => [ | b | | | | | expr A B h hi hsub ] w hw //=.
  apply hi in hw.
  by apply SubTrans with A.
}
move => h; eapply hgen; first by apply h.
reflexivity.
Qed.

Lemma inv_expr_has_ty_null lty T: expr_has_ty lty NullE T → NullT <: T.
Proof.
assert(hgen: ∀ lty e T, expr_has_ty lty e T → e = NullE → NullT <: T).
{
  clear lty  T.
  move => lty e T.
  elim  => [ | | | | | | expr A B h hi hsub ]  hw //=.
  apply hi in hw.
  by apply SubTrans with A.
}
move => h; eapply hgen; first by apply h.
done.
Qed.

Lemma inv_expr_has_ty_op lty op e1 e2 T:
  expr_has_ty lty (OpE op e1 e2) T →
  if is_bool_op op then BoolT <: T else IntT <: T.
Proof.
assert(hgen: ∀ lty e T, expr_has_ty lty e T → ∀ op e1 e2, e = OpE op e1 e2 →
  if is_bool_op op then BoolT <: T else IntT <: T
 ).
{
  clear lty op e1 e2 T.
  move => lty e T.
  elim => [ | | | op e1 e2 hop he1 _ he2 _ | op e1 e2 hop he1 _ he2 _| |
     expr A B h hi hsub ]
      op' e1' e2' heq //=.
  - injection heq; intros; subst; clear heq.
    by rewrite /is_bool_op; destruct op'.
  - injection heq; intros; subst; clear heq.
    by rewrite /is_bool_op; destruct op'.
  - apply hi in heq.
    destruct is_bool_op; by apply SubTrans with A.
}
move => h; eapply hgen; first by apply h.
reflexivity.
Qed. 

Lemma inv_expr_has_ty_var lty v T: expr_has_ty lty (VarE v) T →
  ∃ T0, lty !! v = Some T0 ∧ T0 <: T.
Proof.
assert(hgen: ∀ lty e T, expr_has_ty lty e T → ∀ v, e = VarE v →
  ∃ T0, lty !! v = Some T0 ∧ T0 <: T).
{
  clear lty v T.
  move => lty e T.
  elim => [ | | | | | v ty hin | expr A B h hi hsub ] w hw //=.
  - injection hw; intros <-; clear hw. 
    exists ty; by split.
  - apply hi in hw.
    destruct hw as (T0 & hin & hsub').
    exists T0; split; first done.
    by apply SubTrans with A.
}
move => h; eapply hgen; first by apply h.
reflexivity.
Qed.
  

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
  | GetTy: forall lty lhs recv t name fty,
      expr_has_ty lty recv (ClassT t) →
      has_field name fty t →
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
  | CallTy: forall lty lhs recv t name mdef args,
      expr_has_ty lty recv (ClassT t) →
      has_method name mdef t →
      dom (gset string) mdef.(methodargs) = dom _ args →
      (forall x ty arg,
        mdef.(methodargs) !! x = Some ty →
        args !! x = Some arg →
        expr_has_ty lty arg ty) →
      cmd_has_ty lty (CallC lhs recv name args) (<[lhs := mdef.(methodrettype)]>lty)
.

Definition wf_mdef_ty t mdef :=
  ∃ lty,
  cmd_has_ty (<["$this" := ClassT t]>mdef.(methodargs)) mdef.(methodbody) lty ∧
  expr_has_ty lty mdef.(methodret) mdef.(methodrettype)
.

Definition wf_cdefs (prog: stringmap classDef)  : Prop :=
  map_Forall (fun cname => wf_cdef_fields) prog
  ∧ map_Forall (fun cname => wf_cdef_methods) prog
  ∧
  map_Forall (fun cname cdef =>
    map_Forall (fun mname mdef => wf_mdef_ty cname mdef) cdef.(classmethods)) prog
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

Lemma map_args_empty: forall A B (f: A → option B),
  map_args f ∅ = Some ∅.
Proof.
  rewrite /map_args => A B f /=.
  case_option_guard; first by rewrite omap_empty.
  elim: H.
  apply map_Forall_lookup => i x h; discriminate h.
Qed.

Lemma map_args_update: forall A B (f: A → option B) k a m n,
  map_args f m = Some n →
  map_args f (<[ k := a]> m) =
  match f a with
  | Some b => Some (<[ k := b]> n)
  | None => None
  end.
Proof.
  rewrite /map_args => A B f k a m n h/=.
  case_option_guard; last done.
  injection h; intros <-; clear h.
  case_option_guard.
  - rewrite map_Forall_lookup in H0.
    specialize H0 with k a.
    rewrite lookup_insert in H0.
    destruct H0 as [ b hb ]; first by done.
    rewrite hb.
    f_equal.
    by apply omap_insert_Some.
  - destruct (f a) as [b | ] eqn:hb; last done.
    elim: H0 => i x h.
    rewrite lookup_insert_Some in h.
    destruct h as [[<- <-] | [hne hin]]; first by rewrite hb.
    rewrite map_Forall_lookup in H.
    now apply H in hin.
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
  | CallEv: forall le h h' lhs recv l t vs name args vargs mdef
      run_env run_env' ret,
      expr_eval le recv = Some (LocV l) →
      map_args (expr_eval le) args = Some vargs →
      h !! l = Some (t, vs) →
      has_method name mdef t →
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
    own γ (gmap_view_auth (DfracOwn 1) sh) ∗ ⌜dom (gset loc) sh = dom _ h⌝ ∗
    □ ∀ (ℓ : loc) (t : tag) (vs : stringmap value),
      ⌜h !! ℓ = Some (t, vs)⌝ -∗
        ∃ (iFs : gmapO string (laterO (sem_typeO Σ))),
        sh !! ℓ ≡ Some (t, iFs) ∗ heap_models_fields iFs vs.

Definition interp_local_tys
  (lty : local_tys) (le : local_env) : iProp :=
  (∀ v ty, ⌜lty !! v = Some ty⌝ -∗
           ∃ val, ⌜le !! v = Some val⌝ ∗ interp_type ty val)%I.

Lemma expr_adequacy e lty le ty val :
  expr_eval le e = Some val →
  expr_has_ty lty e ty →
  interp_local_tys lty le -∗
  interp_type ty val.
Proof.
  (* the language is this simple that no
     induction is necessary *)
  case: e => [z | b | | op e1 e2 | v] /=.
  - move => [= <-] hexpr.
    apply inv_expr_has_ty_int in hexpr.
    iIntros "_".
    iApply subtype_is_inclusion; first by apply hexpr.
    rewrite interp_type_unfold.
    by iExists _.
  - move => [= <-] hexpr.
    apply inv_expr_has_ty_bool in hexpr.
    iIntros "_".
    iApply subtype_is_inclusion; first by apply hexpr.
    rewrite interp_type_unfold.
    by iExists _.
  - move => [= <-] hexpr.
    apply inv_expr_has_ty_null in hexpr.
    iIntros "_".
    iApply subtype_is_inclusion; first by apply hexpr.
    by rewrite interp_type_unfold.
  - destruct (expr_eval le e1) as [[z1| ? | | ?] | ] eqn:h1; move => //=.
    destruct (expr_eval le e2) as [[z2| ? | | ?] | ] eqn:h2; move => //=.
    move => [= <-] hexpr.
    apply inv_expr_has_ty_op in hexpr; iIntros "hty".
    destruct op;
    ( iApply subtype_is_inclusion; [by apply hexpr |
      rewrite interp_type_unfold; by eauto]).
  - move => hle hexpr.
    apply inv_expr_has_ty_var in hexpr.
    destruct hexpr as (T0 & hin & hsub').
    iIntros "#Hlty".
    iDestruct ("Hlty" with "[//]") as (?) "[% H]".
    rewrite hle in H; injection H; intros <-; clear H.
    iApply subtype_is_inclusion; first by apply hsub'.
    done.
Qed.

Lemma expr_adequacy2 e lty le ty val :
  expr_eval le e = Some val →
  expr_has_ty lty e ty →
  interp_local_tys lty le -∗
  interp_type ty val.
Proof.
  move => he h; move: le val he.
  elim: h => [z | b | | op e1 e2 hop he1 hi1 he2 hi2 |
      op e1 e2 hop he1 hi1 he2 hi2 |
      v vty hv | exp S T hS hi hsub ] le val he; iIntros "#Hlty".
  - inv he; rewrite interp_type_unfold /=; by eauto.
  - inv he; rewrite interp_type_unfold /=; by eauto.
  - inv he; rewrite interp_type_unfold /=; by eauto.
  - inv he.
    case heq1 : (expr_eval le e1) => [v1 | ]; rewrite heq1 in H0; last by done.
    apply hi1 in heq1.
    iDestruct (heq1 with "Hlty") as "hv1".
    rewrite interp_type_unfold /=.
    iDestruct "hv1" as (z1) "%hz1".
    rewrite hz1 in H0.
    case heq2 : (expr_eval le e2) => [v2 | ]; rewrite heq2 in H0; last by done.
    apply hi2 in heq2.
    iDestruct (heq2 with "Hlty") as "hv2".
    rewrite interp_type_unfold /=.
    iDestruct "hv2" as (z2) "%hz2".
    rewrite hz2 in H0.
    case: H0 => <-.
    rewrite interp_type_unfold /= /interp_int.
    move: hop; rewrite /is_bool_op; destruct op => //= _; by iExists _.
  - inv he.
    case heq1 : (expr_eval le e1) => [v1 | ]; rewrite heq1 in H0; last by done.
    apply hi1 in heq1.
    iDestruct (heq1 with "Hlty") as "hv1".
    rewrite interp_type_unfold /=.
    iDestruct "hv1" as (z1) "%hz1".
    rewrite hz1 in H0.
    case heq2 : (expr_eval le e2) => [v2 | ]; rewrite heq2 in H0; last by done.
    apply hi2 in heq2.
    iDestruct (heq2 with "Hlty") as "hv2".
    rewrite interp_type_unfold /=.
    iDestruct "hv2" as (z2) "%hz2".
    rewrite hz2 in H0.
    case: H0 => <-.
    rewrite interp_type_unfold /= /interp_bool.
    move: hop; rewrite /is_bool_op; destruct op => //= _; by iExists _.
  - inv he.
    iDestruct ("Hlty" with "[//]") as (?) "[% H]".
    rewrite H0 in H; by case: H => ->.
  - apply hi in he.
    iApply subtype_is_inclusion; first by apply hsub.
    by iApply he.
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

Lemma interp_local_tys_weaken_ty v A B lty le:
  lty !! v = Some A →
  A <: B →
  interp_local_tys lty le -∗
  interp_local_tys (<[v := B]> lty) le.
Proof.
  move => hin hAB; iIntros "H".
  rewrite /interp_local_tys.
  iIntros (w ty) "%Hin".
  rewrite lookup_insert_Some in Hin.
  destruct Hin as [[<- <-]|[hne Hin]].
  - iSpecialize ("H" $! v A).
    iDestruct ("H" with "[//]") as (val) "[%Hin #h]".
    iExists val; iSplitR; first done.
    by iApply subtype_is_inclusion.
  - iSpecialize ("H" $! w ty).
    iDestruct ("H" with "[//]") as (val) "[%Hin' #h]".
    iExists val; by iSplitR.
Qed.

Lemma interp_local_tys_update_weaken v A B lty le:
  A <: B →
  interp_local_tys (<[v := A]> lty) le -∗
  interp_local_tys (<[v := B]> lty) le.
Proof.
  move => hAB; iIntros "H".
  replace (<[v:=B]>lty) with (<[v:=B]> (<[v:=A]> lty)); last by rewrite insert_insert.
  iApply interp_local_tys_weaken_ty; try done.
  by rewrite lookup_insert.
Qed.

Lemma interp_local_tys_list lty le targs args vargs:
  dom stringset targs = dom stringset args →
  map_args (expr_eval le) args = Some vargs →
  (∀ (x : string) (ty : lang_ty) (arg : expr),
       targs !! x = Some ty →
       args !! x = Some arg →
       expr_has_ty lty arg ty) →
  interp_local_tys lty le -∗
  interp_local_tys targs vargs.
Proof.
  move => hdom hargs helt.
  iIntros "#Hle" (v ty) "%hin".
  assert (ha: ∃ arg, args !! v = Some arg).
  { apply elem_of_dom.
    rewrite -hdom.
    apply elem_of_dom.
    now rewrite hin.
  }
  destruct ha as [arg harg].
  apply helt with v ty arg in hin; last done.
  assert (hv: ∃ varg, vargs !! v = Some varg).
  { apply elem_of_dom.
    apply dom_map_args in hargs.
    rewrite hargs.
    apply elem_of_dom.
    now rewrite harg.
  }
  destruct hv as [varg hvarg].
  iExists varg; rewrite hvarg; iSplitR; first done.
  rewrite (map_args_lookup _ _ _ args vargs hargs v) harg /= in hvarg.
  by iApply expr_adequacy.
Qed.

Lemma heap_models_lookup l h A vs t :
  h !! l = Some (t, vs) →
  heap_models h -∗
  interp_type (ClassT A) (LocV l) -∗
  ∃ fields, heap_models h ∗
    ⌜inherits t A ∧ has_fields t fields⌝ ∗
    ∀ f fty, ⌜fields !! f = Some fty⌝ → 
    ∃ v, ⌜vs !! f = Some v⌝ ∗
    ▷ interp_type fty v.
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

Lemma heap_models_update h l t t0 vs f v fty:
  wf_cdefs Δ ->
  h !! l = Some (t, vs) ->
  has_field f fty t0 ->
  inherits t t0 ->
  heap_models h -∗
  interp_type (ClassT t0) (LocV l) -∗
  interp_type fty v -∗
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
      apply has_field_inherits with t0 => //.
      now apply wfΔ.
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
  elim: n => [//|n HI H /=].
  iApply bupd_mono.
  iApply bi.later_mono.
  by iApply HI.
Qed.

Lemma updN_mono_I n (P Q : iProp) :
  (P -∗ Q) -∗ (|=▷^n P) -∗ (|=▷^n Q).
Proof.
  elim: n => [|n hi]; first done.
  iIntros "H".
  rewrite !updN_S.
  iIntros "HH".
  iMod "HH".
  iModIntro.
  iNext.
  by iApply (hi with "H").
Qed.

Lemma updN_intro n (P: iProp) : P -∗ (|=▷^n P).
Proof.
  elim: n => [// | n hi /=].
  iIntros "p".
  iApply bupd_intro.
  apply bi.later_mono in hi.
  by iApply hi.
Qed.

Lemma updN_sep n (P R: iProp) : ((|=▷^n P) ∗ (|=▷^n R)) -∗ |=▷^n (P ∗ R).
Proof.
  elim: n => [// | n hi /=].
  iIntros "[H0 H1]".
  iMod "H0".
  iMod "H1".
  iModIntro.
  iNext.
  iApply hi.
  by iSplitL "H0".
Qed.

Lemma updN_frame_r n (P R: iProp) : (|=▷^n P) ∗ R -∗ |=▷^n P ∗ R.
Proof.
  elim: n => [// | n hi /=].
  iIntros "[H HR]".
  iMod "H"; iModIntro.
  iNext.
  iApply hi.
  by iSplitL "H".
Qed.

Lemma cmd_adequacy st cmd st' :
  wf_cdefs Δ →
  cmd_eval st cmd st' →
  ∃ n,
  forall lty lty', cmd_has_ty lty cmd lty' →
    heap_models st.2 ∗ interp_local_tys lty st.1 -∗ |=▷^n
    heap_models st'.2 ∗ interp_local_tys lty' st'.1.
Proof.
  move=> wfΔ.
  elim.
  - move => ?; exists 0 => lty lty' hty.
    by inv hty.
  - move=> le h lhs recv val hrecv /=.
    exists 0 => lty lty' hc; iIntros "[? #Hle]".
    rewrite updN_zero. iFrame.
    inv hc.
    iDestruct (expr_adequacy with "Hle") as "#?"; try done.
    by iApply interp_local_tys_update.
  - move => le h lhs new t args vargs hnew hargs /=.
    exists 1 => lty lty' hc.
    inv hc.
    iIntros "[Hh #Hle]".
    (* we need one modality to update the
       semantic heap *)
    rewrite updN_S updN_zero.
    iDestruct "Hh" as (sh) "(H●&Hdom&#Hh)".
    iDestruct "Hdom" as %Hdom.
    iMod (own_update with "H●") as "[H● H◯]".
    { apply (gmap_view_alloc _ new DfracDiscarded
        (t, interp_tys_next interp_type fields)); last done.
      apply (not_elem_of_dom (D:=gset loc)).
      by rewrite Hdom not_elem_of_dom. }
    iIntros "!> !>". iDestruct "H◯" as "#H◯".
    iAssert (interp_type (ClassT t) (LocV new))
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
        rewrite -dom_interp_tys_next elem_of_dom.
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
      by iDestruct (expr_adequacy a0 with "Hle") as "#Ha0".
    + rewrite lookup_insert_ne; last done.
      by iApply "Hh".
  - move => le h hls recv name l t vs v hle hh hvs.
    exists 1 => lty lty' hc.
    inv hc.
    iIntros "[Hh #Hle]". simpl.
    iModIntro. (* keep the later *)
    iDestruct (expr_adequacy with "Hle") as "#He"; try done.
    iDestruct (heap_models_lookup with "Hh He") as (fields) "(Hh&Ht&Hv)"; first done.
    iDestruct "Ht" as %[? ?].
    rewrite bi.later_sep.
    iSplitL "Hh"; first done.
    assert (hf: fields !! name = Some fty).
    { apply has_fields_inherits_lookup with t t0 => //.
      by apply wfΔ.
    }
    iDestruct ("Hv" $! name fty hf) as (w) "[%hw hi]".
    rewrite hvs in hw; injection hw; intros ->; clear hw.
    iNext. by iApply interp_local_tys_update.
  - move => le h recv fld rhs l v t vs vs' hrecv hrhs hh ->.
    exists 0 => lty lty' hcmd.
    inv hcmd.
    iIntros "[Hh #Hle]".
    rewrite updN_zero /=. iSplitL; last done.
    iDestruct (expr_adequacy recv with "Hle") as "#Hrecv" => //.
    iDestruct (expr_adequacy rhs with "Hle") as "#Hrhs" => //.
    iDestruct (heap_models_lookup with "Hh Hrecv") as (fields) "(Hh&Ht&?)"; first done.
    iDestruct "Ht" as %[? ?].
    by iApply (heap_models_update with "Hh").
  - move => st1 st2 st3 fstc sndc hcfst hfst hcsnd hsnd.
    destruct hfst as [n1 h1].
    destruct hsnd as [n2 h2].
    exists (n1 + n2) => lty lty' hc.
    inv hc.
    apply h1 in H2.
    apply h2 in H4.
    iIntros "H".
    iDestruct (H2 with "H") as "H".
    iPoseProof (updN_mono with "H") as "H";
      first done.
    by rewrite Nat_iter_add.
  - move => st1 st2 cond thn els hexpr hcthn hi.
    destruct hi as [n Hifc]. exists n => lty lty' hc.
    inv hc.
    iIntros "H".
    by iPoseProof (Hifc with "H") as "H".
  - move => st1 st2 cond thn els hexpr hcthn hi.
    destruct hi as [n Helc]. exists n => lty lty' hc.
    inv hc.
    iIntros "H".
    by iPoseProof (Helc with "H") as "H".
  - move => le h h' lhs recv l t vs name args vargs mdef run_env run_env'
    ret hrecv hargs hl hmdef <- hmbody hi hmret.
    destruct hi as [nbody hi].
    exists nbody => lty lty' hc.
    inv hc; simpl in *.
    iIntros "[Hh #Hle]".
    iDestruct (expr_adequacy recv with "Hle") as "#Hrecv" => //.
    iAssert (⌜inherits t t0⌝)%I as "%Hinherits".
    { rewrite interp_type_unfold /= /interp_class.
      iDestruct "Hrecv" as (? t1 ?) "[%hpure Hsem]".
      destruct hpure as [[= <-] [hinherits ?]].
      iDestruct "Hh" as (sh) "(H● & % & #Hh)".
      iDestruct (own_valid_2 with "H● Hsem") as "#Hv".
      rewrite gmap_view_both_validI.
      iDestruct "Hv" as "[_ HΦ]".
      iDestruct ("Hh" with "[//]") as (?) "[H H▷]".
      iRewrite "H" in "HΦ".
      rewrite option_equivI prod_equivI /=.
      by iDestruct "HΦ" as "[-> HΦ]".
    }
    replace mdef0 with mdef in *; last first.
    { eapply has_method_inherits in Hinherits; [ | by apply wfΔ | by apply H6 ].
      by eapply has_method_fun.
    }
    iAssert (
    heap_models h ∗
     interp_local_tys (<["$this":=ClassT t0]> (methodargs mdef))
       (<["$this":=LocV l]> vargs))%I with "[Hh]" as "H".
    { iFrame.
      iApply interp_local_tys_update; last done.
      by iApply interp_local_tys_list.
    }
    assert (wfbody: ∃B, wf_mdef_ty B mdef ∧ inherits t0 B).
    { destruct wfΔ as (? & ? & hbodies).
      rewrite map_Forall_lookup in hbodies.
      apply has_method_from in H6.
      destruct H6 as (B & cdef & hB & hm & hin).
      apply hbodies in hB.
      rewrite map_Forall_lookup in hB.
      apply hB in hm.
      exists B; split; first done.
      by eapply rtc_transitive.
    }
    destruct wfbody as (B & (lty' & hb & hr) & hB).
    apply hi in hb.
    iAssert ( heap_models h ∗
     interp_local_tys (<["$this":=ClassT B]> (methodargs mdef))
     (<["$this":=LocV l]> vargs))%I with "[H]" as "H".
    { iDestruct "H" as "[H #Hsem]".
      iFrame.
      iApply interp_local_tys_update_weaken; last done.
      apply SubClass.
      by eapply rtc_transitive.
    }
    iPoseProof (hb with "H") as "H".
    iRevert "H".
    iApply updN_mono_I.
    iIntros "[Hh #Hlty]".
    iFrame.
    iApply interp_local_tys_update; first done.
    by iDestruct (expr_adequacy (methodret mdef) with "Hlty") as "#Hret".
Qed.

Print Assumptions cmd_adequacy.

Lemma updN_plus n1 (P: iProp) : forall n2,
  (|=▷^n1 P) -∗ (|=▷^(n1 + n2) P).
Proof.
  elim:n1 => [ | n1 hi] /= => n2; iIntros "h1"; first by iApply updN_intro.
  iMod "h1".
  iModIntro.
  iNext.
  by iApply hi.
Qed.


(* Thank you Robbert. TODO: update iris to get it from it *)
Global Instance gmap_dom_ne n `{Countable K} {A : ofe}:
  Proper ((≡{n}@{gmap K A}≡) ==> (=)) (dom (gset K)).
Proof. intros m1 m2 Hm. apply set_eq=> k. by rewrite !elem_of_dom Hm. Qed.

(*
Alternative version by induction on the types, seems fairly similar.

Lemma cmd_adequacy2 lty cmd lty' :
  wf_cdefs Δ →
  cmd_has_ty lty cmd lty' →
  ∃ n,
  forall st st', cmd_eval st cmd st' →
    heap_models st.2 ∗ interp_local_tys lty st.1 -∗ |=▷^n
    heap_models st'.2 ∗ interp_local_tys lty' st'.1.
Proof.
  move => wfΔ.
  move : lty lty'.
  induction 1 as [ lty | lty1 lty2 lty3 fstc sndc hfst hi1 hsnd hi2 |
      lty lhs e ty he | lty1 lty2 cond thn els hcond hthn hi1 hels hi2 |
      lty lhs recv t name fty hrecv hf |
      lty recv fld rhs fty t hrecv hrhs hf |
      lty lhs t args fields hf hdom harg |
      lty lty_body lhs recv t name mdef args hrecv hm hdom harg
      hbody hi hret ].
  - exists 0 => st st' hc.
    inv hc.
    by rewrite updN_zero.
  - destruct hi1 as (n1 & hn1).
    destruct hi2 as (n2 & hn2).
    exists (n1 + n2) => st st' hc.
    inv hc.
    apply hn1 in H2.
    apply hn2 in H4.
    iIntros "H".
    iDestruct (H2 with "H") as "H".
    iPoseProof (updN_mono with "H") as "H";
      first done.
    by rewrite Nat_iter_add.
  - exists 0 => st st' hc.
    inv hc.
    iIntros "[? #Hle]".
    rewrite updN_zero. iFrame.
    iDestruct (expr_adequacy with "Hle") as "#?"; try done.
    by iApply interp_local_tys_update.
  - destruct hi1 as (n1 & hn1).
    destruct hi2 as (n2 & hn2).
    exists (n1 + n2) => st st' hc.
    iIntros "H".
    inv hc.
    + apply hn1 in H5.
      iApply updN_plus.
      by iApply H5.
    + apply hn2 in H5.
      rewrite Nat.add_comm.
      iApply updN_plus.
      by iApply H5.
  - exists 1 => st st' hc.
    inv hc.
    iIntros "[Hh #Hle]". simpl.
    iModIntro. (* keep the later *)
    iDestruct (expr_adequacy with "Hle") as "#He"; try done.
    iDestruct (heap_models_lookup with "Hh He") as (fields) "(Hh&Ht&Hv)"; first done.
    iDestruct "Ht" as %[? ?].
    rewrite bi.later_sep.
    iSplitL "Hh"; first done.
    assert (hfield: fields !! name = Some fty).
    { apply has_fields_inherits_lookup with t0 t => //.
      by apply wfΔ.
    }
    iDestruct ("Hv" $! name fty hfield) as (w) "[%hw hi]".
    rewrite H6 in hw; injection hw; intros ->; clear hw.
    iNext. by iApply interp_local_tys_update.
  - (* TODO: set *) admit.
  - exists 1 => st st' hc.
    inv hc; simpl.
    iIntros "[Hh #Hle]".
    (* we need one modality to update the
       semantic heap *)
    iDestruct "Hh" as (sh) "(H●&Hdom&#Hh)".
    iDestruct "Hdom" as %Hdom.
    iMod (own_update with "H●") as "[H● H◯]".
    { apply (gmap_view_alloc _ new DfracDiscarded
        (t, interp_tys_next interp_type fields)); last done.
      apply (not_elem_of_dom (D:=gset loc)).
      by rewrite Hdom not_elem_of_dom. }
    iIntros "!> !>". iDestruct "H◯" as "#H◯".
    iAssert (interp_type (ClassT t) (LocV new))
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
        apply dom_map_args in H5.
        by rewrite dom_interp_tys_next H5 -hdom.
      }
      iIntros (f iF) "hiF".
      iAssert (⌜f ∈ dom stringset fields⌝)%I as "%hfield".
      {
        rewrite -dom_interp_tys_next elem_of_dom.
        rewrite /interp_tys_next /interp_ty_next.
        rewrite !lookup_fmap.
        by iRewrite "hiF".
      }
      assert (h0: is_Some (args !! f)).
      {
        apply elem_of_dom.
        by rewrite -hdom.
      }
      destruct h0 as [a0 ha0].
      assert (h1: is_Some (vargs !! f)).
      {
        apply elem_of_dom.
        apply dom_map_args in H5.
        by rewrite H5 -hdom.
      }
      destruct h1 as [v0 hv0].
      assert (h2: is_Some (fields !! f)) by (by apply elem_of_dom).
      destruct h2 as [fty hty].
      iExists v0; iSplitR; first done.
      rewrite /interp_tys_next /interp_ty_next lookup_fmap.
      assert (heval0: expr_eval le a0 = Some v0).
      { rewrite (map_args_lookup _ _ _ args vargs H5 f) in hv0.
        by rewrite ha0 in hv0.
      }
      assert (hty0: expr_has_ty lty a0 fty) by (by apply harg with f).
      rewrite hty /= option_equivI later_equivI.
      iNext.
      rewrite discrete_fun_equivI.
      iSpecialize ("hiF" $! v0).
      iRewrite -"hiF".
      by iDestruct (expr_adequacy a0 with "Hle") as "#Ha0".
    + rewrite lookup_insert_ne; last done.
      by iApply "Hh".
*)
