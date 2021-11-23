Axiom loc num fname tag tvar: Type.

Axiom dict: forall (K V:Type), Type.
Axiom get: forall {K V} (d:dict K V), K -> option V.
Axiom set: forall {K V} (d:dict K V), K -> V -> dict K V.

Inductive value :=
  | Null | Num (n:num) | Loc (l:loc).

Record obj :=
  mk_obj
    {
      obj_type: tag;
      obj_fields: dict fname value
    }.

Definition heap := dict loc obj.

Definition semtype := heap -> value -> Prop.

Inductive typ :=
| TNum
| TVar (x:tvar) (* type variable in generic def *)
| TApp (typ1: typ) (X: tvar) (typ2: typ)
| TUnion (typ1 typ2: typ)
| TClass (t: tag).

Record class_decl :=
  mk_cl {
      cl_parent: option tag;
      cl_fields: dict fname typ;
      cl_params: list tvar; (* non empty only for generics *)
    }.

Definition prog := dict tag class_decl.

(* Let's fix a program *)
Axiom p: prog.

Inductive inherits: tag -> tag -> Prop :=
| inherits_direct A B clA clB:
  get p A = Some clA ->
  get p B = Some clB ->
  clA.(cl_parent) = Some B ->
  inherits A B
| inherits_trans A B C:
  inherits A B -> inherits B C -> inherits A C.

Lemma inherits_right_exist_class: forall A B,
    inherits A B ->
    exists cl, get p B = Some cl.
Proof.
  induction 1; eauto.
Qed.

Inductive inherited_fields: tag -> fname -> typ -> Prop :=
| inherited_fields_direct A clA f ft:
  get p A = Some clA ->
  get clA.(cl_fields) f = Some ft ->
  inherited_fields A f ft
| inherited_fields_parents A B f ft:
  inherits A B ->
  inherited_fields B f ft ->
  inherited_fields A f ft.

Inductive interp (tenv:dict tvar semtype) : typ -> semtype :=
| interp_TNum h n:
  interp tenv TNum h (Num n)
         
| interp_Tunion typ1 typ2 h v:
  (interp tenv typ1 h v \/ interp tenv typ2 h v) ->
  interp tenv (TUnion typ1 typ2) h v
         
| interp_TClass_null t h:
  interp tenv (TClass t) h Null

| interp_TVar X ST h v:
  get tenv X = Some ST ->
  ST h v ->
  interp tenv (TVar X) h v

(*         
| interp_TApp typ1 X typ2 h v:
  interp (set tenv X (interp tenv typ2)) typ1 h v ->
  interp tenv (TApp typ1 X typ2) h v

Error: Non strictly positive occurrence of "interp" in
 "forall (typ1 : typ) (X : tvar) (typ2 : typ) (h : heap) (v : value),
  interp (set tenv X (interp tenv typ2)) typ1 h v ->
  interp tenv (TApp typ1 X typ2) h v".
*)
         
| interp_TClass_obj t_dyn A cl h l o:
  get p A = Some cl ->
  get h l = Some o ->
  o.(obj_type) = t_dyn ->
  (t_dyn = A \/ inherits t_dyn A) ->
  (forall f tf,
      inherited_fields A f tf ->
      exists v, get o.(obj_fields) f = Some v /\ interp tenv tf h v) ->
  interp tenv (TClass A) h (Loc l).

Inductive subtype : typ -> typ -> Prop :=
| subtype_refl A:
  subtype A A
| sutype_inherits A B:
  inherits A B ->
  subtype (TClass A) (TClass B)
| subtype_union_left A B C:
    subtype A B ->
    subtype A (TUnion B C)
| subtype_union_right A B C:
    subtype A C ->
    subtype A (TUnion B C).

Ltac inv H := inversion H; clear H; subst.

Lemma subtype_implies_inclusion:
  forall typ1 typ2,
    subtype typ1 typ2 ->
    forall tenv h v, interp tenv typ1 h v -> interp tenv typ2 h v.
Proof.
  induction 1; intros tenv h v HI.
  - assumption.
  - inv HI; try constructor.
    edestruct inherits_right_exist_class as (clB, HclB); eauto.
    econstructor; eauto.
    + destruct H4; subst; auto.
      right; eapply inherits_trans; eauto.
    + intros f tf Hinh.
      apply H5.
      eapply inherited_fields_parents; eauto.
  - constructor; eauto.
  - constructor; eauto.
Qed.

