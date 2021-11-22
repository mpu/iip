Axiom loc num fname tag: Type.

Axiom dict: forall (K V:Type), Type.
Axiom get: forall {K V} (d:dict K V), K -> option V.

Inductive value :=
  | Null | Num (n:num) | Loc (l:loc).

Record obj :=
  mk_obj
    {
      obj_type: tag;
      obj_fields: dict fname value
    }.

Definition heap := dict loc obj.


Inductive typ :=
| TNum
| TUnion (typ1 typ2 : typ)
| TClass (t: tag).

Record class_decl :=
  mk_cl {
      cl_parent: option tag;
      cl_fields: dict fname typ
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

Inductive interp: typ -> heap -> value -> Prop :=
| interp_TNum h n:
  interp TNum h (Num n)
         
| interp_Tunion typ1 typ2 h v:
  (interp typ1 h v \/ interp typ2 h v) ->
  interp (TUnion typ1 typ2) h v
         
| interp_TClass_null t h:
  interp (TClass t) h Null

| interp_TClass_obj t_dyn A cl h l o:
  get p A = Some cl ->
  get h l = Some o ->
  o.(obj_type) = t_dyn ->
  (t_dyn = A \/ inherits t_dyn A) ->
  (forall f tf,
      inherited_fields A f tf ->
      exists v, get o.(obj_fields) f = Some v /\ interp tf h v) ->
  interp (TClass A) h (Loc l).

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
    forall h v, interp typ1 h v -> interp typ2 h v.
Proof.
  induction 1; intros h v HI.
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

