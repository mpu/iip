Axiom loc num fname tag tvar: Type.

Axiom eq_tvar: forall (X Y:tvar), {X=Y}+{X<>Y}.

Axiom dict: forall (K V:Type), Type.
Axiom get: forall {K V} (d:dict K V), K -> option V.
Axiom set: forall {K V} (d:dict K V), K -> V -> dict K V.
Axiom get_set_tvar: forall V (X Y:tvar) (v:V) d,
    get (set d X v) Y = if eq_tvar X Y then Some v else get d Y.

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
| Tmixed
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
  subtype A (TUnion B C)
| subtype_mixed A:
  subtype A Tmixed.

Ltac inv H := inversion H; clear H; subst.

Module InductiveDefs.
  
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
    interp tenv (TClass A) h (Loc l)

  | interp_Tmixed A h v:
    A <> Tmixed ->
    interp tenv A h v ->
    interp tenv Tmixed h v
  .

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
    - destruct A; try assumption; econstructor; eauto; congruence.
  Qed.

End InductiveDefs.


Module StepIndexedFixpoint.

  Fixpoint interp (tenv:dict tvar semtype) (n:nat) (t:typ) : semtype :=
    match n with
    | O => fun h v => True
    | S k => fun h v =>
        match t with
        | TNum =>
            match v with
            | Num _ => True
            | _ => False
            end
        | TUnion typ1 typ2 =>
            interp tenv k typ1 h v \/ interp tenv k typ2 h v
        | TClass A =>
            match v with
            | Null => True
            | Loc l =>
                match get p A, get h l with
                | Some cl, Some o => 
                    (let t_dyn := o.(obj_type) in
                     t_dyn = A \/ inherits t_dyn A)
                    /\
                      (forall f tf,
                          inherited_fields A f tf ->
                          exists v, get o.(obj_fields) f = Some v
                                    /\ interp tenv k tf h v) 
                | _, _ => False
                end
            | _ => False
            end
        | TVar X =>
            match get tenv X with
            | Some ST =>
                ST h v
            | None => False
            end
        | TApp typ1 X typ2 =>
            interp (set tenv X (interp tenv k typ2)) k typ1 h v
        | Tmixed  =>
            exists t, t<>Tmixed /\ interp tenv k t h v
        end
  end.

  Definition tenv_order (tenv1 tenv2: dict tvar semtype) : Prop :=
    forall X ST1,
      get tenv1 X = Some ST1 ->
      exists ST2, get tenv2 X = Some ST2 /\
                    forall h v, ST1 h v -> ST2 h v.
  
  Lemma step_index_succ_aux: forall n tenv1 tenv2 t h v,
      tenv_order tenv1 tenv2 ->
      interp tenv1 (S n) t h v ->
      interp tenv2 n t h v.
  Proof.
    induction n; intros tenv1 tenv2 t h v Ho.
    - simpl; trivial.
    - remember (S n) as k eqn:Hk.
      intros H; rewrite Hk.
      simpl in *.
      repeat match goal with
             [ |- context[match ?x with | _ => _ end] ] =>
               let h := fresh in destruct x eqn:h
             end; auto.
      + unfold tenv_order in *.
        destruct (get tenv1 x) eqn:Henv1; try (elim H; fail).
        edestruct Ho as (s1 & T1 & T2); eauto.
        assert (s=s1) by congruence; subst.
        eauto.
      + destruct (get tenv1 x) eqn:Henv1; try (elim H; fail).
        edestruct Ho as (s1 & T1 & T2); eauto.
        congruence.
      + apply IHn with(2:=H); auto.
        intros Y ST1.
        rewrite get_set_tvar.
        destruct eq_tvar.
        * intros T; inv T.
          econstructor; rewrite get_set_tvar; destruct eq_tvar; try congruence.
          split; eauto.
        * intros T.
          edestruct Ho as (ST2 & S1 & S2); eauto.
          exists ST2; split; eauto.
          rewrite get_set_tvar; destruct eq_tvar; congruence.
      + intuition eauto.
      + destruct H as (t' & T1 & T2).
        econstructor; split; eauto.
      + destruct H; split; auto.
        intros f tf Hi.
        edestruct H4 as (v' & V1 & V2); eauto.
  Qed.


  Lemma step_index_succ: forall n tenv t h v,
      interp tenv (S n) t h v ->
      interp tenv n t h v.
  Proof.
    intros n tenv t h v H.
    apply step_index_succ_aux with tenv; auto.
    intro; eauto.
  Qed.
  Hint Resolve step_index_succ.
  
  Lemma subtype_implies_inclusion:
    forall typ1 typ2,
      subtype typ1 typ2 ->
      forall n tenv h v, interp tenv n typ1 h v -> interp tenv n typ2 h v.
  Proof.
    induction 1; (destruct n; [auto|intros tenv h v]).
    - intro; assumption.
    - destruct v; auto.
      simpl.
      case_eq (get p A); [intros cl Hcl|intuition;fail].
      case_eq (get h l); [intros o Ho|intuition;fail].
      intros (Hi1, Hi2).
      edestruct inherits_right_exist_class as (clB, HclB); eauto;
        rewrite HclB.
      split.
      + destruct Hi1; subst; auto.
        right; eapply inherits_trans; eauto.
      + intros f tf Hinh.
        apply Hi2.
        eapply inherited_fields_parents; eauto.
    - intros; simpl; auto.
    - intros; simpl; auto.
    - intros H.
      destruct A; try assumption; simpl; econstructor; split; eauto;
        try congruence.
  Qed.
  
End StepIndexedFixpoint.

