From iris.algebra Require Import excl auth list.    (* stuff for ghost state *)
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import atomic.      (* atomic triples/update *)
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation. (* atomic_heap *)

(* Useful reading:
   - https://github.com/tchajed/coq-tricks
   - https://coq.inria.fr/refman/proof-engine/tactics.html#intro-patterns
 *)

(** Simple concurrent stack, with comments, lots of them *)

(* Ghost state is central in Iris, it is defined with resource
   algebras (CMRA). CMRAs are a generalization of partial
   commutative monoids. The composition law of an RA is what
   will give the rules that govern the separating conjunction
   of two ghost state assertions; indeed:

     own a ∗ own b ⊣⊢ own (a ⋅ b)

   where own is how we "lift" an RA element into a proposition.


   The ghost state for our stack, we use the CMRA:

     Auth(Option(Excl(ListOfe)))
       where ListOfe = List(Val)

   Auth takes a CMRA with 'unit' and Excl has no unit, this is
   why we insert Option in the middle.

   Auth is the authoritative monoid, it lets us split some
   knowledge in two parts ● and ◯; ● being the so-called
   authoritative part (usually hidden in an invariant)
   while ◯ is left for clients.

   Excl(X) is a simple monoid parameterized by a set X. It
   composes only trivially (x ⋅ ε) = (ε ⋅ x) = x (where
   x ∈ X); all other compositions are undefined.

   In reality, X in Excl(X) is not a mere set (as described in
   the POPL'15 paper), but an ofe (ordered family of equivalence);
   that is because of a refinement Iris got to support so-called
   "higher-order ghost state" (technically, the step-indexing
   had to make its way into ghost state).

   Note: This CMRA happens to be in the standard library of Iris
   in iris/algebra/lib/excl_auth.v; so we could marginally
   simplify our development using 'excl_authR (list0 val0)'
   directly.
 *)
Class stackG Σ := StackG {
  (* The :> syntax means that when an instance of stackG Σ can
     automatically be seen as an instance of inG Σ (authR ...) *)
  stack_stateG :> inG Σ (authR (optionUR (exclR (listO valO))));
}.

(* Alternative definition (because there is a single field): *)
(* Class stackG Σ := StackG :> inG Σ (authR (optionUR (exclR (listO valO)))). *)

Section stack.
  (* Context introduces parameters for all the subsequent definitions &
     theorems. Here we assume that we have the ghost state to represent
     a heap (ℓ ↦ v is not buitin, it's coming from the heapG CMRA). And
     also the ghost state for our stack.

     I believe the `{ ... } syntax tells Coq 2 things. First, we want
     it to generalize free variables in ... as "implicit" and
     "maximally inserted" arguments. Second, the `{A, B} syntax lets
     us add variables in our context of type A and B without naming
     them. If we remove the `, we have to give names for the variables.

     Some more details about "maximally inserted" and "implict".
     Implicit means that they are left for Coq to figure out, and
     maximally inserted means that they should be inserted even when no
     explicit arguments are given. 'cons' (the empty list) for instance
     has an implicit argument A : Type that is implicit and maximally
     inserted, so 'Print cons.' will show an unresolved existential for
     this argument A.

     The ! is here to ask Coq not to implicitly add typeclass arguments
     but instead try to resolve them. I believe that in our case it is
     of no use since both heapG and stackG do not have typeclass
     parameters.

     Relevant doc:
       https://coq.inria.fr/refman/language/extensions/implicit-arguments.html#implicit-generalization
       https://softwarefoundations.cis.upenn.edu/draft/qc-current/Typeclasses.html#lab21
   *)
  Context `{!heapG Σ, !stackG Σ} (* {aheap: atomic_heap Σ} *) (N : namespace).
  Notation iProp := (iProp Σ).

  (* Import atomic_heap.notation. *)

  (* Heaplang syntax is relatively nice and self-explanatory,
     for a change! *)
  Definition new_stack : val :=
    λ: <>,
      (* Heaplang values & expressions can be explored using

           Print val.

         or, in emacs:  C-c C-a C-p val <ENTER>

         You will see that NONE is not an expression, it is in
         fact a notation defined in iris.heap_lang.notation and
         expands to (InjL #()). Similarly (SOME x) expands to
         (InjR x).
       *)
      let: "head" := ref NONE in
      "head".

  Definition push : val :=
    rec: "push" "stack" "val" :=
      let: "head_old" := !"stack" in
      let: "head_new" := ref ("val", "head_old") in
      if: CAS "stack" "head_old" (SOME "head_new") then
        (* The value is inserted, we are done. *)
        #()
      else
        (* Else, retry. *)
        "push" "stack" "val".

  Definition pop : val :=
    rec: "pop" "stack" :=
      match: !"stack" with
        NONE => NONE (* stack empty *)
      | SOME "head_old" =>
        let: "head_old_data" := !"head_old" in
        (* See if we can change the master head pointer *)
        if: CAS "stack" (SOME "head_old") (Snd "head_old_data") then
          (* The CAS worked. Return the value. *)
          SOME (Fst "head_old_data")
        else
          (* Else, retry. *)
          "pop" "stack"
      end.

  (* Use our ghost state to define a proposition capturing the
     contents of the stack; we are using ◯ because that is the
     proposition we will be giving to clients *)
  Definition stack_content (γs : gname) (l : list val) : iProp :=
    (own γs (◯ Excl' l))%I.

  (* Turn a Coq representation of a stack element into a heaplang
     value *)
  Definition stack_elem_to_val (stack_rep : option loc) : val :=
    match stack_rep with
    | None => NONEV
    | Some l => SOMEV #l
    end.

  (* We can prove that stack_elem_to_val is an injective function.
     Inj is from stdpp, the standard library extended by Iris folks;
     it takes the equivalence relations on the domain and co-domain
     as arguments. Here, we use leibniz equality.

     Local is used because stack_elem_to_val is a notion internal to
     our proof/module. Instance is used because Inj is a typeclass.

     Reference doc:
       https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.base.html#lab8
   *)
  Local Instance stack_elem_to_val_inj : Inj (=) (=) stack_elem_to_val.
  Proof.
    (* Here we use an ssreflect rewrite tactic. /Foo unfolds the
       constant Foo; => is a 'tactical' that moves stuff from the
       goal to the context. In this case we move two universally
       quantified variable x and y. Instead of giving them names
       we use ? to have ssreflect "invent" a name. Note: the invented
       names cannot be mentioned further down in the proof script
       for script-robustness purposes (their names are mangled: _x_
       and _y_).

       Reference doc:
         https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html#rewriting
     *)
    rewrite /Inj /stack_elem_to_val => ? ?.
    (* case_match is a tactic from stdpp:
       https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.tactics.html *)
    repeat case_match; congruence.
  Qed.

  (* The classic inductively-defined 'list' separation logic
     predicate *)
  Fixpoint list_inv (l : list val) (rep : option loc) : iProp :=
    match l with
      (* ⌜ ⌝ is used to lift pure Coq/math propositions in iProp *)
    | nil => ⌜rep = None⌝
    | v::l => ∃ (ℓ : loc) (rep' : option loc),
                ⌜rep = Some ℓ⌝ ∗
                (* ↦□ is a persistent readonly version of ↦;
                   having this permission does not allow mutating
                   the location *)
                ℓ ↦□ (v, stack_elem_to_val rep') ∗
                list_inv l rep'
    end%I. (* %I is here to put the whole expression in the correct Coq
              notation namespace; namely the one of Iris propositions *)

  (* Local Hint Extern 0 (environments.envs_entails _ (list_inv (_::_) _)) => simpl : core. *)

  Definition stack_inv (γs : gname) (head : loc) : iProp :=
    (∃ stack_rep l, own γs (● Excl' l) ∗
       head ↦ stack_elem_to_val stack_rep ∗ list_inv l stack_rep)%I.

  (* Local Hint Extern 0 (environments.envs_entails _ (stack_inv _ _ _)) => unfold stack_inv : core. *)

  (* Name for our local invariant; names are necessary in Iris
     to avoid allowing opening the same invariant in a nested
     fashion; apparently, that'd be unsound. *)
  Let stackN := N .@ "stack".

  (* Finally, define what it is to be a stack; mostly, is_stack holds when
     we hold the stack invariant. *)
  Definition is_stack (γs : gname) (s : val) : iProp :=
    (∃ head : loc, ⌜s = (#head)%V⌝ ∗ inv stackN (stack_inv γs head))%I.

  (* is_stack is a persistent proposition, because both inv and pure propositions
     are persistent; Coq can figure it out without any help via typeclass resolution *)
  Global Instance is_stack_persistent γs s : Persistent (is_stack γs s) := _.

  (* Now for some proofs! *)
  Lemma new_stack_spec :
    {{{ True }}} new_stack #() {{{ γs s, RET s; is_stack γs s ∗ stack_content γs [] }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_alloc head as "Hhead". wp_let.
    (* The important part of the proof is assembling our invariant.
       We first need to allocate the ghost state. *)
    iMod (own_alloc (● Excl' [] ⋅ ◯ Excl' [])) as (γs) "[Hs● Hs◯]".
    { (* proving: ✓ (● Excl' [] ⋅ ◯ Excl' []) follows from the Auth RA rules *)
      apply auth_both_valid_discrete. split.
      - (* ≼ is a reflexive relation; as such it implements the
           Reflexive typeclass, and Coq can figure it out! The
           real name of ≼ is 'included', as we can read in
           iris/algbra/cmra.v *)
        apply (_ : Reflexive included).
        (* Equivalently, we could have used 'reflexivity.'
           see: https://coq.inria.fr/refman/addendum/generalized-rewriting.html

           One final way to do it is merely to use 'done.'
           which tries a bunch of things it knows about *)

      - (* done. solves this goal, but let's try to figure out
           a proof ourselves to understand what's going on.

           Inspecting the Iris definitions for validity in
           the option and auth CMRAs, it looks like we can
           simply compute in the goal to reduce it to True.
         *)
        exact I. (* so this works! (I is a (the?) proof of True) *)
      (* we're done; all these ramblings could be replaced with
         'by split.' or 'done.'; but here it's about the journey,
         not the destination! *)
    }
    (* Then we allocate the invariant; here we use a "negative"
       specialization pattern to frame all the hypotheses but
       HΦ and Hs◯; we could have equally used with "[Hhead Hs●]" *)
    iMod (inv_alloc stackN _ (stack_inv γs head) with "[-HΦ Hs◯]").
    { iModIntro.                 (* use that P ⊢ ▷P *)
      rewrite /stack_inv.        (* open the stack invariant *)
      iExists None, []. iFrame.  (* set the initial stack representation *)
      done.                      (* boils down to ⌜ None = None ⌝ which done proves *)
    }
    iApply "HΦ". iModIntro.
    iFrame.     (* solves stack_contents ?x [] *)
    iExists _.  (* we can use iExists even with is_stack folded *)
    (* auto. *) (* the last three steps can be solved with auto *)
    iFrame.     (* uses the invariant we proved *)
    iPureIntro. reflexivity.
  Qed.

  (* Some remarks about Iris modalities.
     It is the case that
       P ⊢ |={E}=> P and
       P ⊢ ▷ P
  *)
  Goal ∀(P : iProp) E, (P ⊢ |={E}=> P) ∧ (P ⊢ ▷ P).
  Proof.
    intros. split; iIntros "?"; iModIntro; iAssumption.
  Qed.

  (* Here we prove an atomic triple (using the <<< >>> syntax). This
     is what makes the stack usable in a concurrent setting: as far as
     the user is concerned, a push operation happens atomically (logically
     atomically, to be precise). In particular, this means that the user
     can open invariants around the call to push!

     There is an 'is_stack γs s' assumption, but it is easy to fulfill
     because it is a persistent formula; as such, the library user
     can copy it for all the threads that'll be interacting with the
     stack

     The part '⊤ ∖ ↑N' in the atomic triple specifies an 'outer' mask.
     (See the definition of the notation in iris/program_logic/atomic.v)
     This outer mask makes sure that, when a client uses the atomic
     triple, it does not use an invariant in the upward closure of
     the namespace N (introduced at the beginning of the section).
     That is important because, in the proof of push, we will want
     to open stackN and that's only possible if no enclosing namespace
     is already opened. *)
  Lemma push_spec γs s (v : val) :
    is_stack γs s -∗
    <<< ∀ l : list val, stack_content γs l >>>
      push s v @ ⊤ ∖ ↑N
    <<< stack_content γs (v::l), RET #() >>>.
  Proof.
    (* The first tactic moves is_stack into the persistent context
       using #; the second tactic digs into the syntactic sugar of
       atomic triples.

       Reference doc (about introduction & specialization patterns):
         https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md
     *)
    iIntros "#Hinv". iIntros (Φ) "AU".
    (* First thing we do is open the is_stack predicate; it's a
       black box for the user, but we need it as module implementers.
       The destruct pattern comes in two parts:
         1. a regular Coq part (head)
         2. an Iris part "[-> #Hinv]"
       The Coq pattern is straightforward; the Iris pattern will
       split the separating conjunction ∗ in is_stack in two,
       use the first part as a rewrite rule with ->, and send
       the second part in the persistent context (with #). *)
    iDestruct "Hinv" as (head) "[-> #Hinv]".
    (* We might be calling ourselves recursively, now is a good time
       to use induction because we have not yet expanded the definition
       of push. *)
    iLöb as "IH".
    wp_lam. wp_let.
    (* You might be tempted to use wp_load here (and I tried to!);
       but it will not work.

       Why? because we will only know something about the head
       pointer when we open the invariant. So the first thing to
       do is to focus the WP on an atomic statement (the load),
       then we will be able to open the invariant. *)
    wp_bind (Load _).
    (* The load is focused, we can now use the stack invariant
       for the duration of the load (because it is atomic!).
       When we are done loading, we will have to close the
       invariant for it to be used by other threads. That should
       be easy though, since no mutation happened. *)
    iInv stackN as (stack_rep l) "(H● & H↦ & Hl)" "Hclose".
    (* We now have a head ↦ ? assertion in scope we can use for
       the load. *)
    wp_load.
    (* The load is done, we must close the invariant; we
       simply use all the assertions we got when opening it. *)
    iMod ("Hclose" with "[H● H↦ Hl]").
    { iModIntro. iExists _,_. iFrame. }
    clear l. (* we can get rid of l now *)
    (* Okay, we're done with the first load! *)
    (* We now go though the let; it's easy because we now have
       the value resulting from the load. *)
    iModIntro. wp_let.
    wp_alloc head_new as "Hhead_new". (* execute the allocation *)
    wp_let.
    (* We now reach the second tricky operation of the push function:
       the compare & swap. Again, we'll have to open the invariant,
       so we start by focusing the CAS. *)
    wp_bind (CmpXchg _ _ _).
    (* The CAS will be atomic only if all its arguments are values;
       here we have an InjR argument which we first need to turn into
       a value. *)
    wp_pures.
    (* We can now open the invariant.

       I used a fancy Iris intro pattern to destruct a separating
       conjunction with three elements and strip some ▷ modalities
       (when possible) using ">".

       I initially used an "Hclose" as last parameter, but we end
       up blocked later if we do so. We need to use this more
       primitive version instead to be able to chain the atomic
       update AU. I would like to understand better what is going
       on here. *)
    iInv stackN as (stack_rep' l) "(>H● & >H↦ & Hl)".
    (* Note that we may, a priori, get a different stack_rep and a
       different l from the one we got in the first load. That is
       because, in the meantime, some other thread might have changed
       the stack.

       To continue we need to perform a case analysis and find out if
       the CAS will succeed or fail. Equality on loc, and consequently
       on option loc is decidable, so we can use the Decision type
       class. *)
    destruct (decide (stack_elem_to_val stack_rep' = stack_elem_to_val stack_rep))
             (* Fancy Coq intro pattern to
                  1. apply the stack_elem_to_val_inj theorem
                  2. use the result (stack_rep' = stack_rep) as a
                     rewrite rule.
                Reference doc:
                  https://coq.inria.fr/refman/proof-engine/tactics.html#intro-patterns *)
             as [->%stack_elem_to_val_inj|?].
    (* The first case is when the CAS succeeds (stack_rep' = stack_rep). *)
    - wp_cmpxchg_suc.
      { (* The first subgoal is to prove that it is *safe* to compare the two
           values CAS is comparing.

           In iris_heap_lang/lang.v we can find that it is safe when the value
           fit in 64bits. That's a bit weird IMO, considering we've never heard
           of "bits" so far.

           Anyway, looking at the definition of vals_compare_safe, and then
           val_is_unboxed, we see that whatever stack_elem_to_val returns we
           should be okay. So we simply perform a case analysis on stack_rep to
           deal with both cases.
         *)
        destruct stack_rep; simpl; auto.
      }
      (* We now have to close the invariant; it is the non-trivial case,
         because we managed to update the stack! Exciting. Let's try to
         use Hclose.

         I think at this point we'd like to change the list 'l' in the
         invariant and append the new value v to it. For this to work
         we need both (● Excl' l') and (◯ Excl' l'); while we do have the
         former, the latter is hidden in the AU assumption... We'll have
         to get it from there.

         Looking at my main example, it is precisely the point where we
         have to use AU. Let's go.
   
         That's interesting, AU is really what'll let us close the
         stackN invariant; the Iris destruct pattern below will give
         us two things: a list latomic together with the assumption
         that 'stack_content γs latomic' holds; and a CHOICE expressed
         as a conjunction ∧ of two iProps. We need to choose between:

           1. the blue pill: if the atomic update stays in its
              precondition state
           2. the red pill: if we decide to take the atomic step
              and move to the side of the postcondition; in this
              case, we'll have a way to show Φ, our "final"
              predicate.

         Here we take the red pill!
       *)
      iMod ("AU") as (l') "[H◯ [_ Hredpill]]".
      (* The goal now is to re-establish the invariant;
         for that we need to show 'list_inv (v :: l) ?'.
         
         Let us begin by turning our ↦ into a persistent
         readonly ↦□ *)
      iMod (mapsto_persist with "Hhead_new") as "#Hhead_new".
      (* Then we use the fact that we have both ● Excl' l and
         ◯ Excl' l' to infer that l = l'. The fancy intro pattern
         goes from ✓ (● Excl' l) (◯ Excl' l') to l' = l; and
         uses this equality to rewrite the goal. *)
      iDestruct (own_valid_2 with "H● H◯") as
        %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      (* We now want to go from ● Excl' l to ● Excl' (v :: l).
         To this end, we use the own_update_2 theorem. *)
      iMod (own_update_2 with "H● H◯") as "[H● H◯]".
      { (* The theorems in the comma-separated list below are applied in
           sequence. *)
        apply auth_update, option_local_update.
        apply (exclusive_local_update _ (Excl (v :: l))).
        done.
      }
      (* We'll now use the red pill and, to do so, restore the
         stack invariant with the updated list. *)
      iMod ("Hredpill" with "H◯") as "HΦ".
      iModIntro. (* c.f. my remarks about modalities *)
      iSplitR "HΦ".
      { iModIntro. iExists (Some head_new), (v :: l).
        iFrame. simpl.
        (* eauto can go look in the context and instantiate existentials.
           Its job is rather easy here. *)
        eauto. }
      (* We're now almost done; concluding is merely a matter of
         using HΦ *)
      wp_pures. by iApply "HΦ".
    (* Moving on to the failure case of the CAS. *)
    - wp_cmpxchg_fail.
      { (* copied from above *) destruct stack_rep; compute; auto. }
      (* We will not use AU directly in the branch because we don't
         need to update the stack invariant. So concluding will be
         a mere matter of applying the Löb induction hypothesis. *)
      iModIntro. iSplitR "AU".
      { iModIntro. iExists _, _. iFrame. }
      wp_pures. by iApply ("IH" with "AU").
  Qed.

End stack.
