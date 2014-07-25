Require Import Setoid FunctionalExtensionality.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

(** The standard library does not provide projections of [sigT2] or
    [sig2].  I define coercions to [sigT] and [sig], so that [projT1],
    [projT2], [proj1_sig], and [proj2_sig] do the right thing, and I
    define [projT3], [proj3_sig]. *)
Section sig.
  Definition sigT_of_sigT2 A P Q (x : @sigT2 A P Q) := let (a, h, _) := x in existT _ a h.
  Global Coercion sigT_of_sigT2 : sigT2 >-> sigT.
  Definition projT3 A P Q (x : @sigT2 A P Q) :=
    let (x0, _, h) as x0 return (Q (projT1 x0)) := x in h.

  Definition sig_of_sig2 A P Q (x : @sig2 A P Q) := let (a, h, _) := x in exist _ a h.
  Global Coercion sig_of_sig2 : sig2 >-> sig.
  Definition proj3_sig A P Q (x : @sig2 A P Q) :=
    let (x0, _, h) as x0 return (Q (proj1_sig x0)) := x in h.
End sig.

(** Test if a tactic succeeds, but always roll-back the results *)
Tactic Notation "test" tactic3(tac) :=
  try (first [ tac | fail 2 tac "does not succeed" ]; fail tac "succeeds"; [](* test for [t] solved all goals *)).

(** [not tac] is equivalent to [fail tac "succeeds"] if [tac] succeeds, and is equivalent to [idtac] if [tac] fails *)
Tactic Notation "not" tactic3(tac) := try ((test tac); fail 1 tac "succeeds").

(** fail if [x] is a function application, a dependent product ([fun _
    => _]), or a pi type ([forall _, _]), or a fixpoint *)
Ltac atomic x :=
  idtac;
  match x with
    | _ => is_evar x; fail 1 x "is not atomic (evar)"
    | ?f _ => fail 1 x "is not atomic (application)"
    | (fun _ => _) => fail 1 x "is not atomic (fun)"
    | forall _, _ => fail 1 x "is not atomic (forall)"
    | let x := _ in _ => fail 1 x "is not atomic (let in)"
    | match _ with _ => _ end => fail 1 x "is not atomic (match)"
    | _ => is_fix x; fail 1 x "is not atomic (fix)"
    | context[?E] => (* catch-all *) (not constr_eq E x); fail 1 x "is not atomic (has subterm" E ")"
    | _ => idtac
  end.

(** [destruct] discriminees of [match]es, but only if they satisfy [tac] (e.g., [atomic] *)
Ltac destruct_in_match_if' tac :=
  match goal with
    | [ |- appcontext[match ?D with _ => _ end] ] => tac D; destruct D
  end.
Ltac destruct_in_match_if tac := repeat destruct_in_match_if' tac.


(* [pose proof defn], but only if no hypothesis of the same type exists.
   most useful for proofs of a proposition *)
Tactic Notation "unique" "pose" "proof" constr(defn) :=
  let T := type of defn in
  match goal with
    | [ H : T |- _ ] => fail 1
    | _ => pose proof defn
  end.

(** [pose defn], but only if that hypothesis doesn't exist *)
Tactic Notation "unique" "pose" constr(defn) :=
  match goal with
    | [ H := defn |- _ ] => fail 1
    | _ => pose defn
  end.

(** check's if the given hypothesis has a body, i.e., if [clearbody]
    could ever succeed.  We can't just do [test_tac (clearbody H)],
    because maybe the correctness of the proof depends on the body of
    H *)
Tactic Notation "has" "body" hyp(H) :=
  test (let H' := fresh in pose H as H'; unfold H in H').

(** find the head of the given expression *)
Ltac head expr :=
  match expr with
    | ?f _ => head f
    | _ => expr
  end.

Ltac head_hnf expr := let expr' := eval hnf in expr in head expr'.

(** Fail if the goal has an evar *)
Ltac goal_has_evar :=
  idtac;
  match goal with
    | [ |- ?G ] => first [ has_evar G | fail 2 "Goal has no evars" ]
  end.

(** call [tac H], but first [simpl]ify [H].
    This tactic leaves behind the simplified hypothesis. *)
Ltac simpl_do tac H :=
  let H' := fresh in pose H as H'; simpl; simpl in H'; tac H'.

(** clear the left-over hypothesis after [simpl_do]ing it *)
Ltac simpl_do_clear tac H := simpl_do ltac:(fun H => tac H; try clear H) H.

Ltac simpl_rewrite term := simpl_do_clear ltac:(fun H => rewrite H) term.
Ltac simpl_rewrite_rev term := simpl_do_clear ltac:(fun H => rewrite <- H) term.
Tactic Notation "simpl" "rewrite" open_constr(term) := simpl_rewrite term.
Tactic Notation "simpl" "rewrite" "->" open_constr(term) := simpl_rewrite term.
Tactic Notation "simpl" "rewrite" "<-" open_constr(term) := simpl_rewrite_rev term.

Ltac do_with_hyp tac :=
  match goal with
    | [ H : _ |- _ ] => tac H
  end.

Ltac rewrite_hyp' := do_with_hyp ltac:(fun H => rewrite H).
Ltac rewrite_hyp := repeat rewrite_hyp'.
Ltac rewrite_rev_hyp' := do_with_hyp ltac:(fun H => rewrite <- H).
Ltac rewrite_rev_hyp := repeat rewrite_rev_hyp'.

Ltac setoid_rewrite_hyp' := do_with_hyp ltac:(fun H => setoid_rewrite H).
Ltac setoid_rewrite_hyp := repeat setoid_rewrite_hyp'.
Ltac setoid_rewrite_rev_hyp' := do_with_hyp ltac:(fun H => setoid_rewrite <- H).
Ltac setoid_rewrite_rev_hyp := repeat setoid_rewrite_rev_hyp'.

Ltac apply_hyp' := do_with_hyp ltac:(fun H => apply H).
Ltac apply_hyp := repeat apply_hyp'.
Ltac eapply_hyp' := do_with_hyp ltac:(fun H => eapply H).
Ltac eapply_hyp := repeat eapply_hyp'.


(** Do something with every hypothesis. *)
Ltac do_with_hyp' tac :=
  match goal with
    | [ H : _ |- _ ] => tac H
  end.

(** Rewrite with any applicable hypothesis. *)
Tactic Notation "rewrite" "*" := do_with_hyp' ltac:(fun H => rewrite H).
Tactic Notation "rewrite" "->" "*" := do_with_hyp' ltac:(fun H => rewrite -> H).
Tactic Notation "rewrite" "<-" "*" := do_with_hyp' ltac:(fun H => rewrite <- H).
Tactic Notation "rewrite" "?*" := repeat do_with_hyp' ltac:(fun H => rewrite !H).
Tactic Notation "rewrite" "->" "?*" := repeat do_with_hyp' ltac:(fun H => rewrite -> !H).
Tactic Notation "rewrite" "<-" "?*" := repeat do_with_hyp' ltac:(fun H => rewrite <- !H).
Tactic Notation "rewrite" "!*" := progress rewrite ?*.
Tactic Notation "rewrite" "->" "!*" := progress rewrite -> ?*.
Tactic Notation "rewrite" "<-" "!*" := progress rewrite <- ?*.

(** Run [subst], running [hnf] on any hypothesis that allows [subst]
    to make more progress. *)
Ltac hnf_subst :=
  repeat first [ progress subst
               | do_with_hyp' ltac:(fun H => hnf in H; progress subst) ].

(** solve simple setiod goals that can be solved by [transitivity] *)
Ltac simpl_transitivity :=
  try solve [ match goal with
                | [ _ : ?Rel ?a ?b, _ : ?Rel ?b ?c |- ?Rel ?a ?c ] => transitivity b; assumption
              end ].

(** given a [matcher] that succeeds on some hypotheses and fails on
    others, destruct any matching hypotheses, and then execute [tac]
    after each [destruct].

    The [tac] part exists so that you can, e.g., [simpl in *], to
    speed things up. *)
Ltac destruct_all_matches_then matcher tac :=
  repeat match goal with
           | [ H : ?T |- _ ] => matcher T; destruct H; tac
         end.

Ltac destruct_all_matches matcher := destruct_all_matches_then matcher ltac:(simpl in *).
Ltac destruct_all_matches' matcher := destruct_all_matches_then matcher idtac.

(* matches anything whose type has a [T] in it *)
Ltac destruct_type_matcher T HT :=
  match HT with
    | context[T] => idtac
  end.
Ltac destruct_type T := destruct_all_matches ltac:(destruct_type_matcher T).
Ltac destruct_type' T := destruct_all_matches' ltac:(destruct_type_matcher T).

Ltac destruct_head_matcher T HT :=
  match head HT with
    | T => idtac
  end.
Ltac destruct_head T := destruct_all_matches ltac:(destruct_head_matcher T).
Ltac destruct_head' T := destruct_all_matches' ltac:(destruct_head_matcher T).

Ltac destruct_head_hnf_matcher T HT :=
  match head_hnf HT with
    | T => idtac
  end.
Ltac destruct_head_hnf T := destruct_all_matches ltac:(destruct_head_hnf_matcher T).
Ltac destruct_head_hnf' T := destruct_all_matches' ltac:(destruct_head_hnf_matcher T).

Ltac destruct_sig_matcher HT :=
  match eval hnf in HT with
    | ex _ => idtac
    | ex2 _ _ => idtac
    | sig _ => idtac
    | sig2 _ _ => idtac
    | sigT _ => idtac
    | sigT2 _ _ => idtac
    | and _ _ => idtac
    | prod _ _ => idtac
  end.
Ltac destruct_sig := destruct_all_matches destruct_sig_matcher.
Ltac destruct_sig' := destruct_all_matches' destruct_sig_matcher.

Ltac destruct_all_hypotheses := destruct_all_matches ltac:(fun HT =>
  destruct_sig_matcher HT || destruct_sig_matcher HT
).

(** if progress can be made by [exists _], but it doesn't matter what
    fills in the [_], assume that something exists, and leave the two
    goals of finding a member of the apropriate type, and proving that
    all members of the appropriate type prove the goal *)
Ltac destruct_exists' T := cut T; try (let H := fresh in intro H; exists H).
Ltac destruct_exists := destruct_head_hnf @sigT;
  match goal with
(*    | [ |- @sig ?T _ ] => destruct_exists' T*)
    | [ |- @sigT ?T _ ] => destruct_exists' T
(*    | [ |- @sig2 ?T _ _ ] => destruct_exists' T*)
    | [ |- @sigT2 ?T _ _ ] => destruct_exists' T
  end.

(** if the goal can be solved by repeated specialization of some
    hypothesis with other [specialized] hypotheses, solve the goal by
    brute force *)
Ltac specialized_assumption tac := tac;
  match goal with
    | [ x : ?T, H : forall _ : ?T, _ |- _ ] => specialize (H x); specialized_assumption tac
    | _ => assumption
  end.

(** for each hypothesis of type [H : forall _ : ?T, _], if there is
    exactly one hypothesis of type [H' : T], do [specialize (H H')]. *)
Ltac specialize_uniquely :=
  repeat match goal with
           | [ x : ?T, y : ?T, H : _ |- _ ] => test (specialize (H x)); fail 1
           | [ x : ?T, H : _ |- _ ] => specialize (H x)
         end.

(** specialize all hypotheses of type [forall _ : ?T, _] with
    appropriately typed hypotheses *)
Ltac specialize_all_ways_forall :=
  repeat match goal with
           | [ x : ?T, H : forall _ : ?T, _ |- _ ] => unique pose proof (H x)
         end.

(** try to specialize all hypotheses with all other hypotheses.  This
    includes [specialize (H x)] where [H x] requires a coercion from
    the type of [H] to Funclass. *)
Ltac specialize_all_ways :=
  repeat match goal with
           | [ x : ?T, H : _ |- _ ] => unique pose proof (H x)
         end.
         
(** specialize [H] with any hypothesis that is the unique one of its type. *)
Ltac specialize_hyp_uniquely H :=
  match goal with
    | [ x : ?T, y : ?T' |- _ ] => pose proof (H x); pose proof (H y); fail 1 H "can be specialized by duplicate variables" x "and" y
    | _ => idtac
  end;
  let H' := fresh in
  match goal with
    | [ x : ?T |- _ ] => pose proof (H x) as H'
  end;
    clear H;
    rename H' into H.

(** specialize all hypotheses with any uniquely typed variables *)
Ltac specialize_all_uniquely := do_with_hyp specialize_hyp_uniquely.


(** Run [hnf] in anything inside of a [match] statement *)
Ltac hnf_in_match' :=
  idtac;
  try match goal with
        | [ |- appcontext[match ?E with _ => _ end] ]
          => let E' := (eval hnf in E) in
             progress change E with E'
      end.
Ltac hnf_in_match_in' H :=
  idtac;
  try match type_of H with
        | appcontext[match ?E with _ => _ end]
          => let E' := (eval hnf in E) in
             progress change E with E' in H
      end.

Tactic Notation "hnf_in_match" := do ?progress hnf_in_match'.
Tactic Notation "hnf_in_match" "in" hyp(H) := do ?progress hnf_in_match_in' H.
Tactic Notation "hnf_in_match" "in" "*" := hnf_in_match; do ?do_with_hyp' ltac:(fun H => progress hnf_in_match in H).
Tactic Notation "hnf_in_match" "in" "*" "|-" := do ?do_with_hyp' ltac:(fun H => progress hnf_in_match in H).
Tactic Notation "hnf_in_match" "in" "*" "|-" "*" := hnf_in_match in *.
Tactic Notation "hnf_in_match" "in" hyp(H) "|-" "*" := hnf_in_match; hnf_in_match in H.


(** try to do [tac] after [repeat rewrite] on [rew_H], in both directions *)
Ltac try_rewrite rew_H tac :=
  (rewrite ?rew_H; tac) ||
    (rewrite <- ?rew_H; tac).

Ltac try_rewrite_by rew_H by_tac tac :=
  (rewrite ?rew_H by by_tac; tac) ||
    (rewrite <- ?rew_H by by_tac; tac).

Ltac try_rewrite_repeat rew_H tac :=
  (repeat (rewrite rew_H; tac)) ||
    (repeat (rewrite <- rew_H; tac)).

Ltac solve_repeat_rewrite rew_H tac :=
  solve [ repeat (rewrite rew_H; tac) ] ||
    solve [ repeat (rewrite <- rew_H; tac) ].

(* For things with decidable equality, we have [forall x (P : x = x),
   P = eq_refl].  So replace such hypotheses with [eq_refl]. *)

(** [generalize] any construction in an [eq] match *)
Ltac generalize_eq_match :=
  repeat match goal with
           | [ |- appcontext[match ?f ?x with eq_refl => _ end] ] =>
             let H := fresh in
             progress set (H := f x);
               clearbody H
         end.

(** [destruct] any matches on variables of type [_ = _] *)
Ltac destruct_eq_in_match :=
  repeat match goal with
           | [ |- appcontext[match ?E with _ => _ end] ] => let t := type of E in
                                                            match eval hnf in t with
                                                              | @eq _ _ _ => destruct E
                                                            end
         end.

(** [destruct] things in [if]s *)
Ltac tac_if' tac := 
  match goal with
    | [ |- context[if ?a then _ else _] ] => tac a
  end.
Ltac tac_if tac := repeat tac_if' tac.
Ltac case_eq_if' := tac_if' case_eq.
Ltac case_eq_if := tac_if case_eq.

(** Coq's built in tactics don't work so well with things like [iff]
    so split them up into multiple hypotheses *)
(** We do some hackery with typeclasses to get around the fact that
    Coq 8.4 doesn't have tactics in terms; we want to say
<<
Ltac make_apply_under_binders_in lem H :=
  let tac := make_apply_under_binders_in in
  match type of H with
    | forall x : ?T, @?P x
      => let ret := constr:(fun x' : T =>
                              let Hx := H x' in
                              $(let ret' := tac lem Hx in
                                exact ret')$) in
         let ret' := (eval cbv zeta in ret) in
         constr:(ret')
    | _ => let ret := constr:($(let H' := fresh in
                                pose H as H';
                                apply lem in H';
                                exact H')$) in
           let ret' := (eval cbv beta zeta in ret) in
           constr:(ret')
  end.

Ltac apply_under_binders_in lem H :=
  let H' := make_apply_under_binders_in lem H in
  let H'' := fresh in
  pose proof H' as H'';
    clear H;
    rename H'' into H.
>> *)

Class make_apply_under_binders_in_helper {T} (lem : T) {T'} (H : T') {T''} := do_make_apply_under_binders_in_helper : T''.

Class make_apply_under_binders_in_helper_helper {T} (H : T) {T'} (lem : T') {T''} := do_make_apply_under_binders_in_helper_helper : T''.

Hint Extern 0 (make_apply_under_binders_in_helper_helper ?H ?lem)
=> let H' := fresh in
   pose H as H';
     apply lem in H';
     exact H'
           : typeclass_instances.

Ltac make_apply_under_binders_in lem H :=
  match type of H with
    | forall x : ?T, @?P x
      => let ret := constr:(fun x' : T =>
                              let Hx := H x' in
                              _ : make_apply_under_binders_in_helper lem Hx) in
         let ret' := (eval cbv zeta beta delta [do_make_apply_under_binders_in_helper make_apply_under_binders_in_helper] in ret) in
         let retT := type of ret' in
         let retT' := (eval cbv zeta beta delta [do_make_apply_under_binders_in_helper make_apply_under_binders_in_helper] in retT) in
         constr:(ret' : retT')
    | _ => let ret := constr:(_ : make_apply_under_binders_in_helper_helper H lem) in
           let ret' := (eval cbv beta zeta delta [make_apply_under_binders_in_helper_helper do_make_apply_under_binders_in_helper_helper] in ret) in
           let retT := type of ret' in
           let retT' := (eval cbv beta zeta delta [make_apply_under_binders_in_helper_helper do_make_apply_under_binders_in_helper_helper] in retT) in
           constr:(ret' : retT')
  end.

Hint Extern 0 (make_apply_under_binders_in_helper ?lem ?H) =>
let ret := make_apply_under_binders_in lem H
in exact ret
   : typeclass_instances.

Ltac apply_under_binders_in lem H :=
  let H' := make_apply_under_binders_in lem H in
  let H'' := fresh in
  pose proof H' as H'';
    clear H;
    rename H'' into H.

Ltac split_in_context ident proj1 proj2 :=
  repeat match goal with
           | [ H : context[ident] |- _ ] =>
             let H0 := make_apply_under_binders_in proj1 H in
             let H1 := make_apply_under_binders_in proj2 H in
             pose proof H0;
               pose proof H1;
               clear H
         end.

Ltac split_iff := split_in_context iff @fst @snd.
Ltac split_and := split_in_context and @fst @snd.

(** Test case for [split_and]. *)
Goal (forall x y, x /\ y) -> True.
Proof.
  intro.
  split_and.
  lazymatch goal with
  | [ H0 : forall x : Type, Type -> x, H1 : Type -> forall x : Type, x |- True ] => idtac
  end.
  exact I.
Qed.

Ltac clear_hyp_of_type type :=
  repeat match goal with
           | [ H : type |- _ ] => clear H
         end.

(* If [conVar] is not mentioned in any hypothesis other than [hyp],
   nor in the goal, then clear any hypothesis of the same type as [hyp] *)
Ltac clear_hyp_unless_context hyp conVar :=
  let hypT := type of hyp in
    match goal with
      | [ H0 : hypT, H : context[conVar] |- _ ] => fail 1 (* there is a hypotheses distinct from [hyp] which mentions [conVar] *)
      | [ |- context[conVar] ] => fail 1
      | _ => clear_hyp_of_type hypT
    end.

Ltac recur_clear_context con :=
  repeat match goal with
           | [ H : appcontext[con] |- _ ] =>
             recur_clear_context H; try clear H
           | [ H := appcontext[con] |- _ ] =>
             recur_clear_context H; try clear H
         end.

(* equivalent to [idtac] if [subexpr] appears nowhere in [expr],
   equivalent to [fail] otherwise *)
Ltac FreeQ expr subexpr :=
  match expr with
    | appcontext[subexpr] => fail 1
    | _ => idtac
  end.

Ltac subst_mor x :=
  match goal with
    | [ H : ?Rel ?a x |- _ ] => FreeQ a x; rewrite <- H in *;
      try clear_hyp_unless_context H x
    | [ H : ?Rel x ?a |- _ ] => FreeQ a x; rewrite H in *;
      try clear_hyp_unless_context H x
  end.

Ltac repeat_subst_mor_of_type type :=
  repeat match goal with
           | [ m : context[type] |- _ ] => subst_mor m; try clear m
         end.

(* Using [rew] instead of [rew'] makes this fail... WTF? *)
Ltac subst_by_rewrite_hyp_rew a H rew' :=
  rew' H; clear H;
  match goal with
    | [ H : appcontext[a] |- _ ] => fail 1 "Rewrite failed to clear all instances of" a
    | [ |- appcontext[a] ] => fail 1 "Rewrite failed to clear all instances of" a
    | _ => idtac
  end.

Ltac subst_by_rewrite_hyp a H :=
  subst_by_rewrite_hyp_rew a H ltac:(fun H => try rewrite H in *; try setoid_rewrite H).

Ltac subst_by_rewrite_rev_hyp a H :=
  subst_by_rewrite_hyp_rew a H ltac:(fun H => try rewrite <- H in *; try setoid_rewrite <- H).

Ltac subst_by_rewrite a :=
  match goal with
    | [ H : ?Rel a ?b |- _ ] => subst_by_rewrite_hyp a H
    | [ H : ?Rel ?b a |- _ ] => subst_by_rewrite_rev_hyp a H
  end.

Ltac subst_atomic a := first [ atomic a | fail "Non-atomic variable" a ];
                      subst_by_rewrite a.

Ltac subst_rel rel :=
  match goal with
    | [ H : rel ?a ?b |- _ ] => (atomic a; subst_by_rewrite_hyp a H) || (atomic b; subst_by_rewrite_rev_hyp b H)
  end.

Ltac subst_body :=
  repeat match goal with
           | [ H := _ |- _ ] => subst H
         end.
         
(** Destruct hypotheses that can be destructed without loosing
    information, such as [and] and [sig]. *)
Ltac destruct_safe_hyps' :=
  first [ progress destruct_head_hnf ex
        | progress destruct_head_hnf and
        | progress destruct_head_hnf prod
        | progress destruct_head_hnf sig
        | progress destruct_head_hnf sig2
        | progress destruct_head_hnf sigT
        | progress destruct_head_hnf sigT2
        | progress hnf_subst ].

Ltac destruct_safe_hyps := repeat destruct_safe_hyps'.

(** Split goals that can be split without loosing
    information, such as [and] and [prod]. *)
Ltac split_safe_goals' :=
  hnf;
  match goal with
    | [ |- and _ _ ] => split
    | [ |- prod _ _ ] => split
  end.

Ltac split_safe_goals := repeat split_safe_goals'.

(** Run [reflexivity], but only if the goal has no evars or one or the other argument is an evar. *)
Ltac evar_safe_reflexivity :=
  idtac;
  let R := match goal with |- ?R ?a ?b => constr:(R) end in
  let a := match goal with |- ?R ?a ?b => constr:(a) end in
  let b := match goal with |- ?R ?a ?b => constr:(b) end in
  first [ not goal_has_evar
        | not has_evar a; is_evar b; unify a b
        | not has_evar b; is_evar a; unify a b ];
    reflexivity.

(** Copying from HoTT *)
(** The fact that [r] is a left inverse of [s]. As a mnemonic, note that the partially applied type [Sect s] is the type of proofs
that [s] is a section. *)
Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

(** A typeclass that includes the data making [f] into an adjoint equivalence. *)
Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = f_equal f (eissect x)
}.

Arguments eisretr {A B} f {_} _.
Arguments eissect {A B} f {_} _.
Arguments eisadj {A B} f {_} _.

(** A record that includes all the data of an adjoint equivalence. *)
Record Equiv A B := BuildEquiv {
  equiv_fun :> A -> B ;
  equiv_isequiv :> IsEquiv equiv_fun
}.

Existing Instance equiv_isequiv.

Delimit Scope equiv_scope with equiv.
Local Open Scope equiv_scope.

Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.
Notation "A ≃ B" := (Equiv A B) (at level 85) : equiv_scope.

(** A notation for the inverse of an equivalence.  We can apply this to a function as long as there is a typeclass instance
asserting it to be an equivalence.  We can also apply it to an element of [A <~> B], since there is an implicit coercion to [A -> B]
and also an existing instance of [IsEquiv]. *)

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3) : equiv_scope.
Notation "f ⁻¹" := (@equiv_inv _ _ f _) (at level 3) : equiv_scope.

Instance isequiv_id A : IsEquiv (@id A) :=
  {| equiv_inv := @id A;
     eisretr x := eq_refl;
     eissect x := eq_refl;
     eisadj x := eq_refl |}.

Instance isequiv_idmap A : IsEquiv (fun x : A => x) :=
  {| equiv_inv x := x;
     eisretr x := eq_refl;
     eissect x := eq_refl;
     eisadj x := eq_refl |}.

(** So we know the difference betwen the [sigT]s we're using and the [sigT]s others use *)
Inductive Common_sigT (A : Type) (P : A -> Type) : Type :=
    Common_existT : forall x : A, P x -> Common_sigT P.
Definition Common_projT1 (A : Type) (P : A -> Type) (x : @Common_sigT A P) := let (a, _) := x in a.
Definition Common_projT2 (A : Type) (P : A -> Type) (x : @Common_sigT A P) := let (x0, h) as x0 return (P (Common_projT1 x0)) := x in h.

Definition functor_Common_sigma `{P : A -> Type} `{Q : B -> Type}
  (f : A -> B) (g : forall a, P a -> Q (f a))
  : Common_sigT P -> Common_sigT Q
  := fun u => Common_existT
                _
                (f (Common_projT1 u))
                (g (Common_projT1 u) (Common_projT2 u)).

Lemma path_Common_sigT_uncurried {A : Type} (P : A -> Type) (u v : Common_sigT P)
      (pq : Common_sigT (fun p : Common_projT1 u = Common_projT1 v =>
                           eq_rect _ P (Common_projT2 u) _ p = Common_projT2 v))
: u = v.
Proof.
  destruct pq as [p q], u, v; simpl in *.
  destruct p, q.
  reflexivity.
Defined.

Definition trans_pV {A} {x y : A} (p : x = y)
: eq_trans p (eq_sym p) = eq_refl.
Proof.
  destruct p; reflexivity.
Defined.

Definition trans_Vp {A} {x y : A} (p : x = y)
: eq_trans (eq_sym p) p = eq_refl.
Proof.
  destruct p; reflexivity.
Defined.

Definition trans_assoc {A} {x y z w : A} (p : x = y) (q : y = z) (r : z = w)
: eq_trans p (eq_trans q r) = eq_trans (eq_trans p q) r.
Proof.
  destruct p, q, r.
  reflexivity.
Defined.

Definition f_equal2 {A1 A2 B} (f : A1 -> A2 -> B) {x1 y1 : A1} {x2 y2 : A2}
           (H : x1 = y1) (H' : x2 = y2) : f x1 x2 = f y1 y2.
Proof.
  destruct H, H'.
  reflexivity.
Defined.

Definition path_Common_sigT {A : Type} (P : A -> Type) (u v : Common_sigT P)
      (p : Common_projT1 u = Common_projT1 v)
      (q : eq_rect _ P (Common_projT2 u) _ p = Common_projT2 v)
: u = v
  := @path_Common_sigT_uncurried A P u v (Common_existT _ p q).

Lemma f_equal_compose {A B C} (f : A -> B) (g : B -> C) x y (p : x = y)
: f_equal g (f_equal f p) = f_equal (fun y => g (f y)) p.
Proof.
  destruct p.
  reflexivity.
Defined.

Lemma f_equal_trans {A B} (f : A -> B) {x y z} (p : x = y) (q : y = z)
: f_equal f (eq_trans p q) = eq_trans (f_equal f p) (f_equal f q).
Proof.
  destruct p, q.
  reflexivity.
Defined.

Lemma f_equal_sym {A B} (f : A -> B) {x y} (p : x = y)
: f_equal f (eq_sym p) = eq_sym (f_equal f p).
Proof.
  destruct p.
  reflexivity.
Defined.

Lemma f_equal_pV `{IsEquiv A B f} {x y} (p : x = y)
: f_equal f (f_equal f⁻¹ p) = eq_trans (eisretr f x) (eq_trans p (eq_sym (eisretr f y))).
Proof.
  destruct p; simpl.
  destruct (eisretr f x).
  reflexivity.
Defined.

Lemma f_equal_Vp `{IsEquiv A B f} {x y} (p : x = y)
: f_equal f⁻¹ (f_equal f p) = eq_trans (eissect f x) (eq_trans p (eq_sym (eissect f y))).
Proof.
  destruct p; simpl.
  destruct (eissect f x).
  reflexivity.
Defined.

Section isequiv_f_equal.
  Context `{IsEquiv A B f} {x y : A}.

  Let f_equal_inv (H' : f x = f y) : x = y
    := eq_trans (eq_sym (eissect f x)) (eq_trans (f_equal f⁻¹ H') (eissect f y)).

  Lemma eisretr_f_equal : Sect f_equal_inv (@f_equal _ _ f x y).
  Proof.
    subst f_equal_inv.
    intro.
    etransitivity; [ apply f_equal_trans | ].
    etransitivity; [ apply f_equal; apply f_equal_trans | ].
    etransitivity; [ apply f_equal; apply f_equal2; [ apply f_equal_pV | reflexivity ] | ].
    pattern (eisretr f (f x)).
    refine (eq_rect _ _ _ _ (eq_sym (eisadj f x))).
    pattern (eisretr f (f y)).
    refine (eq_rect _ _ _ _ (eq_sym (eisadj f y))).
    etransitivity; [ apply f_equal2; [ apply f_equal_sym | reflexivity ] | ].
    generalize (f_equal f (eissect f x)).
    generalize (f_equal f (eissect f y)).
    generalize dependent (f (f⁻¹ (f x))).
    generalize dependent (f (f⁻¹ (f y))).
    generalize dependent (f x).
    generalize dependent (f y).
    intros ? ? [] ? ? [] [].
    reflexivity.
  Defined.

  Lemma eissect_f_equal : Sect (@f_equal _ _ f x y) f_equal_inv.
  Proof.
    subst f_equal_inv.
    intros [].
    destruct (eissect f x).
    reflexivity.
  Defined.

  Global Instance isequiv_f_equal : IsEquiv (@f_equal _ _ f x y).
  Proof.
    refine {| eisretr := eisretr_f_equal;
              eissect := eissect_f_equal |}.
    unfold eisretr_f_equal, eissect_f_equal.
    subst f_equal_inv.
    intros [].
    simpl.
    generalize (eq_sym (eisadj f x)).
    generalize (eisretr f (f x)).
    intros ? [].
    generalize (eissect f x).
    intros [].
    reflexivity.
  Defined.
End isequiv_f_equal.

Definition other_adj `{IsEquiv A B f} x
: eissect f (f ⁻¹ x) = f_equal f ⁻¹ (eisretr f x).
Proof.
  refine (eq_trans (eq_sym (eissect (@f_equal _ _ f _ _) _)) (eq_trans _ (eissect (@f_equal _ _ f _ _) _))).
  apply f_equal.
  etransitivity; [ | symmetry; apply f_equal_pV ].
  symmetry; etransitivity; [ apply f_equal; apply trans_pV | ].
  apply eisadj.
Defined.

Definition other_other_adj `{IsEquiv A B f} x
: eissect f x = (@f_equal _ _ f _ _)⁻¹ (eisretr f (f x)).
Proof.
  simpl.
  pattern (eisretr f (f x)).
  refine (eq_rect _ _ _ _ (eq_sym (eisadj f x))).
  etransitivity; [ | apply f_equal2; [ apply f_equal | reflexivity ];
                     symmetry; etransitivity; [ apply other_adj | apply f_equal; apply eisadj ]].
  etransitivity; [ | symmetry; apply trans_assoc ].
  etransitivity; [ | apply f_equal2; [ symmetry; apply trans_Vp | reflexivity ] ].
  destruct (eissect f x).
  reflexivity.
Defined.

Lemma concat_pA1 : forall (A : Type) (f : A -> A) (p : forall x : A, x = f x)
                          (x y : A) (q : x = y), eq_trans (p x) (f_equal f q) = eq_trans q (p y).
Proof.
  intros.
  destruct q.
  simpl.
  destruct (p x).
  reflexivity.
Defined.

Lemma moveR_M1 : forall (A : Type) (x y : A) (p q : x = y), eq_refl = eq_trans (eq_sym p) q -> p = q.
Proof.
  intros.
  destruct p.
  etransitivity; [ apply H | ].
  simpl; case q.
  reflexivity.
Defined.

Lemma moveL_Vp : forall (A : Type) (x y z : A) (p : x = z) (q : y = z) (r : x = y),
       eq_trans r q = p -> q = eq_trans (eq_sym r) p.
Proof.
  intros.
  destruct r, q; simpl in *.
  etransitivity; try eassumption.
  case p; reflexivity.
Defined.

Lemma eq_sym_sym {A} {x y : A} (p : x = y) : eq_sym (eq_sym p) = p.
Proof.
  destruct p.
  reflexivity.
Defined.

Instance symmetric_isequiv `{IsEquiv A B f} : IsEquiv f⁻¹
  := {| eissect := eisretr f;
        eisretr := eissect f;
        eisadj := @other_adj _ _ f _ |}.

Section adjointify.
  Context {A B : Type} (f : A -> B) (g : B -> A).
  Context (isretr : Sect g f) (issect : Sect f g).

  (* This is the modified [eissect]. *)
  Let issect' := fun x =>
                   eq_trans (f_equal g (f_equal f (eq_sym (issect x))))
                            (eq_trans (f_equal g (isretr (f x))) (issect x)).

  Let is_adjoint' (a : A) : isretr (f a) = f_equal f (issect' a).
  Proof.
    subst issect'.
    simpl.
    apply moveR_M1.
    repeat rewrite f_equal_trans, trans_assoc.
    pose proof (concat_pA1 _ (fun b => eq_sym (isretr b)) (f_equal f (eq_sym (issect a)))) as H.
    simpl in H.
    rewrite <- f_equal_compose in H.
    rewrite H.
    clear H.
    rewrite <- !trans_assoc.
    rewrite f_equal_sym.
    apply moveL_Vp.
    rewrite !trans_assoc.
    pose proof (concat_pA1 _ (fun b => eq_sym (isretr b)) (isretr (f a))) as H.
    simpl in H.
    rewrite <- f_equal_compose in H.
    rewrite H.
    rewrite trans_pV.
    case (issect a).
    reflexivity.
  Qed.

  (** We don't make this a typeclass instance, because we want to control when we are applying it. *)
  Definition isequiv_adjointify : IsEquiv f
    := @BuildIsEquiv A B f g isretr issect' is_adjoint'.

  Definition equiv_adjointify : A <~> B
    := @BuildEquiv A B f isequiv_adjointify.
End adjointify.

Section isequiv_functor_Common_sigma.
  Context `{P : A -> Type} `{Q : B -> Type}
  `{IsEquiv A B f} `{forall a, @IsEquiv (P a) (Q (f a)) (g a)}.

  Let functor_Common_sigma_inv : Common_sigT Q -> Common_sigT P
    := functor_Common_sigma
         (f⁻¹)
         (fun x y =>
            (@g (f⁻¹ x))⁻¹ (eq_rect _ Q y _ (eq_sym (eisretr f x)))).

  Lemma functor_Common_sigma_eisretr : Sect functor_Common_sigma_inv (functor_Common_sigma f g).
  Proof.
    subst functor_Common_sigma_inv.
    intro xy.
    apply path_Common_sigT_uncurried.
    destruct xy as [x y].
    simpl in *.
    exists (eisretr f x).
    match goal with
      | [ |- appcontext[g ((@g (f⁻¹ x))⁻¹ ?y)] ]
        => pattern (g ((@g (f⁻¹ x))⁻¹ y))
    end.
    match goal with
      | [ |- ?P (g ((@g (f⁻¹ x))⁻¹ ?y)) ]
        => refine (eq_rect _ P _ _ (eq_sym (eisretr (@g (f⁻¹ x)) y)))
    end.
    generalize (eisretr f x).
    generalize (f (f ⁻¹ x)).
    intros ? e.
    destruct e.
    reflexivity.
  Defined.


  Lemma functor_Common_sigma_eissect : Sect (functor_Common_sigma f g) functor_Common_sigma_inv.
  Proof.
    subst functor_Common_sigma_inv.
    intro xy.
    apply path_Common_sigT_uncurried.
    destruct xy as [x y].
    simpl in *.
    exists (eissect f x).
    pattern (eisretr f (f x)).
    refine (eq_rect _ _ _ _ (eq_sym (eisadj f x))).
    generalize (eissect f x).
    generalize (f ⁻¹ (f x)).
    intros ? e.
    destruct e.
    simpl.
    apply eissect.
  Defined.

  Global Instance isequiv_functor_Common_sigma
  : IsEquiv (functor_Common_sigma f g) | 1000
    := @isequiv_adjointify
         _ _
         _ _
         functor_Common_sigma_eisretr
         functor_Common_sigma_eissect.
End isequiv_functor_Common_sigma.

Definition curry {A B C} (f : forall (x : A) (y : B x), C x y)
: forall xy : Common_sigT B, C (Common_projT1 xy) (Common_projT2 xy)
  := fun xy => f (Common_projT1 xy) (Common_projT2 xy).

Instance isequiv_curry {A B C} : IsEquiv (@curry A B C).
Proof.
  refine (@isequiv_adjointify
            _ _
            curry
            (fun g x y => g (Common_existT _ x y))
            _
            _);
  repeat (intros [] || intro);
  unfold curry; simpl;
  apply functional_extensionality_dep; intro;
  destruct_head Common_sigT; trivial.
Defined.

Ltac uncurryT H :=
  match eval simpl in H with
    | forall (x : ?T1) (y : @?T2 x), @?f x y => uncurryT (forall xy : @Common_sigT T1 T2, f (Common_projT1 xy) (Common_projT2 xy))
    | ?H' => H'
  end.

Ltac curryT H :=
  match eval simpl in H with
    | forall xy : @Common_sigT ?T1 ?T2, @?f xy => curryT (forall (x : T1) (y : T2 x), f (@Common_existT T1 T2 x y))
    | ?H' => H'
  end.

Ltac uncurry H := let HT := type of H in
  match eval simpl in HT with
    | forall (x : ?T1) (y : @?T2 x) (z : @?T3 x y), @?f x y z =>
      uncurry (fun xyz => H (Common_projT1 (Common_projT1 xyz)) (Common_projT2 (Common_projT1 xyz)) (Common_projT2 xyz))
    | forall (x : ?T1) (y : @?T2 x), @?f x y => uncurry (fun xy : @Common_sigT T1 T2 => H (Common_projT1 xy) (Common_projT2 xy))
    | ?H' => H
  end.

Ltac curry H := let HT := type of H in
  match eval simpl in HT with
    | forall xy : @Common_sigT ?T1 ?T2, @?f xy => curry (fun (x : T1) (y : T2 x) => H (@Common_existT T1 T2 x y))
    | ?H' => H
  end.

Class can_transform A B := do_transform : A -> B.

Instance can_transform_sigma_base {A} {P : A -> Type}
: can_transform (sigT P) (sigT P) | 0
  := fun x => x.

Instance can_transform_sigma {A B B' C'}
         `{forall x : A, can_transform (B x) (@sigT (B' x) (C' x))}
: can_transform (forall x : A, B x)
                (@sigT (forall x, B' x) (fun b => forall x, C' x (b x))) | 0
  := fun f => existT
                (fun b => forall x : A, C' x (b x))
                (fun x => projT1 (do_transform (f x)))
                (fun x => projT2 (do_transform (f x))).

(*
Monomorphic Definition equal_f_dep
: forall A B (f g : forall a : A, B a), f = g -> forall x : A, f x = g x
  := fun A B f g H x => eq_ind_r (fun f0 => f0 x = g x) eq_refl H.
Monomorphic Definition equal_f
: forall A B (f g : A -> B), f = g -> forall x : A, f x = g x
  := fun A B => @equal_f_dep _ _.
*)
Lemma fg_equal : forall A B (f g : A -> B), f = g -> forall x : A, f x = g x.
Proof.
  intros A B f g []; reflexivity.
Qed.

Section telescope.
  Inductive telescope :=
  | Base : forall (A : Type) (B : A -> Type), (forall a, B a) -> (forall a, B a) -> telescope
  | Quant : forall A : Type, (A -> telescope) -> telescope.

  Fixpoint telescopeOut (t : telescope) :=
    match t with
      | Base _ _ x y => x = y
      | Quant _ f => forall x, telescopeOut (f x)
    end.

  Fixpoint telescopeOut' (t : telescope) :=
    match t with
      | Base _ _ f g => forall x, f x = g x
      | Quant _ f => forall x, telescopeOut' (f x)
    end.

  Theorem generalized_fg_equal : forall (t : telescope),
    telescopeOut t
    -> telescopeOut' t.
  Proof.
    induction t; simpl;
    repeat (intros [] || intro); trivial;
    apply_hyp.
  Qed.
End telescope.

Ltac curry_in_Quant H :=
  match eval simpl in H with
    | @Quant (@Common_sigT ?T1 ?T2) (fun xy => @?f xy) => curry_in_Quant (@Quant T1 (fun x => @Quant (T2 x) (fun y => f (@Common_existT T1 T2 x y))))
    | ?H' => H'
  end.

Ltac reifyToTelescope' H := let HT := type of H in let H' := uncurryT HT in
  match H' with
    | @eq ?T ?f ?g => let T' := eval hnf in T in
      match T' with
        | forall x : ?a, @?b x => constr:(@Base a b f g)
      end
    | forall x, @eq (@?T x) (@?f x) (@?g x) => let T' := eval hnf in T in (* XXX does [hnf] even do anything on [(fun _ => _)]?  I want to do [hnf] inside the function, but I don't want to do [compute] *)
      match T' with
        | (fun x => forall y : @?a x, @?b x y) => constr:(Quant (fun x => @Base (a x) (b x) (f x) (g x)))
      end
  end.

Ltac reifyToTelescope H := let t' := reifyToTelescope' H in curry_in_Quant t'.
Ltac fg_equal_in H := let t := reifyToTelescope H in apply (generalized_fg_equal t) in H; simpl in H.

Ltac fg_equal :=
  repeat match goal with
           | [ H : _ |- _ ] => fg_equal_in H
         end.

(*Ltac split_sig' :=
  match goal with
    | [ H : sig _ |- _ ]
      => let H' := uncurry H in
         let H'' :=

Goal forall T, (forall (x : T) (P : T -> Prop), sig P) -> True.
  intros T H.
  let t' := uncurry H in pose t'.
  reifyToTelescope H.*)

Lemma f_equal_helper A0 (A B : A0 -> Type) (f : forall a0, A a0 -> B a0) (x y : forall a0, A a0) :
  (forall a0, x a0 = y a0) -> (forall a0, f a0 (x a0) = f a0 (y a0)).
  intros H a0; specialize (H a0); rewrite H; reflexivity.
Qed.

(*Local Notation f_equal := ap.*)

Ltac f_equal_in_r H k := let H' := uncurry H in let H'T := type of H' in
  let k' := (fun v => let v' := curry v in let H := fresh in assert (H := v'); simpl in H) in
    match eval simpl in H'T with
      | @eq ?A ?x ?y => k (fun B (f : A -> B) => @f_equal A B f x y H') k'
      | forall a0 : ?A0, @eq (@?A a0) (@?x a0) (@?y a0)
        => k (fun (B : A0 -> Type) (f : forall a0 : A0, A a0 -> B a0) => @f_equal_helper A0 A B f x y H') k'
    end; clear H.
Ltac f_equal_in f H := f_equal_in_r H ltac:(fun pf k => k (pf _ f)).

Ltac eta_red :=
  repeat match goal with
           | [ H : appcontext[fun x => ?f x] |- _ ] => change (fun x => f x) with f in H
           | [ |- appcontext[fun x => ?f x] ] => change (fun x => f x) with f
         end.

Lemma sigT_eta : forall A (P : A -> Type) (x : sigT P),
  x = existT _ (projT1 x) (projT2 x).
  destruct x; reflexivity.
Qed.
(*
Lemma sigT_eta_2 A B P (x : @sigT A (fun a : A => @sigT (B a) (P a)))
: (x.1; (x.2.1; x.2.2)) = x.
Proof.
  destruct x as [? [? ?]].
  reflexivity.
Qed.

Lemma sigT2_eta : forall A (P Q : A -> Type) (x : sigT2 P Q),
  x = existT2 _ _ (projT1 x) (projT2 x) (projT3 x).
  destruct x; reflexivity.
Qed.
(*
Lemma sig_eta : forall A (P : A -> Prop) (x : sig P),
  x = exist _ (proj1_sig x) (proj2_sig x).
  destruct x; reflexivity.
Qed.

Lemma sig2_eta : forall A (P Q : A -> Prop) (x : sig2 P Q),
  x = exist2 _ _ (proj1_sig x) (proj2_sig x) (proj3_sig x).
  destruct x; reflexivity.
Qed.
*)

Ltac rewrite_eta_in Hf :=
  repeat match type of Hf with
(*           | context[match ?E with existT2 _ _ _ => _ end] => rewrite (sigT2_eta E) in Hf; simpl in Hf
           | context[match ?E with exist2 _ _ _ => _ end] => rewrite (sig2_eta E) in Hf; simpl in Hf*)
           | context[match ?E with existT _ _ => _ end] => rewrite (sigT_eta E) in Hf; simpl in Hf
(*           | context[match ?E with exist _ _ => _ end] => rewrite (sig_eta E) in Hf; simpl in Hf*)
           | context[match ?E with pair _ _ => _ end] => rewrite (eta_prod E) in Hf; simpl in Hf
         end.

Ltac destruct_match_in' T :=
  match T with
    | appcontext[match ?E with _ => _ end] => let x := fresh in set (x := E) in *; destruct x
  end.

Ltac destruct_match_in T :=
  repeat match T with
           | appcontext[match ?E with _ => _ end] => let x := fresh in set (x := E) in *; destruct x
         end.

Ltac destruct_match_in_goal :=
  repeat match goal with
           | [ |- appcontext[match ?E with _ => _ end] ] => let x := fresh in set (x := E) in *; destruct x
         end.

Ltac destruct_match_in_hyp Hf :=
  repeat (let T := type of Hf in
          destruct_match_in' T).

Ltac rewrite_eta :=
  repeat match goal with
           | [ |- context[match ?E with existT2 _ _ _ => _ end] ] => rewrite (sigT2_eta E); simpl
(*           | [ |- context[match ?E with exist2 _ _ _ => _ end] ] => rewrite (sig2_eta E); simpl*)
           | [ |- context[match ?E with existT _ _ => _ end] ] => rewrite (sigT_eta E); simpl
(*           | [ |- context[match ?E with exist _ _ => _ end] ] => rewrite (sig_eta E); simpl*)
           | [ |- context[match ?E with pair _ _ => _ end] ] => rewrite (eta_prod E); simpl
         end.
(*
Ltac intro_proj2_sig_from_goal'_by tac :=
  repeat match goal with
           | [ |- appcontext[proj1_sig ?x] ] => tac (proj2_sig x)
           | [ |- appcontext[proj1_sig (sig_of_sig2 ?x)] ] => tac (proj3_sig x)
         end.

Ltac intro_proj2_sig_from_goal_by tac :=
  repeat match goal with
           | [ |- appcontext[proj1_sig ?x] ] => tac (proj2_sig x)
           | [ |- appcontext[proj1_sig (sig_of_sig2 ?x)] ] => tac (proj3_sig x)
         end; simpl in *.
*)
Ltac intro_projT2_from_goal_by tac :=
  repeat match goal with
           | [ |- appcontext[projT1 ?x] ] => tac (projT2 x)
           | [ |- appcontext[projT1 (sigT_of_sigT2 ?x)] ] => tac (projT3 x)
         end; simpl in *.
(*
Ltac intro_proj2_sig_by tac :=
  repeat match goal with
           | [ |- appcontext[proj1_sig ?x] ] => tac (proj2_sig x)
           | [ H : appcontext[proj1_sig ?x] |- _ ] => tac (proj2_sig x)
           | [ H := appcontext[proj1_sig ?x] |- _ ] => tac (proj2_sig x)
           | [ |- appcontext[proj1_sig (sig_of_sig2 ?x)] ] => tac (proj3_sig x)
           | [ H : appcontext[proj1_sig (sig_of_sig2 ?x)] |- _ ] => tac (proj3_sig x)
           | [ H := appcontext[proj1_sig (sig_of_sig2 ?x)] |- _ ] => tac (proj3_sig x)
         end; simpl in *.
*)
Ltac intro_projT2_by tac :=
  repeat match goal with
           | [ |- appcontext[projT1 ?x] ] => tac (projT2 x)
           | [ H : appcontext[projT1 ?x] |- _ ] => tac (projT2 x)
           | [ H := appcontext[projT1 ?x] |- _ ] => tac (projT2 x)
           | [ |- appcontext[projT1 (sigT_of_sigT2 ?x)] ] => tac (projT3 x)
           | [ H : appcontext[projT1 (sigT_of_sigT2 ?x)] |- _ ] => tac (projT3 x)
           | [ H := appcontext[projT1 (sigT_of_sigT2 ?x)] |- _ ] => tac (projT3 x)
         end; simpl in *.

(*
Ltac intro_proj2_sig_from_goal' := intro_proj2_sig_from_goal'_by unique_pose.
Ltac intro_proj2_sig_from_goal := intro_proj2_sig_from_goal_by unique_pose.*)
Ltac intro_projT2_from_goal := intro_projT2_from_goal_by unique_pose.
Ltac intro_projT2_from_goal_with_body := intro_projT2_from_goal_by unique_pose_with_body.
(*Ltac intro_proj2_sig := intro_proj2_sig_by unique_pose.*)
Ltac intro_projT2 := intro_projT2_by unique_pose.
Ltac intro_projT2_with_body := intro_projT2_by unique_pose_with_body.

Ltac recr_destruct_with tac H :=
  let H0 := fresh in let H1 := fresh in
    (tac H; try reflexivity; try clear H) ||
      (destruct H as [ H0 H1 ];
        simpl in H0, H1;
          recr_destruct_with tac H0 || recr_destruct_with tac H1;
            try clear H0; try clear H1).

Ltac do_rewrite H := rewrite H.
Ltac do_rewrite_rev H := rewrite <- H.
Ltac recr_destruct_rewrite H := recr_destruct_with do_rewrite H.
Ltac recr_destruct_rewrite_rev H := recr_destruct_with do_rewrite_rev H.

(*
Ltac use_proj2_sig_with tac :=
  repeat match goal with
           | [ |- appcontext[proj1_sig ?x] ] =>
             match x with
               | context[proj1_sig] => fail 1
               | _ => simpl_do_clear tac (proj2_sig x)
             end
         end.

Ltac rewrite_proj2_sig := use_proj2_sig_with recr_destruct_rewrite.
Ltac rewrite_rev_proj2_sig := use_proj2_sig_with recr_destruct_rewrite_rev.
*)
Definition is_unique (A : Type) (x : A) := forall x' : A, x' = x.
Implicit Arguments is_unique [A].

Ltac rewrite_unique :=
  match goal with
    | [ H : is_unique _ |- _ ] => unfold is_unique in H; rewrite H || rewrite <- H; reflexivity
  end.

Ltac generalize_is_unique_hyp H T :=
  assert (forall a b : T, a = b) by (intros; etransitivity; apply H || symmetry; apply H); clear H.

Ltac generalize_is_unique :=
  repeat match goal with
           | [ H : @is_unique ?T _ |- _ ] => generalize_is_unique_hyp H T
         end.

Ltac intro_fresh_unique :=
  repeat match goal with
           | [ H : @is_unique ?T ?x |- _ ] => let x' := fresh in assert (x' := x); rewrite <- (H x') in *; generalize_is_unique_hyp H T
         end.

Ltac specialize_with_evars_then_do E tac :=
  lazymatch type of E with
    | forall x : ?T, _ =>
      let y := fresh in evar (y : T);
        let y' := (eval unfold y in y) in clear y;
          specialize_with_evars_then_do (E y') tac
    | _ => tac E
  end.

Ltac specialize_hyp_with_evars E :=
  repeat match type of E with
           | forall x : ?T, _ =>
             let y := fresh in evar (y : T);
               let y' := (eval unfold y in y) in clear y;
                 specialize (E y')
         end.

(* tries to convert an existential to an evar *)
Ltac existential_to_evar x :=
  is_evar x;
  let x' := fresh in
  set (x' := x) in *.

(* converts existentials in the goal into evars *)
Ltac existentials_to_evars_in_goal :=
  repeat match goal with
           | [ |- context[?x] ] => existential_to_evar x
         end.

(* converts all the existentials in the hypotheses to evars *)
Ltac existentials_to_evars_in_hyps :=
  repeat match goal with
           | [ H : context[?x] |- _ ] => existential_to_evar x
         end.

(* converts all the existentials in the hypothesis [H] to evars *)
Ltac existentials_to_evars_in H :=
  repeat match type of H with
           | context[?x] => existential_to_evar x
         end.

Tactic Notation "existentials_to_evars" := existentials_to_evars_in_goal.
Tactic Notation "existentials_to_evars" "in" "|-" "*" := existentials_to_evars_in_goal.
Tactic Notation "existentials_to_evars" "in" "*" := existentials_to_evars_in_goal; existentials_to_evars_in_hyps.
Tactic Notation "existentials_to_evars" "in" "*" "|-" := existentials_to_evars_in_hyps.
Tactic Notation "existentials_to_evars" "in" hyp(H) "|-" "*" := existentials_to_evars_in H; existentials_to_evars_in_goal.
Tactic Notation "existentials_to_evars" "in" hyp(H) := existentials_to_evars_in H.
Tactic Notation "existentials_to_evars" "in" hyp(H) "|-" := existentials_to_evars_in H.

(* rewrite fails if hypotheses depend on one another.  simultaneous rewrite does not *)
Ltac simultaneous_rewrite' E :=
  match type of E with
    | ?X = _ => generalize E; generalize dependent X; intros until 1;
      let H := fresh in intro H at top;
        match type of H with
          ?X' = _ => subst X'
        end
  end.

Ltac simultaneous_rewrite_rev' E :=
  match type of E with
    | _ = ?X => generalize E; generalize dependent X; intros until 1;
      let H := fresh in intro H at top;
        match type of H with
          _ = ?X' => subst X'
        end
  end.

Ltac simultaneous_rewrite E := specialize_with_evars_then_do E ltac:(fun E =>
  match type of E with
    | ?T = _ => let H := fresh in
      match goal with
        | [ _ : context[?F] |- _ ] =>
          assert (H : T = F) by reflexivity; clear H
      end; simultaneous_rewrite' E
  end
).

Ltac simultaneous_rewrite_rev E := specialize_with_evars_then_do E ltac:(fun E =>
  match type of E with
    | _ = ?T => let H := fresh in
      match goal with
        | [ _ : context[?F] |- _ ] =>
          assert (H : T = F) by reflexivity; clear H
      end; simultaneous_rewrite_rev' E
  end
).

(* rewrite by convertiblity rather than syntactic equality *)
Ltac conv_rewrite_with rew_tac H := specialize_with_evars_then_do H ltac:(fun H =>
  lazymatch type of H with
    | ?a = _ => match goal with
                  | [ |- appcontext[?a'] ]
                    => change a' with a; rew_tac H
                end
  end
).
Ltac conv_rewrite_rev_with rew_tac H := specialize_with_evars_then_do H ltac:(fun H =>
  lazymatch type of H with
    | _ = ?a => match goal with
                  | [ |- appcontext[?a'] ]
                    => change a' with a; rew_tac H
                end
  end
).

Ltac conv_rewrite H := conv_rewrite_with ltac:(fun h => rewrite h) H.
Ltac conv_rewrite_rev H := conv_rewrite_rev_with ltac:(fun h => rewrite <- h) H.
Ltac conv_repeat_rewrite H := repeat conv_rewrite_with ltac:(fun h => repeat rewrite h) H.
Ltac conv_repeat_rewrite_rev H := repeat conv_rewrite_rev_with ltac:(fun h => repeat rewrite <- h) H.

Ltac rewrite_by_context ctx H :=
  match type of H with
    | ?x = ?y => let ctx' := context ctx[x] in let ctx'' := context ctx[y] in
      cut ctx'; [ let H' := fresh in intro H'; simpl in H' |- *; exact H' | ];
        cut ctx''; [ let H' := fresh in intro H'; etransitivity; try apply H'; rewrite H; reflexivity
          |
        ]
  end.

Ltac rewrite_rev_by_context ctx H :=
  match type of H with
    | ?x = ?y => let ctx' := context ctx[y] in let ctx'' := context ctx[x] in
      cut ctx'; [ let H' := fresh in intro H'; simpl in H' |- *; exact H' | ];
        cut ctx''; [ let H' := fresh in intro H'; etransitivity; try apply H'; rewrite <- H; reflexivity
          |
        ]
  end.

Ltac do_for_each_hyp' tac fail_if_seen :=
  match goal with
    | [ H : _ |- _ ] => fail_if_seen H; tac H; try do_for_each_hyp' tac ltac:(fun H' => fail_if_seen H'; match H' with | H => fail 1 | _ => idtac end)
  end.
Ltac do_for_each_hyp tac := do_for_each_hyp' tac ltac:(fun H => idtac).

(* [change a with b in *] fails if it would create a self-referential hypothesis.
   This version does not. *)
Tactic Notation "change_in_all" constr(from) "with" constr(to) :=
  change from with to; do_for_each_hyp ltac:(fun H => change from with to in H).

(* [expand] replaces both terms of an equality (either [eq] or [JMeq]
   in the goal with their head normal forms *)
Ltac expand :=
  match goal with
    | [ |- @eq ?T ?X ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (@eq T X' Y')
    | [ |- ?X == ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' == Y')
  end; simpl.


Ltac pre_abstract_trailing_props_helper T B Rel :=
  cut { A : T | Rel A B };
  [ let x := fresh in intro x; exists (proj1_sig x); destruct x as [ ? x ]; unfold proj1_sig; destruct x; reflexivity
  | ].

Ltac pre_abstract_trailing_props :=
  match goal with
    | [ |- { F0 : ?T | @?P F0 } ] => let T' := eval hnf in T in change { F0 : T' | P F0 }; cbv beta
  end;
  try match goal with
        | [ |- { A : ?T | identity A ?B } ] => pre_abstract_trailing_props_helper T B (@eq T)
        | [ |- { A : ?T | identity ?B A } ] => pre_abstract_trailing_props_helper T B (@eq T)
        | [ |- { A : ?T | ?B = A } ] => pre_abstract_trailing_props_helper T B (@eq T)
(*        | [ |- { A : ?T | @JMeq ?TB ?B ?T A } ] => pre_abstract_trailing_props_helper T B (fun a b => @JMeq T a TB b)*)
      end.

Ltac clear_then_exact pf :=
  match goal with
    | [ H : _ |- _ ] => clear H; clear_then_exact pf
    | _ => abstract (exact pf)
  end.

Ltac do_replace_trailing_matching_with_goal term matcher tac :=
  match term with
    | ?f ?x => (first [ (matcher x;
                         let t := type of x in
                         let t' := (eval simpl in t) in
                         let y := fresh in
                         assert (y : t') by ((clear; abstract (exact x)) || clear_then_exact x);
                         (do_replace_trailing_matching_with_goal f matcher ltac:(fun H => tac (H y)))
                           || fail 2 "tactic failed")
                      | (tac term || fail 1 "tactic failed") ])
    | _ => tac term || fail 1 "tactic failed"
  end.

Ltac exact_replace_trailing_matching_with_goal term matcher :=
  do_replace_trailing_matching_with_goal term matcher ltac:(fun H => exact H).

Ltac type_of_type_of_matches T :=
  fun term =>
    let t := type of term in
    let t' := type of t in
    match eval hnf in t' with
      | T => idtac
    end.

Ltac abstract_trailing_props term :=
  let term' := (eval hnf in term) in
  exact_replace_trailing_matching_with_goal term' ltac:(type_of_type_of_matches Prop).

Ltac hnf_simpl_abstract_trailing_props term :=
  let term' := (eval hnf in term) in
  let term'' := (eval simpl in term') in
  exact_replace_trailing_matching_with_goal term'' ltac:(type_of_type_of_matches Prop).

Ltac evar_evar_Type t :=
  let T := fresh in evar (T : Type); evar (t : T); subst T.

(* [hideProof' pf] generalizes [pf] only if it does not already exist
   as a hypothesis *)
Ltac hideProof' pf :=
  match goal with
    | [ x : _ |- _ ] => match x with
                          | pf => fail 2
                        end
    | _ => generalize pf; intro
  end.

(* TODO(jgross): Is there a better way to do this? *)
Tactic Notation "hideProofs" constr(pf)
  := hideProof' pf.
Tactic Notation "hideProofs" constr(pf0) constr(pf1)
  := progress (try hideProof' pf0; try hideProof' pf1).
Tactic Notation "hideProofs" constr(pf0) constr(pf1) constr(pf2)
  := progress (try hideProof' pf0; try hideProof' pf1; try hideProof' pf2).
Tactic Notation "hideProofs" constr(pf0) constr(pf1) constr(pf2) constr(pf3)
  := progress (try hideProof' pf0; try hideProof' pf1; try hideProof' pf2; try hideProof' pf3).
Tactic Notation "hideProofs" constr(pf0) constr(pf1) constr(pf2) constr(pf3) constr(pf4)
  := progress (try hideProof' pf0; try hideProof' pf1; try hideProof' pf2; try hideProof' pf3; try hideProof' pf4).
Tactic Notation "hideProofs" constr(pf0) constr(pf1) constr(pf2) constr(pf3) constr(pf4) constr(pf5)
  := progress (try hideProof' pf0; try hideProof' pf1; try hideProof' pf2; try hideProof' pf3; try hideProof' pf4; try hideProof' pf5).

Section unique.
  Definition uniqueT (A : Type) (P : A -> Type) (x : A)
    := P x + forall x' : A, P x' -> x = x'.
End unique.

Ltac destruct_to_empty_set :=
  match goal with
    | [ H : Empty |- _ ] => destruct H
    | [ H : ?T -> Empty, a : ?T |- _ ] => destruct (H a)
    | [ H : context[Empty] |- _ ] => solve [ destruct H; trivial; assumption ]
  end.

Ltac destruct_to_empty_set_in_match :=
  match goal with
    | [ |- appcontext[match ?x with end] ] => solve [ destruct x || let H := fresh in pose x as H; destruct H ]
    | [ _ : appcontext[match ?x with end] |- _ ] => solve [ destruct x || let H := fresh in pose x as H; destruct H ]
  end.

Ltac destruct_first_if_not_second a b :=
  (constr_eq a b; fail 1)
    || (let t := type of b in
        let H := fresh in
        set (H := a : t) in *;
          destruct H).

Ltac destruct_singleton_constructor c :=
  let t := type of c in
  repeat match goal with
           | [ H : t |- _ ] => destruct H
           | [ H : context[?e] |- _ ] => destruct_first_if_not_second e c
           | [ |- context[?e] ] => destruct_first_if_not_second e c
         end.

Ltac destruct_units := destruct_singleton_constructor tt.
Ltac destruct_Trues := destruct_singleton_constructor I.
(*
Section contr.
  (** Contr taken from HoTT *)
  Class Contr (A : Type) :=
    {
      center : A ;
      contr : (forall y : A, center = y)
    }.

  Global Arguments center A {_}.

  Notation IsHProp A := (forall x y : A, Contr (x = y)).

  Global Instance ContrIsHProp `{Contr A} : IsHProp A.
  Proof.
    repeat intro.
    exists (match contr x, contr y with eq_refl, eq_refl => eq_refl end).
    intro H0.
    destruct H0.
    destruct (contr x).
    reflexivity.
  Defined.

  Global Instance ContrIsHProp' `{Contr A} (x y : A) : Contr (x = y).
  Proof (ContrIsHProp x y).

  Lemma contr_eq A : forall x y : Contr A, x = y.
  Proof.
    repeat intro.
    pose x as x'; destruct x as [ centerx contrx ].
    pose y as y'; destruct y as [ centery contry ].
    destruct (contry centerx).
    apply f_equal.
    apply functional_extensionality_dep.
    intros.
    apply center.
    eauto with typeclass_instances.
  Defined.

  Global Instance PiContr `(H : forall x : A, Contr (T x)) : Contr (forall x, T x).
  Proof.
    exists (fun _ => center _).
    intros; apply functional_extensionality_dep.
    intros; apply contr.
  Defined.

  Global Instance SigmaContr `{Contr A} `{forall x : A, Contr (P x)} : Contr (sigT P).
  Proof.
    exists (existT P (center _) (center _)).
    intros [x ?].
    cut (center _ = x); [ intro; subst | apply contr ].
    apply f_equal.
    apply contr.
  Defined.

  Global Instance SigContr `{Contr A} (P : A -> Prop) `{forall x : A, Contr (P x)} : Contr (sig P).
  Proof.
    exists (exist P (center _) (center _)).
    intros [x ?].
    cut (center _ = x); [ intro; subst | apply contr ].
    apply f_equal.
    apply contr.
  Defined.

  Global Instance Sigma2Contr `{Contr A} `{forall x : A, Contr (P x)} `{forall x : A, Contr (Q x)} : Contr (sigT2 P Q).
  Proof.
    exists (existT2 P Q (center _) (center _) (center _)).
    intros [x ? ?].
    cut (center _ = x); [ intro; subst | apply contr ].
    apply f_equal2;
      apply contr.
  Defined.


  Global Instance Sig2Contr `{Contr A} (P Q : A -> Prop) `{forall x : A, Contr (P x)} `{forall x : A, Contr (Q x)} : Contr (sig2 P Q).
  Proof.
    exists (exist2 P Q (center _) (center _) (center _)).
    intros [x ? ?].
    cut (center _ = x); [ intro; subst | apply contr ].
    apply f_equal2;
      apply contr.
  Defined.

  Local Ltac contr_eq_t :=
    intros;
    repeat match goal with
             | [ x : _ |- _ ] => progress destruct (contr x)
           end;
    reflexivity.

  Lemma contr_eqT `{Contr A} : forall x x' y y' : A, @eq Type (x = x') (y = y').
    contr_eq_t.
  Defined.

  Lemma contr_eqS `{Contr A} : forall x x' y y' : A, @eq Set (x = x') (y = y').
    contr_eq_t.
  Defined.

  Lemma contr_eqP `{Contr A} : forall x x' y y' : A, @eq Prop (x = x') (y = y').
    contr_eq_t.
  Defined.
End contr.

Notation IsHProp A := (forall x y : A, Contr (x = y)).
*)(*
Section True.
  Global Instance True_contr : Contr True
    := @BuildContr True I (fun x => match x with I => idpath end).

  Definition True_singleton u : u = I := @symmetry True (@eq True) _ I u (contr u).
  Definition True_eq (u u' : True) : u = u' := center _.
  Definition True_eq_singleton (u u' : True) (H : u = u') : H = True_eq _ _ := center _.
  Definition True_eq_eq (u u' : True) (H H' : u = u') : H = H' := center _.

(*  Lemma True_JMeq (u u' : True) : u == u'.
    case u; case u'; reflexivity.
  Defined.*)
(*
  Definition True_eqT_eq (u u' v v' : True) : @eq Type (u = u') (v = v') := contr_eqT _ _ _ _.
  Definition True_eqS_eq (u u' v v' : True) : @eq Set (u = u') (v = v') := contr_eqS _ _ _ _.
  Definition True_eqP_eq (u u' v v' : True) : @eq Prop (u = u') (v = v') := contr_eqP _ _ _ _.
*)(*
  Lemma True_eq_JMeq (u u' v v' : True) (H : u = u') (H' : v = v') : H == H'.
    destruct_head @eq; destruct_head True; reflexivity.
  Defined.
*)
  Global Instance FalseIsHProp : IsHProp False.
  Proof.
    intros [].
  Defined.
Print center.
  Definition False_eq (a b : False) : a = b := @center _ (FalseIsHProp  _.

  Lemma False_JMeql (a : False) T (b : T) : a == b.
    destruct a.
  Defined.

  Lemma False_JMeqr T (a : T) (b : False) : a == b.
    destruct b.
  Defined.
End True.

Section unit.
  Global Instance unit_contr : Contr unit
    := @Build_Contr unit tt (fun x => match x with tt => eq_refl end).

  Definition unit_singleton u : u = tt := eq_sym (contr u).
  Definition unit_eq (u u' : unit) : u = u' := center _.
  Definition unit_eq_singleton (u u' : unit) (H : u = u') : H = unit_eq _ _ := center _.
  Definition unit_eq_eq (u u' : unit) (H H' : u = u') : H = H' := center _.

  Lemma unit_JMeq (u u' : unit) : u == u'.
    case u; case u'; reflexivity.
  Defined.

  Definition unit_eqT_eq (u u' v v' : unit) : @eq Type (u = u') (v = v') := contr_eqT _ _ _ _.
  Definition unit_eqS_eq (u u' v v' : unit) : @eq Set (u = u') (v = v') := contr_eqS _ _ _ _.
  Definition unit_eqP_eq (u u' v v' : unit) : @eq Prop (u = u') (v = v') := contr_eqP _ _ _ _.

  Lemma unit_eq_JMeq (u u' v v' : unit) (H : u = u') (H' : v = v') : H == H'.
    destruct_head @eq; destruct_head unit; reflexivity.
  Defined.

  Global Instance Empty_setIsHProp : IsHProp Empty_set.
  Proof.
    intros [].
  Defined.

  Definition Empty_set_eq (a b : Empty_set) : a = b := center _.

  Lemma Empty_set_JMeql (a : Empty_set) T (b : T) : a == b.
    destruct a.
  Defined.

  Lemma Empty_set_JMeqr T (a : T) (b : Empty_set) : a == b.
    destruct b.
  Defined.
End unit.

Hint Rewrite True_singleton.
Hint Extern 0 (@eq True _ _) => apply True_eq.
Hint Extern 0 (@eq (@eq True _ _) _ _) => apply True_eq_eq.
Hint Extern 0 (@JMeq True _ True _) => apply True_JMeq.
Hint Extern 0 (@JMeq (@eq True _ _) _ (@eq True _ _) _) => apply True_eq_JMeq.
Hint Extern 0 (@eq Set (@eq True _ _) (@eq True _ _)) => apply True_eqS_eq.
Hint Extern 0 (@eq Prop (@eq True _ _) (@eq True _ _)) => apply True_eqP_eq.
Hint Extern 0 (@eq Type (@eq True _ _) (@eq True _ _)) => apply True_eqT_eq.
Hint Extern 0 True => constructor.
Hint Extern 0 (@eq False _ _) => apply False_eq.
Hint Extern 0 (@JMeq False _ _ _) => apply False_JMeql.
Hint Extern 0 (@JMeq _ _ False _) => apply False_JMeqr.

Hint Rewrite unit_singleton.
Hint Extern 0 (@eq unit _ _) => apply unit_eq.
Hint Extern 0 (@eq (@eq unit _ _) _ _) => apply unit_eq_eq.
Hint Extern 0 (@JMeq unit _ unit _) => apply unit_JMeq.
Hint Extern 0 (@JMeq (@eq unit _ _) _ (@eq unit _ _) _) => apply unit_eq_JMeq.
Hint Extern 0 (@eq Set (@eq unit _ _) (@eq unit _ _)) => apply unit_eqS_eq.
Hint Extern 0 (@eq Prop (@eq unit _ _) (@eq unit _ _)) => apply unit_eqP_eq.
Hint Extern 0 (@eq Type (@eq unit _ _) (@eq unit _ _)) => apply unit_eqT_eq.
Hint Extern 0 unit => constructor.
Hint Extern 0 (@eq Empty_set _ _) => apply Empty_set_eq.
Hint Extern 0 (@JMeq Empty_set _ _ _) => apply Empty_set_JMeql.
Hint Extern 0 (@JMeq _ _ Empty_set _) => apply Empty_set_JMeqr.
*)
(* The following makes Examples.v slower by about a minute *)
(* Hint Extern 0 (@eq _ _ _) => try solve [ refine (center _) ]. *)


(** Fixes for HoTT library **)

Notation "0" := (trunc_S (trunc_S minus_two)) : trunc_scope.
Notation "1" := (trunc_S 0) : trunc_scope.
Notation "2" := (trunc_S 1) : trunc_scope.
Notation "3" := (trunc_S 3) : trunc_scope.

Tactic Notation "subst" :=
  repeat match goal with
           | [ H : ?x = ?y |- _ ]
             => is_var y; (destruct H || induction H)
           | [ H : ?x = ?y |- _ ]
             => is_var x; symmetry in H;
                (destruct H || induction H)
         end.

Lemma transport_projT1_path_sigma_uncurried
      A (P : A -> Type) (u v : sigT P)
      (pq : { p : u.1 = v.1 & transport P p u.2 = v.2 })
      Q Qx
: transport (fun x => Q x.1) (@path_sigma_uncurried A P u v pq) Qx
  = transport _ pq.1 Qx.
Proof.
  destruct pq as [p q], u, v; simpl in *.
  destruct p, q; simpl in *.
  reflexivity.
Defined.

Lemma transport_path_prod_uncurried A B (P : A * B -> Type) (x y : A * B)
      (H : (fst x = fst y) * (snd x = snd y))
      Px
: transport P (path_prod_uncurried _ _ H) Px
  = match y as y' return P (fst y', snd y') -> P y' with
      | (_, _) => idmap
    end (transport (fun x => P (x, snd y))
                   (fst H)
                   (transport (fun y => P (fst x, y))
                              (snd H)
                              (match x as x' return P x' -> P (fst x', snd x') with
                                 | (_, _) => idmap
                               end Px))).
Proof.
  destruct x, y, H; simpl in *.
  path_induction.
  reflexivity.
Defined.

Definition transport_path_prod A B (P : A * B -> Type) (x y : A * B)
           (HA : fst x = fst y)
           (HB : snd x = snd y)
           Px
: transport P (path_prod _ _ HA HB) Px
  = match y as y' return P (fst y', snd y') -> P y' with
      | (_, _) => idmap
    end (transport (fun x => P (x, snd y))
                   HA
                   (transport (fun y => P (fst x, y))
                              HB
                              (match x as x' return P x' -> P (fst x', snd x') with
                                 | (_, _) => idmap
                               end Px)))
  := transport_path_prod_uncurried P x y (HA, HB) Px.

Definition transport_path_prod'
           A B (P : A * B -> Type)
           (x y : A)
           (x' y' : B)
           (HA : x = y)
           (HB : x' = y')
           Px
: transport P (path_prod' HA HB) Px
  = transport (fun x => P (x, y'))
              HA
              (transport (fun y => P (x, y))
                         HB
                         Px)
  := transport_path_prod P (x, x') (y, y') HA HB Px.

(** A variant of [induction] which also tries [destruct] and [case], and may be extended to using other [destruct]-like tactics. *)
Ltac induction_hammer H :=
  destruct H || induction H || (case H; clear H).

(** Takes a term of type [_ = _], and tries to replace it by [idpath] by trying to prove that it's an hProp. *)
Ltac clear_contr_path p :=
  let H := fresh in
  let T := type of p in
  progress (
      first [ assert (H : idpath = p) by exact (center _)
            | assert (H : idpath = p)
              by (
                  let a := match goal with |- @eq (?x = ?y) ?a ?b => constr:(a) end in
                  let b := match goal with |- @eq (?x = ?y) ?a ?b => constr:(b) end in
                  let x := match goal with |- @eq (?x = ?y) ?a ?b => constr:(x) end in
                  let y := match goal with |- @eq (?x = ?y) ?a ?b => constr:(y) end in
                  apply (@equiv_inv _ _ _ (@equiv_ap _ _ _ (@isequiv_apD10 _ _ _ x y) a b));
                  exact (center _)
                )
            | pose proof (@path_contr T _ idpath p) as H ];
      destruct H;
      (* now reduce any matches on [idpath] (and on other things too) *)
      cbv iota in *
    ).

(** Use both [induction_hammer] and [clear_contr_path] on a path, to try to get rid of it *)
Ltac clear_path_no_check p :=
  induction_hammer p || clear_contr_path p.
Ltac clear_path p :=
  let t := type of p in
  lazymatch eval hnf in t with
    | @eq _ _ _ => clear_path_no_check p
    | _ => fail 0 "clear_path only works on eq;" p "is not a path"
  end.

(** Run [clear_path] on hypotheses *)
(** We don't match only on things of type [_ = _], because maybe that's the head normal form, but it's hiding behind something else; [clear_path] will make sure it's of the right type.  We include some redundant cases at the top, for speed; it is faster to try to destruct everything first, and then do the full battery of tactics, than to just run the hammer. *)
Ltac step_clear_eq :=
  match goal with
    | [ p : _ = _ |- _ ] => destruct p
    | [ p : _ = _ |- _ ] => clear_path_no_check p
    | [ p : _ |- _ ] => clear_path p
  end.
Ltac clear_eq := progress repeat step_clear_eq.

(** Run [clear_path] on anything inside a [match] *)
Ltac step_clear_eq_in_match :=
  match goal with
    | [ |- appcontext[match ?p with idpath => _ end] ] => progress destruct p
    | [ |- appcontext[match ?p with idpath => _ end] ] => clear_path_no_check p
  end.
Ltac clear_eq_in_match := progress repeat step_clear_eq_in_match.

(** Now some lemmas about trivial [match]es *)
Definition match_eta T (x y : T) (H0 : x = y)
: (H0 = match H0 in (_ = y) return (x = y) with
          | idpath => idpath
        end)
  := match H0 with idpath => idpath end.

Definition match_eta1 T (x : T) (E : x = x)
: (match E in (_ = y) return (x = y) with
     | idpath => idpath
   end = idpath)
  -> idpath = E
  := fun H => ((H # match_eta E) ^)%path.

Definition match_eta2 T (x : T) (E : x = x)
: (idpath
   = match E in (_ = y) return (x = y) with
       | idpath => idpath
     end)
  -> idpath = E
  := fun H => match_eta1 E (H ^)%path.

(** And now the actual tactic. *)
Ltac step_path_induction_hammer :=
  match goal with
    | _ => reflexivity
    | _ => intro
    | _ => progress simpl in *
    | _ => exact (contr _)
    | [ p : _ = _ |- _ ]
      => progress destruct p (* placed up here for speed *)
    | [ H : _ |- _ ]
      => let H' := fresh in assert (H' := match_eta1 _ H); destruct H'
    | [ H : _ |- _ ]
      => let H' := fresh in assert (H' := match_eta2 _ H); destruct H'
    | _ => step_clear_eq
    | _ => expand; step_clear_eq_in_match
    | _ => progress auto with path_hints
    | _ => done
    | _ => exact (center _)
  end.

Ltac path_induction_hammer := repeat step_path_induction_hammer.

Ltac do_unless_goal_has_evar tac :=
  match goal with
    | [ |- ?G ] => has_evar G; fail 1 "Goal has evars"
    | _ => idtac
  end;
  tac.

(*Hint Extern 100 => do_unless_goal_has_evar ltac:(apply @IsTrunc_path) : typeclass_instances.*)


(*Hint Extern 1 => progress cbv beta : typeclass_instances.*)
Hint Extern 0 => assumption : typeclass_instances.
Hint Extern 3 => progress cbv beta : typeclass_instances.
Hint Extern 1000 => progress simpl : typeclass_instances.
Hint Extern 1000 => progress intros : typeclass_instances.
(*Hint Extern 100 => do_unless_goal_has_evar ltac:(apply @IsTrunc_path') : typeclass_instances.*)
(*Hint Extern 0 => match goal with
                   | [ |- appcontext[(fun _ => _) _] ] => cbv beta
                 end : typeclass_instances.*)

Global Instance trunc_pointwise_eq `{Funext} A B (f g : forall x : A, B x) `{IsTrunc n (f = g)}
: IsTrunc n (f == g) | 1000
  := @trunc_equiv' _ _ (symmetry _ _ (equiv_path_forall _ _)) _ _.
(*Global Instance trunc_contr `{H : forall (x y : T) (pf1 pf2 : x = y), Contr (pf1 = pf2)} : IsTrunc 0 T | 10000
  := H.*)

Definition unique A (P : A -> Type) (x : A)
  := P x /\ forall x', P x' -> x = x'.

(** New to HoTT common file **)

Hint Extern 0 => apply false_ne_true; solve [ trivial ].
Hint Extern 0 => apply true_ne_false; solve [ trivial ].

Lemma transport_inverse A P x y p
: @transport A P x y p ^
  = ((@transport A P y x p) ^-1)%equiv.
Proof.
  path_induction; reflexivity.
Defined.

Definition transport_path_universe_fun `{Univalence} `{Funext}
           A B f `{IsEquiv A B f}
: transport idmap (path_universe f) = f.
Proof.
  apply path_forall; intro.
  apply transport_path_universe.
Defined.

Definition transport_path_universe_fun_inv `{Univalence} `{Funext}
           A B f `{IsEquiv A B f}
: ((transport idmap (path_universe f)) ^-1 = f ^-1)%equiv.
Proof.
  apply path_forall; intro.
  etransitivity; [ | apply transport_path_universe ].
  simpl.
  rewrite <- path_universe_V.
  reflexivity.
Defined.*)

Local Open Scope list_scope.
(** Takes two lists, and recursively iterates down their structure, unifying forced evars *)
Ltac structurally_unify_lists l1 l2 :=
  first [ constr_eq l1 l2
        | is_evar l1; unify l1 l2
        | is_evar l2; unify l2 l1
        | lazymatch l1 with
            | nil => match l2 with
                       | ?a ++ ?b => structurally_unify_lists l1 a; structurally_unify_lists l1 b
                       | _ => idtac
                     end
            | ((?a ++ ?b) ++ ?c) => structurally_unify_lists (a ++ (b ++ c)) l2
            | nil ++ ?a => structurally_unify_lists a l2
            | ?a ++ nil => structurally_unify_lists a l2
          end
        | lazymatch l2 with
            | nil => match l1 with
                       | ?a ++ ?b => structurally_unify_lists a l2; structurally_unify_lists b l2
                       | _ => idtac
                     end
            | ((?a ++ ?b) ++ ?c) => structurally_unify_lists l1 (a ++ (b ++ c))
            | nil ++ ?a => structurally_unify_lists l1 a
            | ?a ++ nil => structurally_unify_lists l1 a
          end
        | let l1l2 := constr:((l1, l2)) in
          match l1l2 with
            | (?a ++ ?b, ?a ++ ?b') => structurally_unify_lists b b'
            | (?a ++ ?b, ?a' ++ ?b) => structurally_unify_lists a a'
            | (?a ++ ?b, ?a) => let T := type_of b in structurally_unify_lists b (nil : T)
            | (?a ++ ?b, ?b) => let T := type_of a in structurally_unify_lists a (nil : T)
            | (?a, ?a ++ ?b) => let T := type_of b in structurally_unify_lists (nil : T) b
            | (?b, ?a ++ ?b) => let T := type_of a in structurally_unify_lists (nil : T) a
          end
        | idtac ].

(** Run a tactic associated with [tacClass] under as many binders as necessary until it succeeds. *)
(** In 8.5, this will be simpler:
<<
Ltac do_under_binders tac term := constr:(fun y => $(let z := tac (term y) in exact z)$).
Ltac do_under_forall_binders tac term :=
  let T := match term with forall x : ?T, @?P x => constr:(T) end in
  let P := match term with forall x, @?P x => constr:(P) end in
  constr:(forall y : T, $(let z := tac (P y) in exact z)$).
Ltac do_under_many_binders_helper under_binders tac term :=
  match term with
    | _ => tac term
    | _ => under_binders ltac:(do_under_many_binders_helper under_binders tac) term
  end.
Ltac do_under_many_binders tac term := do_under_many_binders_helper do_under_binders tac term.
Ltac do_under_many_forall_binders tac term := do_under_many_forall_binders_helper do_under_binders tac term.
>> *)
Ltac do_under_binders tacClass term := constr:(fun y => _ : tacClass _ (term y) _).
Ltac do_under_forall_binders tacClass term :=
  let T := match term with forall x : ?T, @?P x => constr:(T) end in
  let P := match term with forall x, @?P x => constr:(P) end in
  constr:(forall y : T, (_ : tacClass _ (P y) _)).
Class do_under_many_binders_class {tacClassT} (tacClass : tacClassT) {T} (term : T) {retT} := make_do_under_many_binders : retT.
Ltac do_under_many_binders tacClass term :=
  let tacClass_head := head tacClass in
  let ret := match (eval cbv beta delta [tacClass_head do_under_many_binders_class] in term) with
               | ?term' => constr:(_ : tacClass _ term' _)
               | ?term' => do_under_binders (@do_under_many_binders_class _ tacClass) term'
             end in
  eval cbv beta delta [tacClass_head do_under_many_binders_class] in ret.
Hint Extern 0 (do_under_many_binders_class ?tacClass ?term)
=> let ret := do_under_many_binders tacClass term in exact ret : typeclass_instances.

Class do_under_many_forall_binders_class {tacClassT} (tacClass : tacClassT) {T} (term : T) {retT} := make_do_under_many_forall_binders : retT.
Ltac do_under_many_forall_binders tacClass term :=
  let tacClass_head := head tacClass in
  let ret := match (eval cbv beta delta [tacClass_head do_under_many_forall_binders_class] in term) with
               | ?term' => constr:(_ : tacClass _ term' _)
               | ?term' => do_under_forall_binders (@do_under_many_forall_binders_class _ tacClass) term'
             end in
  eval cbv beta delta [tacClass_head do_under_many_forall_binders_class] in ret.
Hint Extern 0 (do_under_many_forall_binders_class ?tacClass ?term)
=> let ret := do_under_many_forall_binders tacClass term in exact ret : typeclass_instances.

Section test_do_under_many_binders.
  Let a := True.
  Let b := a.
  Let c := b.
  
  Ltac help_unfold_head term :=
    match eval cbv beta in term with
      | ?f ?x => let f' := help_unfold_head f in
                 constr:(f' x)
      | a     => constr:(a)
      | ?term' => let term'' := (eval unfold term' in term') in
                  help_unfold_head term''
      | ?term' => constr:(term')
    end.

  Class unfolder_helper {T} (term : T) {retT : Type} := make_unfolder_helper : retT.
  Hint Extern 0 (unfolder_helper (True -> ?term)) => let term' := help_unfold_head term in
                                                     exact (True -> term')
                                                     : typeclass_instances.

  Ltac unfold_until_a term := do_under_many_binders (@unfolder_helper) term.
  Ltac unfold_forall_until_a term := do_under_many_forall_binders (@unfolder_helper) term.

  Goal True.
    let term := constr:(fun (_ _ _ _ : Set) => True -> c) in
    let ret := unfold_until_a term in
    constr_eq ret ((fun (_ _ _ _ : Set) => True -> a) : Set -> Set -> Set -> Set -> Prop);
      pose ret as ret0.
    let term := constr:(forall _ _ _ _ : Set, True -> c) in
    let ret := unfold_forall_until_a term in
    constr_eq ret ((forall (_ _ _ _ : Set), True -> a) : Prop);
      pose ret as ret1.
  Abort.
End test_do_under_many_binders.


Lemma match_match_bool_option b T T' oT oF s n
: match match b return option T with
          | true => oT
          | false => oF
        end as o return T' o with
    | Some x => s x
    | None => n
  end
  = match b as b return T' (match b return option T with
                              | true => oT
                              | false => oF
                            end) with
      | true => match oT with
                  | Some x => s x
                  | None => n
                end
      | false => match oF with
                   | Some x => s x
                   | None => n
                 end
    end.
Proof. destruct b, oT, oF; reflexivity. Defined.
Lemma match_match_bool_pair b A B T xT xF P
: match match b return prod A B with
          | true => xT
          | false => xF
        end as p return T p with
    | (x, y) => P x y
  end
  = match b as b return T (match b as b return prod A B with
                             | true => xT
                             | false => xF
                           end) with
      | true => match xT with
                  | (x, y) => P x y
                end
      | false => match xF with
                   | (x, y) => P x y
                 end
    end.
Proof. destruct b, xT, xF; reflexivity. Defined.
Lemma match_pair_eta A B (p : prod A B) T P
: match p return T with
    | (x, y) => P x y
  end
  = P (fst p) (snd p).
Proof. destruct p; reflexivity. Defined.
Lemma match_bool_fn b A B xT xF
: match b as b return forall x : A, B b x with
    | true => xT
    | false => xF
  end
  = fun x : A => match b as b return B b x with
                   | true => xT x
                   | false => xF x
                 end.
Proof. destruct b; reflexivity. Defined.
Lemma match_option_fn T (b : option T) A B s n
: match b as b return forall x : A, B b x with
    | Some k => s k
    | None => n
  end
  = fun x : A => match b as b return B b x with
                   | Some k => s k x
                   | None => n x
                 end.
Proof. destruct b; reflexivity. Defined.
Lemma match_option_match_pair_eta A B (p : option (prod A B)) T Ps Pn
: match p return T with
    | Some k => match k return T with
                  | (x, y) => Ps x y
                end
    | None => Pn
  end
  = match p return T with
      | Some k => Ps (fst k) (snd k)
      | None => Pn
    end.
Proof. destruct p as [[? ?]|]; reflexivity. Defined.
Lemma match_option_match_pair_eta_fun A B (p : option (prod A B)) T T' a Ps Pn
: match p return T' with
    | Some k => match k as k return T k -> T' with
                  | (x, y) => Ps x y
                end (a k)
    | None => Pn
  end
  = match p return T' with
      | Some k => Ps (fst k) (snd k) (a (fst k, snd k))
      | None => Pn
    end.
Proof. destruct p as [[? ?]|]; reflexivity. Defined.
Lemma match_option_comm_1 T (p : option T) A B (f : forall x : A, B x) s n
: match p as p return B match p with
                          | Some k => s k
                          | None => n
                        end with
    | Some k => f (s k)
    | None => f n
  end
  = f match p return A with
        | Some k => s k
        | None => n
      end.
Proof. destruct p; reflexivity. Defined.
Lemma match_option_comm_2 T (p : option T) A B R (f : forall (x : A) (y : B x), R x y) (s1 : T -> A) (s2 : forall x : T, B (s1 x)) n1 n2
: match p as p return R match p with
                          | Some k => s1 k
                          | None => n1
                        end
                        match p as p return B match p with Some k => s1 k | None => n1 end with
                          | Some k => s2 k
                          | None => n2
                        end with
    | Some k => f (s1 k) (s2 k)
    | None => f n1 n2
  end
  = f match p return A with
        | Some k => s1 k
        | None => n1
      end
      match p as p return B match p with Some k => s1 k | None => n1 end with
        | Some k => s2 k
        | None => n2
      end.
Proof. destruct p; reflexivity. Defined.
Definition match_option_comm_1_const T (p : option T) A B (f : A -> B) s n
: (match p return B with
     | Some k => f (s k)
     | None => f n
   end)
  = (f match p return A with
         | Some k => s k
         | None => n
       end)
  := @match_option_comm_1 T p A _ f s n.
Definition match_option_comm_2_const T (p : option T) A B R (f : A -> B -> R) s1 s2 n1 n2
: (match p return R with
     | Some k => f (s1 k) (s2 k)
     | None => f n1 n2
   end)
  = (f match p return A with
         | Some k => s1 k
         | None => n1
       end
       match p return B with
         | Some k => s2 k
         | None => n2
       end)
  := @match_option_comm_2 T p A _ _ f s1 s2 n1 n2.
Lemma match_bool_comm_1 (b : bool) A B (F : forall x : A, B x) t f
: (if b as b return B (if b then t else f) then F t else F f)
  = F (if b then t else f).
Proof. destruct b; reflexivity. Defined.
Lemma match_bool_comm_2 (b : bool) A B R (F : forall (x : A) (y : B x), R x y) t1 f1 t2 f2
: (if b as b return R (if b then t1 else f1) (if b as b return B (if b then t1 else f1) then t2 else f2) then F t1 t2 else F f1 f2)
  = F (if b then t1 else f1) (if b as b return B (if b then t1 else f1) then t2 else f2).
Proof. destruct b; reflexivity. Defined.
Definition match_bool_comm_1_const (b : bool) A R (F : A -> R) t f
: (if b then F t else F f) = F (if b then t else f)
  := @match_bool_comm_1 b _ _ F t f.
Definition match_bool_comm_2_const (b : bool) A B R (F : A -> B -> R) t1 f1 t2 f2
: (if b then F t1 t2 else F f1 f2) = F (if b then t1 else f1) (if b then t2 else f2)
  := @match_bool_comm_2 b _ _ _ F t1 f1 t2 f2.
Lemma match_bool_const (b : bool) A x : (if b return A then x else x) = x.
Proof. destruct b; reflexivity. Defined.
