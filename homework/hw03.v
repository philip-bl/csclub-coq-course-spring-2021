From mathcomp Require Import ssreflect ssrfun ssrbool.

(** Prove the following lemmas by providing explicit proof terms.
A bunch of exercises from the previous seminar we didn't have time
to cover have made it to this homework :) *)

(* An (unsound) placeholder so that the whole file typechecks.
Please replace it with your proof term. Your solutions may not
use any axioms, including `replace_with_your_solution_here` *)
Axiom replace_with_your_solution_here : forall {A : Type}, A.
Axiom cheat : forall {A : Type}, A.

Section Logic.

Variables A B C : Prop.

(** * Exercise *)
Definition notTrue_iff_False : (~ True) <-> False
  := conj
       (fun true_impl_false => true_impl_false I)
       (fun false : False => match false with end).

(* Hint 1: use [Locate "<->".] and [Print iff.] commands to understand better
the type above. *)

(* Hint 2: If you are experiencing an error like the following one
"Found a matching with no clauses on a term unknown to have an empty inductive type." try adding explicit type annotations to functional parameters or
use `match <term> in <type> with ... end` instead of `match <term> with ... end` *)

(** * Exercise: double negation elimination works for `False` *)
Definition dne_False : ~ ~ False -> False
  := fun false_to_false_impl_false : (False -> False) -> False =>
       false_to_false_impl_false (fun false => false).

(** * Exercise: double negation elimination works for `True` too. *)
Definition dne_True : ~ ~ True -> True
  := fun _ => I.

(** * Exercise: Weak Peirce's law
Peirce's law (https://en.wikipedia.org/wiki/Peirce%27s_law) is equivalent to
Double Negation Elimination (and the Law of Excluded Middle too),
so it does not hold in general, but we can prove its weak form. *)
(* Hint 1: use let-in expression to break the proof into pieces and solve them independently *)
(* Hint 2: annotate the identifiers of let-expressions with types: [let x : <type> := ... in ...] *)
Definition weak_Peirce : ((((A -> B) -> A) -> A) -> B) -> B
  := fun c : (((A -> B) -> A) -> A) -> B =>
       let d := fun e : (A -> B) -> A =>
                  let f := fun g : A =>
                             let i := fun _ => g
                             in c (i : ((A -> B) -> A) -> A)
                  in e (f : A -> B)
       in c (d : ((A -> B) -> A) -> A).

Variable T : Type.
Variable P Q : T -> Prop.

(** * Exercise: existential introduction rule *)
Definition exists_introduction :
  forall (x : T), (P x -> (exists (x : T), P x))
  := fun x : T =>
       fun px : P x =>
         ex_intro P x px.

(** * Exercise: Frobenius rule: existential quantifiers and conjunctions commute *)
Definition frobenius_rule :
  (exists x, A /\ P x) <-> A /\ (exists x, P x)
  := conj
       (fun ex_x_a_and_px : (exists x, A /\ P x) =>
          (match ex_x_a_and_px with
           | ex_intro x a_and_px =>
             conj a_and_px.1 (ex_intro P x a_and_px.2) : A /\ (exists x, P x)
           end))
       ((fun a_and_ex_x_px =>
           match a_and_ex_x_px with
           | conj a ex_x_px =>
             match ex_x_px with
             | ex_intro x px =>
               ex_intro (fun x' => A /\ (P x')) x (conj a px)
             end
           end)).

End Logic.



Section Equality.

Variables A B C D : Type.

(** * Exercise *)
Definition eq1 : true = (true && true)
:= eq_refl.

(** * Exercise *)
Definition eq2 : 42 = (if true then 21 + 21 else 239)
:= eq_refl.

(** * Exercise *)
Definition LEM_decidable :
  forall (b : bool), b || ~~ b = true
  := fun b => match b with
     | true => eq_refl
     | false => eq_refl
     end.

(** * Exercise *)
Definition if_neg :
  forall (A : Type) (b : bool) (vT vF: A),
    (if ~~ b then vT else vF) = if b then vF else vT
  := fun A b vT vF =>
       match b with
       | true => eq_refl
       | false => eq_refl
       end.

(** * Exercise : associativity of function composition *)
(** [\o] is a notation for function composition in MathComp, prove that it's associative *)
Definition compA (f : A -> B) (g : B -> C) (h : C -> D) :
  (h \o g) \o f = h \o (g \o f)
  := eq_refl.

(** [=1] stands for extensional equality on unary functions,
    i.e. [f =1 g] means [forall x, f x = g x].
    This means it's an equivalence relation, i.e. it's reflexive, symmetric and transitive.
    Let us prove a number of facts about [=1]. *)
Locate "=1".
Print eqfun.

(** * Exercise: Reflexivity *)
Definition eqext_refl :
  forall (f : A -> B), f =1 f
:= fun f x => eq_refl.

(** * Exercise: Symmetry *)
Definition eqext_sym :
  forall (f g : A -> B), f =1 g -> g =1 f
  := fun f g f_eqext_g x => eq_sym (f_eqext_g x).

(** * Exercise: Transitivity *)
Check eq_trans.
Definition eqext_trans :
  forall (f g h : A -> B), f =1 g -> g =1 h -> f =1 h
  := fun f g h f_eqext_g g_eqext_h x => eq_trans (f_eqext_g x) (g_eqext_h x).

(** * Exercise: left congruence *)
Definition eq_compl :
  forall (f g : A -> B) (h : B -> C),
    f =1 g -> h \o f =1 h \o g
  := fun f g h f_eqext_g x =>
       let fx_eq_gx := f_eqext_g x : f x = g x in
       (match fx_eq_gx in (_ = b) return h (f x) = h b
        with | eq_refl => eq_refl end) : h (f x) = h (g x).

(** * Exercise: right congruence *)
Definition eq_compr :
  forall (f g : B -> C) (h : A -> B),
    f =1 g -> f \o h =1 g \o h
  := fun f g h f_eqext_g x => f_eqext_g (h x).

End Equality.


(** * Extra exercises (feel free to skip) *)

From mathcomp Require Import eqtype.

(* After importing `eqtype` you need to either use a qualified name for
`eq_refl`: `Logic.eq_refl`, or use the `erefl` notation.
This is because `eqtype` reuses the `eq_refl` identifier for a
different lemma.
 *)

Definition iff_is_if_and_only_if :
  forall a b : bool, (a ==> b) && (b ==> a) = (a == b)
  := fun a b =>
       (match a with
       | false => erefl
       | true => match b with
                 | false => erefl
                 | true => erefl
                 end
       end) : (a ==> b) && (b ==> a) = (a == b).

(* It turns out ~~ in the next definition is not double application of not = fun A : Prop => A -> False : Prop *)
(* Instead ~~ is (single) negation of a bool *)
Locate "~~".

Definition negbNE :
  forall b : bool, ~~ ~~ b = true -> b = true
  := fun b (neg_neg_b_eq_true : ~~ ~~ b = true) =>
       match neg_neg_b_eq_true in _ = true return b = true with
       | eq_refl => cheat
       end.
