From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* An (unsound) placeholder so that the whole file typechecks.
Please replace it with your proof term. Your solutions may not
use any axioms, including `replace_with_your_solution_here` *)
Axiom replace_with_your_solution_here : forall {A : Type}, A.
Axiom solved_by_phi_in_seminar03 : forall {A : Type}, A. (* PHI: see seminar03.v *)
Axiom cheat : forall {A : Type}, A.

(* WARNING!
 Since we import `eqtype` module which redefines `eq_refl` to mean something else
 other than the equality type constructor, beware of using `eq_refl` in
 pattern-matching.
 For instance, in a `match`-expression like this one
    match foo in ... return ... with
    | eq_refl => ...
    end
 eq_refl is a new identifier which just shadows the `eq_refl` lemma,
 hence no index rewriting is happening. If you see weird type errors,
 just make sure you spelled the equality type constructor correctly
 in this context:
    match foo in ... return ... with
    | erefl => ...
    end
*)


(** * Exercise: show that [ex] is a more general case of [and].
    This is because terms of type [ex] are dependent pairs, while terms of type [and]
    are non-dependent pairs, i.e. the type of the second component in independent of the
    value of the first one. *)

Definition and_via_ex (A B : Prop) :
  (exists (_ : A), B) <-> A /\ B
:= solved_by_phi_in_seminar03.


(** * Exercise *)
Section Symmetric_Transitive_Relation.

Variables (D : Type)
          (R : D -> D -> Prop).

(* R's type D -> D -> Prop means R is a binary relation *)

(* The lemma refl_if read informally, means
"if R is a symmetric and transitive relation
then each element x which is related to some
element y is also related to itself" *)
Definition refl_if :
  (forall x y, R x y -> R y x) ->
  (forall x y z, R x y -> R y z -> R x z) ->
  forall x : D, (exists y, R x y) -> R x x
  := fun Rsym Rtrans x ex =>
       match ex with
       | ex_intro y Rxy =>
         Rtrans x y x Rxy (Rsym x y Rxy)
       end.


End Symmetric_Transitive_Relation.


(** * Exercise *)
Definition pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2)
:= solved_by_phi_in_seminar03.


(** * Exercise *)
Inductive trilean : Type :=
  | Yes
  | No
  | Maybe.

Definition yes_no_disj :
  Yes <> No
  := fun Yes_eq_No => match Yes_eq_No with | erefl => I end.


(** * Exercise *)
(*
0 + (y + z) = 0 + y + z
y + z = 0 + y + z
y + z = y + z


x'.+1 + (y + z) = x'.+1 + y + z
(x' + (y + z)).+1 = (x'.+1 + y) + z
(x' + (y + z)).+1 = (x' + y).+1 + z
(x' + (y + z)).+1 = ((x' + y) + z).+1

S (x' + (y + z)) = S ((x' + y) + z)

(x' + (y + z))   =   ((x' + y) + z)
*)
Definition addA : associative addn
:= solved_by_phi_in_seminar03.

Check congr1.
Definition addA : associative addn
 (* forall x y z : nat, x + (y + z) = x + y + z *)
:= fix IHx x y z :=
     match x as x
       return (x + (y + z) = x + y + z)
     with
     | 0 => erefl (y + z)
     | x'.+1 =>
       let IHx' : x' + (y + z) = x' + y + z :=
           IHx x' y z
       in congr1 S IHx'
     end.
Definition addA' : associative addn
:= fix IHx {x y z} :=
     if x is x'.+1 then congr1 S IHx else erefl.

Print associative.
Eval hnf in associative addn.
Print addn.
Check tt.
Print nosimpl.
Print addn_rec.
Print Nat.add.

(** * Exercise: *)
Definition addnCA : left_commutative addn
:= solved_by_phi_in_seminar03.

(* Hint: re-use addnS lemma and some general lemmas about equality *)






(** * ====== Optional exercises (feel free to skip) ====== *)

(** * Exercise (optional) *)
Definition J :
  forall (A : Type) (P : forall (x y : A), x = y -> Prop),
    (forall x : A, P x x erefl) ->
    forall x y (p : x = y), P x y p
:= solved_by_phi_in_seminar03.


(** * Exercise (optional): *)
Definition addnC : commutative addn
:= solved_by_phi_in_seminar03.


(** * Exercise (optional):
Formalize and prove
 - bool ≡ unit + unit,
 - A + B ≡ {b : bool & if b then A else B},
 - A * B ≡ forall b : bool, if b then A else B,
where ≡ means "is isomorphic to".
 *) (* PHI: solved by me in seminar03 *)

(** * Exercise (optional): *)
Definition unit_neq_bool:
  unit <> bool
:= solved_by_phi_in_seminar03.
