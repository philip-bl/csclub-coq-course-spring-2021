From mathcomp Require Import ssreflect.

(*| We continue working with our own definitions of Booleans and natural numbers |*)

Module My.

Inductive bool : Type :=
| true
| false.

Definition negb :=
  fun (b : bool) =>
    match b with
    | true => false
    | false => true
    end.

(** * Exercise 1 : boolean functions *)

(*| 1a. Define `orb` function implementing boolean disjunction and test it
_thoroughly_ using the command `Compute`. |*)

Definition orb b c := match b with
  | true => true
  | false => c
end.
Compute orb true true.
Compute orb true false.
Compute orb false true.
Compute orb false false.
Variable x : bool.
Compute orb true x.
Compute orb x true.
Compute orb false x.
Compute orb x false.


(*| 1b. Define `addb` function implementing _exclusive_ boolean disjunction.
Try to come up with more than one definition (try to make it interesting
and don't just swap the variables) and explore its reduction behavior
in the presence of symbolic variables. |*)

Definition andb b c := negb (orb (negb b) (negb c)).
Definition addb b c := orb (andb b (negb c)) (andb c (negb b)).
Compute addb true true.
Compute addb true false.
Compute addb false true.
Compute addb false false.
Compute addb true x. (* Eval cbv beta delta iota in addb true x outputs the same thing *)
Compute addb x true.
Compute addb false x.
Compute addb x false.

Definition addb' b c := andb (orb (negb b) (negb c)) (orb b c).
Compute addb' true true.
Compute addb' true false.
Compute addb' false true.
Compute addb' false false.
Compute addb' true x.
Compute addb' x true.
Compute addb' false x.
Compute addb' x false.

Definition addb'' b c := match b with
  | false => c
  | true => negb c
                         end.
Compute addb' true true.
Compute addb' true false.
Compute addb' false true.
Compute addb' false false.
Compute addb' true x.
Compute addb' x true.
Compute addb' false x.
Compute addb' x false.

(*| 1c. Define `eqb` function implementing equality on booleans, i.e. `eqb b c`
must return `true` if and only iff `b` is equal to `c`. Add unit tests. |*)

Definition eqb b c := addb true (addb b c).

Compute eqb false false.
Compute eqb false true.
Compute eqb true false.
Compute eqb true true.

(** * Exercise 2 : arithmetic *)

Inductive nat : Type :=
| O
| S of nat.

Check nat.
Check nat_ind. (* nat_ind says induction holds on nat, I think *)
Check nat_rect.
(* nat_rect is exactly the same as nat_ind, but for Type instead of Prop. Idk what that means *)
Check nat_rec.
Check nat_sind.

(*| 2a. Define `dec2` function of type `nat -> nat` which takes a natural
number and decrements it by 2, e.g. for the number `5` it must return `3`. Write
some unit tests for `dec2`. What should it return for `1` and `0`? |*)

Definition dec2 (n : nat) : nat :=
  match n with
  | S (S m) => m
  | _ => O
           end.
                 

Compute dec2 O.
Compute dec2 (S O).
Compute dec2 (S (S O)).
Compute dec2 (S (S (S O))).

(*| 2b. Define `subn` function of type `nat -> nat -> nat` which takes two
natural numbers `m` and `n` and returns the result of subtracting `n` from `m`.
E.g. `subn 5 3` returns `2`. Write some unit tests. |*)

(* Fixpoint subn m n := *)
(*   match m with *)
(*   | O => O *)
(*   | S m' => match n with *)
(*             | O => S m' *)
(*             | S n' => subn m' n' *)
(*             end *)
(*   end. *)

Fixpoint subn m n := if m is S m' then (if n is S n' then subn m' n' else S m') else m.
Fixpoint subn' m n := if n is S n' then (if m is S m' then subn' m' n' else m) else m.



Variable m : nat.
Variable n : nat.
Compute subn O n.
Compute subn (S m) O.
Compute subn (S O) (S O).
Compute subn (S (S O)) (S O).

(*| 2c. Define an `muln` function of type `nat -> nat -> nat` which takes two
natural numbers `m` and `n` and returns the result of their multiplication.
Write some unit tests. |*)

Fixpoint addn (n m : nat) : nat := if n is S n' then S (addn n' m) else m.

Fixpoint muln (m n : nat) : nat :=
  if n is S n' then
    addn (muln m n') m
  else
    n.

Compute muln m O.
Compute muln O (S (S O)).
Compute muln (S O) (S O).
Compute muln (S (S O)) (S (S (S O))).

(** 2d. Implement equality comparison function `eqn` on natural numbers of
type `nat -> nat -> bool`. It returns true if and only if the input numbers are
equal. *)

Definition eqn :=
  fix eqn m n {struct m} :=
    match m with
    | O => if n is O then true else false
    | S m' => if n is S n' then eqn m' n' else false
    end.

Compute eqn O O.
Compute eqn (S O) (S O).
Compute eqn (S (S (S O) ) ) (S (S (S O))).
Compute eqn O (S O).
Compute eqn (S O) O.
Compute eqn (S (S O)) (S O).
Compute eqn (S O) (S (S O)).

(** 2e. Implement less-or-equal comparison function `leq` on natural numbers of
type `nat -> nat -> bool`. `leq m n` returns `true` if and only if `m` is less
than or equal to `n`. Your solution must not use recursion but you may reuse any
of the functions you defined in this module so far. *)

Definition leq m n := eqn (subn m n) O.
Compute leq O n.
Compute leq (S O) O.
Compute leq (S (S O)) (S (S O)).
Compute leq (S (S O)) (S (S (S O))).
Compute leq (S (S O)) (S O).

(*| ---------------------------------------------------------------------------- |*)

Print subn.

Fixpoint divn (m n : nat) {struct m} : nat :=
  if n is S n' then
    if subn' m n' is S m' then S (divn m' n) else O
  else
    O.

    
    
  

(*| EXTRA problems: feel free to skip these. If you need to get credit for this
class: extra exercises do not influence your grade negatively if you skip them.
|*)

Fixpoint hyperoperation_helper a n b :=
  match b with
    | O => S O
    | S b' =>
      match n with
      | O => muln a b
      | S n' => hyperoperation_helper a n' (hyperoperation_helper a n b')
      end
  end.

Definition hyperoperation a n b :=
  if n is S n' then
    hyperoperation_helper a n' b
  else
    addn a b.


(*| Ea: implement division (`divn`) on natural numbers and write some unit tests
for it. |*)

End My.
