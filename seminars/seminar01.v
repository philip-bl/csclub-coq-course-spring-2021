From mathcomp Require Import ssreflect.

(* implement functions with the given signatures *)

Definition prodA (A B C : Type) : (A * B) * C -> A * (B * C) :=
  fun triple => match triple with
                | ((a, b), c) => (a, (b, c))
                end.

Definition sumA (A B C : Type) : (A + B) + C -> A + (B + C) :=
  fun x =>
    match x with
      | inr c => inr A (inr B c)
      | inl (inl a) => inl (B + C) a
      | inl (inr b) => inr A (inl C b)
    end.

Definition prod_sumD (A B C : Type) : A * (B + C) -> (A * B) + (A * C) :=
  fun pair =>
    match pair with
    | (a, inl b) => inl (A * C) (a, b)
    | (a, inr c) => inr (A * B) (a, c)
    end.

Check prod_sumD.

Definition prod_sumD' (A : Type) (B : Type) (C : Type) (pair : A * (B + C)) : (A * B) + (A * C) :=
    match pair with
    | (a, inl b) => inl (A * C) (a, b)
    | (a, inr c) => inr (A * B) (a, c)
    end.

(* Definition sum_prodD (A B C : Type) : *)
(*   A + (B * C) -> (A + B) * (A + C) *)
(* := *)


(* function composition *)
Definition comp A B C (f : B -> A) (g : C -> B) : C -> A := fun c => f (g c).
Arguments comp [A B C] _ _ _.
Check comp.

Notation "f ∘ g" :=
  (comp f g)
    (at level 20, right associativity)
  : type_scope.

From mathcomp Require Import ssrnat.

Check comp S S.
Check S ∘ S.
Compute S ∘ S ∘ S.
(* Introduce a notation that lets us use composition like so: f \o g.
   You might need to tweak the implicit status of some comp's arguments *)


(* Introduce empty type, call `void` *)
Inductive void : Type := .

Definition void_terminal (A : Type) (x : void) : A :=
  match x with
  end.

(* Introduce `unit` type (a type with exactly one canonical form) *)
Inductive unit : Type :=
| u.

Check u.

Definition unit_initial (A : Type) (_ : A) : unit :=
  u.
Arguments unit_initial [A] _.

Compute unit_initial (S O).

(* Think of some more type signatures involving void, unit, sum, prod *)

Definition times_unit (A : Type) (a : A) : A * unit := (a, u).
Arguments times_unit {A} _.

Definition un_times_unit (A : Type) (a' : A * unit) : A := fst a'.
Arguments un_times_unit {A} _.

Check un_times_unit.

Compute (un_times_unit (times_unit O)).  (* it works *)

Check (@comp nat (nat * unit) nat (@un_times_unit nat) (@times_unit nat)) O.

Check (comp un_times_unit times_unit) O.
