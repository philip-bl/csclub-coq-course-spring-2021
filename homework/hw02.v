From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.


(** * Arithmetic expression language *)


(** NOTE: If you don't need this homework graded for you university,
          please, do _not_ submit it through the CS club website. *)

(** NOTE: In a later homework we are going to prove some properties of the
functions this homework asks you to implement. Please keep your code so you can
reuse it later. *)


(** Define is a simple language of arithmetic expressions consisting of
constants (natural numbers) and arbitrarily nested additions, subtractions and
multiplications *)
Inductive expr : Type :=
| Const of nat
| Plus of expr & expr
| Minus of expr & expr
| Mult of expr & expr.

(** Let us define a special notation for our language.
    We reuse the standard arithmetic notations here, but only inside
    double square brackets (see examples below) *)

(* This means we declare `expr` as an identifier referring to a 'notation
entry' *)
Declare Custom Entry expr.
(* And we let the parser know `expr` is associated with double brackets, so
inside double brackets the parser will use notations associated with custom
`expr` entries *)
Notation "'[[' e ']]'" := e (e custom expr at level 0).

(* Numerals can be used without wrapping those in the `Const` constructor *)
Notation "x" :=
  (Const x)
    (in custom expr at level 0, x bigint).

Notation "( x )" := x (in custom expr, x at level 2).
Notation "x + y" := (Plus x y) (in custom expr at level 2, left associativity).

(* Define notations for subtraction and multiplication.
   Hint: lower level means higher priority.
   Your notations should start with `in custom expr` as above. *)
Notation "x - y" := (Minus x y) (in custom expr at level 2, left associativity).
Notation "x * y" := (Mult x y) (in custom expr at level 1, left associativity).

(** Here is how we write Plus (Const 0) (Plus (Const 1) (Const 2)) *)
Check [[
          0 + (1 + 2)
      ]].
(** And this is Plus (Plus (Const 0) (Const 1)) (Const 2) *)
Check [[
          (0 + 1) + 2
      ]].

(* Make sure the following are parsed as expected.
   What query can you use to do that? *)
Unset Printing Notations.
Check [[
          ((0 + 1) + 2) + 3
      ]].
Check [[
          0 + (1 + (2 + 3))
      ]].
Check [[
          0 * 1 + 2
      ]].
Check [[
          0 + 1 * 2
      ]].
Check [[
          0 + 1 - 2 + 3
      ]].
Check [[ 0 - 1 - 2 - 3 ]].
Set Printing Notations.

(** Write an evaluator for the expression language which fixes its semantics.
Basically, the semantics of the expression language should be the same as
the corresponding Coq functions `addn`, `subn`, `muln`. *)
Fixpoint eval (e : expr) : nat :=
  match e with
  | Const x => x
  | Plus x y => addn (eval x) (eval y)
  | Minus x y => subn (eval x) (eval y)
  | Mult x y => muln (eval x) (eval y)
  end.

(** Some unit tests *)
(** We haven't discussed in depth what `erefl` means yet.
    But for now, let's just assume if the following lines
    typecheck then the equalities below hold *)
Check erefl : eval [[ 0 - 4 ]] = 0.
Check erefl : eval [[ 0 + (2 - 1) ]] = 1.
Check erefl : eval [[ (0 + 1) + 2 ]] = 3.
Check erefl : eval [[ 2 + 2 * 2 ]] = 6.
Check erefl : eval [[ (2 + 2) * 2 ]] = 8.
Check erefl : eval [[ (2 - 2) * 98 ]] = 0.
Check erefl : eval [[ (5 - 3) * (6 - 2) ]] = 8.

(** * Compiling arithmetic expressions to a stack language *)

(** Here is a "low-level" stack language which can serve as the target language
for a compiler from the arithmetic expression language above.
See, for instance, this page for more detail:
https://en.wikipedia.org/wiki/Stack-oriented_programming.

A program in this language is a list of instructions, each of which manipulates
a stack of natural numbers. There are instructions for pushing constants onto
the stack and for adding/subtracting/muliplying the top two elements of the
stack, popping them off the stack, and pushing the result onto the stack. *)

Inductive instr := Push (n : nat) | Add | Sub | Mul.

(*
Feel free to define your own notations for the stack operations
to make it easier writing unit tests
For example, this is one possible way to start:

Notation " << n >> " := (Push n) (at level 0, n constr).
 *)

(* Feel free to either define your own datatype to represent lists or reuse the
`seq` datatype provided by Mathcomp (this is why this file imports the `seq`
module at the beginning). Btw, `seq` is just a notation for the standard `list`
datatype.

    Inductive list (A : Type) : Type :=
      | nil
k      | cons of A & list A.

You can construct new lists (sequences) like so:
  - [::]           --  notation for the `nil` constructor;
  - x :: xs        --  notation for the `cons` constructor;
  - [:: 1; 2; 3]   --  notation for a sequence of three elements 1, 2 and 3.

Using `seq`, we can define the type of programs as follows:
 *)
Compute 1 :: [:: 2; 3; 4].
Definition prog := seq instr.

(* And the type of stacks like so: *)
Definition stack := seq nat.

(** The [run] function is an interpreter for the stack language. It takes a
 program (list of instructions) and the current stack, and processes the program
 instruction-by-instruction, returning the final stack. *)
Fixpoint run (p : prog) (s : stack) : stack :=
  if p is p_head :: p_tail then
    if p_head is Push n then
      run p_tail (n :: s)
    else
      if s is n :: m :: s_tail then
        let r := match p_head with
                 | Add => m + n
                 | Sub => m - n
                 | Mul => m * n
                 | Push _ => 1597
                 end
        in run p_tail (r :: s_tail)
      else
        [:: 987]
  else
    s.

(** Unit tests: *)

Check erefl : run [:: Add ] [:: 2; 3] = [:: 5].
Check erefl : run [:: Mul ] [:: 2; 3] = [:: 6].
Check erefl : run [:: Sub ] [:: 1; 2] = [:: 1].

Check erefl : run [:: (Push 10); (Push 5); Sub ] [::] = [:: 5].
Check erefl : run [:: (Push 10); (Push 5); (Push 3); Mul; Add] [::] = [:: 25].
Check erefl : run [:: (Push 10); (Push 5); (Push 3); Mul; Add; (Push 3); Sub] [::] = [:: 22].
(** Now, implement a compiler from "high-level" expressions to "low-level" stack
programs and do some unit tests. *)

(* phi: now I make my custom notation for prog *)
Declare Custom Entry foobar.
Notation "'<{' xs '}>'" := (xs : prog) (xs custom foobar at level 0).
Notation "" := ([::] : prog) (in custom foobar at level 0).
Notation "x xs" := (Push x :: xs) (in custom foobar at level 0, x bigint).
Notation "+ xs" := (Add :: xs) (in custom foobar at level 0).
Notation "* xs" := (Mul :: xs) (in custom foobar at level 0).
Notation "- xs" := (Sub :: xs) (in custom foobar at level 0).
(* phi: now I rewrite those unit tests using this notation *)
Check erefl : run <{ + }> [:: 2; 3] = [:: 5].
(* TODO STOPPED HERE *)
Check erefl : run <{ * }> [:: 2; 3] = [:: 6].
Check erefl : run <{ - }> [:: 1; 2] = [:: 1].

Fixpoint compile (e : expr) : prog :=
  match e with
  | Const n => [:: (Push n)]
  | Plus  l r => cat (compile l) (cat (compile r) [:: Add])
  | Minus l r => cat (compile l) (cat (compile r) [:: Sub])
  | Mult  l r => cat (compile l) (cat (compile r) [:: Mul])
  end.

(** Do some unit tests *)
Check erefl : compile [[ 5 ]] = <{ 5 }>.
Check erefl : compile [[ 5 + 3 ]] = <{ 5 3 + }>.
Check erefl : compile [[ (6) ]] = <{ 6 }>.
Check erefl : compile [[ (6 + 4) * (7 - 3) - 8]] = <{ 6 4 + 7 3 - * 8 - }>.
(* Some ideas for unit tests:
  - check that `run (compile e) [::] = [:: eval e]`, where `e` is an arbitrary expression;
  - check that `compile` is an injective function
 *)
Compute eval [[ 5 - 7 + 6 * 4 * 3 * 2 ]].
Compute run (compile [[ 5 - 7 + 6 * 4 * 3 * 2]]) [::].

Check erefl : run (compile [[ 5 - 7 + 6 * 4 * 3 * 2 ]]) [::] = [:: eval [[ 5 - 7 + 6 * 4 * 3 * 2 ]] ].

(** Optional exercise: decompiler *)

(** Implement a decompiler turning a stack program into the corresponding
expression *)
(* Hint: you might want to introduce a recursive helper function `decompile'` to
 reuse it for `decompile`. *)

Print option.

Fixpoint decompile_helper (p : prog) (acc : seq expr) : option (seq expr) :=
  match p with
  | [::] => Some acc
  | Push n :: p_tail => decompile_helper p_tail (Const n :: acc)
  | Add :: p_tail => if acc is r :: l :: acc_tail then
                       decompile_helper p_tail (Plus l r :: acc_tail)
                     else
                       None
  | Sub :: p_tail => if acc is r :: l :: acc_tail then
                       decompile_helper p_tail (Minus l r :: acc_tail)
                     else
                       None
  | Mul :: p_tail => if acc is r :: l :: acc_tail then
                       decompile_helper p_tail (Mult l r :: acc_tail)
                     else
                       None
  end.

Definition decompile (p : prog) : option expr :=
  if decompile_helper p [::] is Some [:: e] then Some e else None.

(** Unit tests *)
Check erefl : Some [[ 5 ]] = decompile <{ 5 }>.
Check erefl : Some [[ 5 + 3 ]] = decompile <{ 5 3 + }>.
Check erefl : Some [[ (6) ]] = decompile <{ 6 }>.
Check erefl : Some [[ (6 + 4) * (7 - 3) - 8]] = decompile <{ 6 4 + 7 3 - * 8 - }>.
