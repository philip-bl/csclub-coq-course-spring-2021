From mathcomp Require Import ssreflect.
Module My.
  Inductive bool : Type :=
  | true
  | false.

  Check false : bool.
  Check false.
  Check (bool -> bool) : Type.
  Check Type : Type.
  Check (fun b : bool => b).
  Check fun b => b.
  Check (fun b => b) true.
  Compute true.
  Compute (fun b => b) true.
  Compute Type.
  Compute Set.
  Check Type.
  Check Set.
  Definition idb := fun b : bool => b.
  Check idb.
  Check (fun (f : bool -> bool) => f false) idb.
  Compute (fun (f : bool -> bool) => f false) idb.
  Fail Check (fun (f : bool -> bool) => f true) false.
  Fail Fail Check true.
  Fail Definition a := b.
  Definition negb :=
    fun (b : bool) =>
      match b with
      | true => false
      | false => true
      end.
  Compute negb false.  
  Check negb.
  Check negb true.
  Check bool -> bool.
  Eval cbv delta in negb true.
  Eval cbv beta delta in negb true.
  Eval cbv beta delta iota in negb true. (* the order of beta delta iota doesn't matter *)
  Eval cbv iota in negb true.
  Variable c : bool.
  Compute idb c.
  Compute negb c.
  Compute negb (negb c).

  Inductive nat : Type :=
  | O
  | S of nat. (* this is syntax sugar from ssreflect *)
  Print nat.
  Check O.
  Check S.
  Check S O.
  Check S (S O).
  Check (fun b => S (S b)).
  Compute S (S O).
  Inductive nat' : Type :=
  | O' : nat'
  | S' : nat' -> nat'.
  Check Prop.
  Definition succn := S.
  Eval cbv beta delta iota in succn.
  Compute S (succn (S (succn O))).
  Definition predn (n : nat) : nat :=
    match n with
    | S x => x
    | O => O
    end.
  Fixpoint addn (n m : nat) {struct n} : nat :=
    match n with
    | O => m
    | S n' => S (addn n' m)
    end.
  Compute addn (S (S O)) (S (S (S (S O)))).  
  Fixpoint addn_idiomatic (n m : nat) : nat := (* this also uses ssreflect *)
    if n is S n' then S (addn_idiomatic n' m) else m.
  Print addn_idiomatic.
  
