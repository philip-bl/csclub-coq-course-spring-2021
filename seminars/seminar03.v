From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Axiom replace_with_your_solution_here : forall {A : Type}, A.
Axiom cheat : forall {A : Type}, A.

(** * Exercise: show that [ex] is a more general case of [and].
    This is because terms of type [ex] are dependent pairs, while terms of type [and]
    are non-dependent pairs, i.e. the type of the second component in independent of the
    value of the first one. *)

Definition and_via_ex (A B : Prop) :
  (@ex A (fun _ : A => B)) <-> A /\ B
  := conj
       (fun ex_a_B : @ex A (fun _ : A => B) =>
          match ex_a_B with | @ex_intro _ _ a b => conj a b end : and A B)
       (fun a_and_b : and A B =>
          match a_and_b with
          | conj a b =>
            (@ex_intro A (fun _ : A => B) a b) : @ex A (fun _ : A => B)
          end).


(** * Exercise *)
Definition pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2)
  := fun eq_pairs =>
       match eq_pairs in _ = r return (a1 = r.1) /\ (b1 = r.2) with
       | erefl => conj erefl erefl
       end.


(** * Exercise (optional) *)
Definition J :
  forall (A : Type) (P : forall (x y : A), x = y -> Prop),
    (forall x : A, P x x erefl) ->
    forall x y (x_eq_y : x = y), P x y x_eq_y
  := fun A P forall_x_Pxxerefl x y x_eq_y =>
       match x_eq_y with
       | erefl => forall_x_Pxxerefl x
       end.
       

(** * Exercise *)
Definition succ_eq_zero_implies_False :
  forall n, n.+1 = 0 -> False
  := fun n succ_n_eq_zero =>
       match succ_n_eq_zero with
       | erefl => I
       end.


(** * Exercise *)
(*Definition foo (m : nat) : m + S 0 = *)

Print Nat.add.
Definition zero_addn (n : nat) : 0 + n = n
  := erefl.
Definition Saddn (n m : nat) : S n + m = S (n + m) := erefl.

Definition addnS :
    forall m n, m + S n = S (m + n)
  := nat_ind
       (fun m => forall n, m + S n = S (m + n))
       (nat_ind
          (fun n => 0 + S n = S (0 + n))
          (erefl : 0 + S 0 = S (0 + 0))
          (fun n (pn : 0 + S n = S (0 + n)) => erefl : 0 + S (S n) = S (0 + S n))
        : forall n, 0 + S n = S (0 + n))
       (fun (m : nat) (pm : forall n, m + S n = S (m + n)) =>
          (nat_ind
             (fun n => S m + S n = S (S m + n))
             ((let a := esym (addn0 (S m)) : S m = S m + 0 in
               let b:= congr1 S a : S (S m) = S (S m + 0) in
               let c := addn1 (S m) : S m + S 0 = S (S m) in
               (etrans c b) : S m + S 0 = S (S m + 0)))
             ((fun n (qn : S m + S n = S (S m + n)) =>
                 let a := congr1 S qn           : S (S m + S n) = S (S (S m + n)) in
                 let b := esym a                : S (S (S m + n)) = S (S m + S n) in
                 let d := Saddn m (S (S n))     : S m + S (S n) = S (m + S (S n)) in
                 let g := (pm (S n))                 : m + S (S n) = S (m + S n) in
                 let h := pm n                  : m + S n = S (m + n) in
                 let i := etrans g (congr1 S h) : m + S (S n) = S (S (m + n)) in
                 let j := Saddn m n             : S (m + n) = S m + n in
                 let f := etrans i (congr1 S j)               : m + S (S n) = S (S m + n) in 
                 let e := congr1 S f            : S (m + S (S n)) = S (S (S m + n)) in
                 let c := etrans d e            : S m + S (S n) = S (S (S m + n)) in
                 etrans c b
                 : S m + S (S n) = S (S m + S n))))
          : forall n, S m + S n = S (S m + n)).
(* PHI: fuck my life *)



(** * Exercise *)
Definition addA : associative addn
  := nat_ind
       _
       (fun n k => erefl : 0 + (n + k) = (0 + n) + k)
       (fun m (pm : forall n k, m + (n + k) = (m + n) + k) n k =>
          let a := Saddn m (n + k) : S m + (n + k) = S (m + (n + k)) in
          let f := esym (Saddn m n) : S (m + n) = S m + n in
          let b := congr1
                     (fun x => x + k)
                     f
                   : S (m + n) + k = (S m + n) + k in
          let g := Saddn (m + n) k : S (m + n) + k = S ((m + n) + k) in
          let h := congr1 (fun x => x + k) (esym f) : (S m + n) + k = S (m + n) + k in
          let e := etrans h g : (S m + n) + k = S ((m + n) + k) in
          let d := etrans b e : S (m + n) + k = S ((m + n) + k) in
          let c := congr1 S (pm n k) : S (m + (n + k)) = S (m + n) + k in
          etrans a (etrans c b) : S m + (n + k) = (S m + n) + k)
     : forall m n k, m + (n + k) = (m + n) + k .
(* PHI: once again, fuck my life *)

(* PHI: the following solution is by Anton Chaynikov *)
Definition addA' : associative addn
:= fix addA' {m n k : nat} {struct m} :=
match m with
| O => erefl
| S m' => congr1 S (addA' : m' + (n + k) = (m' + n) + k) : S m' + (n + k) = (S m' + n) + k
end.

(* PHI: how does his solution work? The trick is in the fact that the following thing checks *)
Check fun m n k => erefl : S (m + (n + k)) = S m + (n + k).
Check fun m n k => erefl : S ((m + n) + k) = (S m + n) + k.

(* In the following solution, I use Anton's trick to shorten my proof *)
Definition addA'' : associative addn
  := nat_ind
       _
       (fun n k => erefl : 0 + (n + k) = (0 + n) + k)
       (fun m (pm : forall n k, m + (n + k) = (m + n) + k) n k =>
          congr1 S (pm n k) : S m + (n + k) = (S m + n) + k)
     : forall m n k, m + (n + k) = (m + n) + k .

(** * Exercise: *)
Definition addnCA : left_commutative addn
  := fix addnCA (m n k : nat) {struct m} :=
       (match m with
        | S m' => let a := addnCA m' n k : m' + (n + k) = n + (m' + k) in
                  let b := congr1 S a : S m' + (n + k) = S (n + (m' + k)) in
                  let c := addnS n (m' + k) : n + (S m' + k) = S (n + (m' + k)) in
                  etrans b (esym c) : S m' + (n + k) = n + (S m' + k)
        | 0 => erefl : 0 + (n + k) = n + (0 + k)
       end) : m + (n + k) = n + (m + k).


(** * Exercise (optional): *)
Definition addn_zero : forall m, m + 0 = 0 + m
  := nat_ind
       _
       (erefl : 0 + 0 = 0 + 0)
       (fun m (pm : m + 0 = 0 + m) =>
          let a := addnS 0 m : 0 + S m = S m in
          let b := congr1 S pm : S m + 0 = S m in
          etrans b (esym a) : S m + 0 = 0 + S m).

Definition addnC : commutative addn
  := fun m =>
       nat_ind
         _
         (addn_zero m : m + 0 = 0 + m)
         (fun n (pn : m + n = n + m) =>
            let a := congr1 S pn : S (m + n) = S n + m in
            let b := addnS m n : m + S n = S (m + n) in
            etrans b a : m + S n = S n + m).


(** * Exercise (optional):
Formalize and prove
 - bool ≡ unit + unit,
 - A + B ≡ {b : bool & if b then A else B},
 - A * B ≡ forall b : bool, if b then A else B,
where ≡ means "is isomorphic to".
 *)

Print injective.

Definition surjective {A B : Type} (f : A -> B) : Prop
  := forall b, exists a, f a = b.

Definition bijective {A B : Type} (f : A -> B) : Prop
  := injective f /\ surjective f.

Definition inverse {A B : Type} (f : A -> B) (g : B -> A) : Prop
  := eqfun (g \o f) id.

Definition exfalso_quodlibet {A : Prop} :
  False -> A
  := fun pF : False => match pF with end. (* no branches *)

Axiom LEM : forall (P : Prop), P \/ ~P.

Definition dne (P : Prop) : ~ ~ P -> P
  := fun not_not_p =>
       match LEM P with
       | or_introl p => p
       | or_intror not_p => exfalso_quodlibet (not_not_p not_p)
       end.

Definition inverse_impl_injective {A B : Type} {f : A -> B} {g : B -> A}
  : inverse f g -> injective f
  := fun inv_f_g =>
       match @LEM (injective f) with
       | or_introl inj_f => inj_f
       | or_intror not_inj_f =>
         let foo := cheat : exists a1, exists a2, a1 <> a2 /\ f a1 = f a2 in
         cheat
       end. (* I'll finish this shit sometime later *)


Definition inverse_impl_surjective {A B : Type} {f : A -> B} {g : B -> A}
  : inverse f g -> surjective g
  := cheat.

(* PHI: Cantor-Bernstein would also be nice, but it seems really difficult
   or maybe even impossible to prove in Coq without advanced stuff. *)

Definition isomorphism {A B : Type} (f : A -> B) (g : B -> A) : Prop
  := inverse f g /\ inverse g f.

Definition isomorphism_implies_both_bijective {A B : Type} (f : A -> B) (g : B -> A)
  : isomorphism f g -> bijective f /\ bijective g
  := fun iso_f_g =>
       match iso_f_g with
       | conj inv_f_g inv_g_f =>
         conj
           (conj (inverse_impl_injective inv_f_g) (inverse_impl_surjective inv_g_f))
           (conj (inverse_impl_injective inv_g_f) (inverse_impl_surjective inv_f_g))
       end.

(* bool ≡ unit + unit *)

Definition b_to_u_plus_u : bool -> unit + unit
  := fun b => if b is true then inr tt else inl tt.

Definition u_plus_u_to_b : unit + unit -> bool
  := fun x => if x is inr _ then true else false.

Definition b_iso_u_plus_u : isomorphism b_to_u_plus_u u_plus_u_to_b
  := conj
       (fun b =>
          (if b is true then
             erefl
           else
             erefl)
          : u_plus_u_to_b (b_to_u_plus_u b) = b)
       (fun u_or_u =>
          (match u_or_u with
           | inl tt => erefl
           | inr tt => erefl
           end) : b_to_u_plus_u (u_plus_u_to_b u_or_u) = u_or_u).

(** * Exercise (optional): *)

Definition false_eq_true_implies_False :
  false = true -> False
:=
  fun     eq :  false = true =>
    match eq in (_    = b)
             return (if b then False else True)
    with
    | erefl => I
    end.

Definition unit_neq_bool:
  unit <> bool
  := fun unit_eq_bool : unit = bool =>
       let true_eq_false :=
           (match unit_eq_bool
                  in _ = b
                  return (forall (x : b), forall (y : b), x = y) with
            | erefl =>
              fun x y =>
                match x with | tt =>
                               match y with | tt => erefl
                               end
                end
            end)
             false true : false = true in
       false_eq_true_implies_False true_eq_false.


(* PHI: A * B ≡ forall b : bool, if b then A else B *)

Definition mul_to_func_on_bool {A B : Type} : A * B -> forall b : bool, if b then A else B
  := fun (pair : A * B) (b : bool) =>
       match b with
       | true => pair.1
       | false => pair.2
       end.

Definition func_on_bool_to_mul {A B : Type} : (forall b : bool, if b then A else B) -> A * B
  := fun func => (func true, func false).

Definition inv1 {A B : Type} : inverse mul_to_func_on_bool func_on_bool_to_mul
  := (fun (pair : A * B) => match pair with | (a, b) => erefl end : (pair.1, pair.2) = pair).

(* PHI: Trun' allows us to use the following axiom for this isomorphism *)
Axiom f_ext_dep : forall {D} {C : D -> Type},
    forall (g h : forall x : D, C x),
      (forall x, g x = h x) -> g = h.

(* PHI: I'll use the following lemma together with f_ext_dep *)
Definition inv2_ext {A B : Type} (f : forall b : bool, if b then A else B) :
  forall b : bool, (mul_to_func_on_bool (func_on_bool_to_mul f)) b = f b
  := fun b => match b with
              | true => erefl
              | false => erefl
              end.

(* PHI: to finally prove the isomorphism *)

Definition inv2 {A B : Type} : inverse func_on_bool_to_mul mul_to_func_on_bool
  := (fun (f : forall b : bool, if b then A else B) =>
        (@f_ext_dep
           bool
           ((fun b : bool => if b then A else B) : bool -> Type)
           (mul_to_func_on_bool (func_on_bool_to_mul f) : forall b : bool, if b then A else B)
           (f : forall b : bool, if b then A else B)
           (inv2_ext f : forall b, (mul_to_func_on_bool (func_on_bool_to_mul f)) b = f b))
        : mul_to_func_on_bool (func_on_bool_to_mul f) = f).

Definition mul_iso_func_on_bool {A B : Type}
  : @isomorphism
      (A * B)
      (forall b : bool, if b then A else B)
      mul_to_func_on_bool
      func_on_bool_to_mul
  := conj inv1 inv2.


(* PHI: final exercise - A + B ≡ {b : bool & if b then A else B} *)

Variable A C : Type.
Check erefl : {b : bool & if b then A else C} = @sigT bool (fun b : bool => if b then A else C).

Definition sum_to_sigT_bool {A C : Type} (a_or_c : A + C)
  : @sigT bool (fun b : bool => if b then A else C)
  := match a_or_c with
     | inl a => @existT bool (fun b : bool => if b then A else C) true a
     | inr c => existT _ false c
     end.

(*
Variable b : bool.
Variable y : if b then A else C.
Fail Check (match b with
      | true => inl y
      | false => inr y
      end) : A + C.

Goal A + C.
  remember y as y.
  clear Heqy.
  destruct b.
  - exact (inl y).
  - exact (inr y).
Show Proof.

Check ((match b as b' return ((if b' then A else C) -> A + C) with
        | true => inl
        | false => inr
        end) y)
      : A + C.
*)

Definition sigT_bool_to_sum {A C : Type} (s : @sigT bool (fun b : bool => if b then A else C))
  : A + C
  := match s with
     | existT b y =>
       (match b as b' return (if b' then A else C) -> A + C with
        | true => inl
        | false => inr
        end) y : A + C
     end.

Definition sigT_bool_to_sum' {A C : Type} (s : @sigT bool (fun b : bool => if b then A else C))
  : A + C
  := match s with
     | existT b y =>
       match b, y with
       | true, a => inl a
       | false, b => inr b
       end
     end.

Definition sum_iso_sigT_bool {A C : Type}
  : @isomorphism
      (A + C)
      (@sigT bool (fun b : bool => if b then A else C))
      sum_to_sigT_bool
      sigT_bool_to_sum.

refine (conj
       (fun a_or_c : A + C =>
          match a_or_c with
          | inl a => _
          | inr b => _
          end)
       (fun s : @sigT bool _ =>
          match s with
          | existT b y => _
          end)).

- exact erefl.
- exact erefl.

destruct b.
- exact erefl.
- exact erefl.
Qed.

(* PHI: ya ebal razbiratsya kak perepisat' sum_iso_sigT_bool bez tactic *)
