Section PropositionalLogic.

Variables A B C : Prop.

Definition anb1 :
  A /\ B -> A
  := fun a_and_b =>
       match a_and_b with
       | conj a b => a
       end.

Definition impl_trans :
  (A -> B) -> (B -> C) -> A -> C
  :=
    fun a_impl_b =>
      fun b_impl_c =>
        fun a =>
          b_impl_c (a_impl_b a).

Definition HilbertS (a_impl_b_impl_c : A -> B -> C) (a_impl_b : A -> B) (a : A) : C :=
  a_impl_b_impl_c a (a_impl_b a).

Definition DNE_triple_neg :
  ~ ~ ~ A -> ~ A
  :=
    fun not_not_not_A : ((A -> False) -> False) -> False =>
      fun a : A => (* want False *)
        not_not_not_A (fun a_impl_false => a_impl_false a).

Definition or_comm :
  A \/ B -> B \/ A
  := fun a_or_b =>
       match a_or_b with
       | or_introl a => or_intror a
       | or_intror b => or_introl b
       end.

End PropositionalLogic.

Section Quantifiers.

Variable T : Type.
Variable A : Prop.
Variable P Q : T -> Prop.

Definition forall_conj_comm :
  (forall x, P x /\ Q x) <-> (forall x, Q x /\ P x)
  :=
    conj 
      (fun all_pq =>
         fun x =>
           match all_pq x with
           | conj px qx => conj qx px
           end)
      (fun all_qp =>
         fun x =>
           match all_qp x with
           | conj qx px => conj px qx
           end).

Definition forall_disj_comm :
  (forall x, P x \/ Q x) <-> (forall x, Q x \/ P x)
  :=
    let all_p_or_q_impl_all_q_or_p :=
        fun all_p_or_q =>
          fun x =>
            match all_p_or_q x with
            | or_introl px => or_intror px
            | or_intror qx => or_introl qx
            end
    in
    let all_q_or_p_impl_all_p_or_q :=
                fun all_q_or_p =>
                  fun x =>
            match all_q_or_p x with
            | or_introl qx => or_intror qx
            | or_intror px => or_introl px
            end
    in
    conj all_p_or_q_impl_all_q_or_p all_q_or_p_impl_all_p_or_q.

Definition not_exists_forall_not :
  ~(exists x, P x) -> forall x, ~P x
  := fun foo : (exists x, P x) -> False =>
       fun x => (* Want: P x -> False *)
         fun px : P x => 
           foo (@ex_intro T P x px).

Definition exists_forall_not
           (ex_x_a_impl_px : exists x, A -> P x)
           (all_not_px : forall x, P x -> False)
           (a : A)
  : False
  := match ex_x_a_impl_px with
     | ex_intro _ x a_impl_px => all_not_px x (a_impl_px a)
     end.
    
(** Extra exercise (feel free to skip): the dual Frobenius rule *)
Definition LEM :=
  forall P : Prop, P \/ ~ P.

Definition Frobenius2 :=
  forall (A : Type) (P : A -> Prop) (Q : Prop),
    (forall x, Q \/ P x) <-> (Q \/ forall x, P x).

(* Uncomment the following block to understand how Frobenius2_impl_lem works *)
(* Variable frobenius2 : Frobenius2. *)
(* Variable R : Prop. *)
(* Definition foo := frobenius2 R (fun _ => False) R. *)
(* Check foo : (R -> R \/ False) <-> R \/ (R -> False). *)
(* Definition R_to_R_or_False_impl_R_or_neg_R := *)
(*   match foo with *)
(*   | conj R_to_R_or_False_impl_R_or_neg_R _ => R_to_R_or_False_impl_R_or_neg_R *)
(*   end. *)
(* Check R_to_R_or_False_impl_R_or_neg_R. *)
(* END block explaining Frobenius2_impl_lem works *)

Definition Frobenius2_impl_lem : Frobenius2 -> LEM
  := fun frobenius2 : Frobenius2 =>
       fun R : Prop =>
         match frobenius2 R (fun _ => False) R with
         | conj R_to_R_or_False_impl_R_or_neg_R _ =>
           R_to_R_or_False_impl_R_or_neg_R (fun r => or_introl r)
         end.

Definition exfalso_quodlibet {A : Prop} :
  False -> A
:= fun pF : False => match pF with end.

Definition lem_impl_Frobenius2 : LEM -> Frobenius2
  := fun lem : LEM =>
       fun A : Type =>
         fun P : A -> Prop =>
           fun Q : Prop =>
             conj
               (fun forall_x_q_or_px : (forall x, Q \/ P x) =>
                  match lem Q with
                  | or_introl q => or_introl q
                  | or_intror not_q =>
                    or_intror (fun x =>
                                 match forall_x_q_or_px x with
                                 | or_introl q => exfalso_quodlibet (not_q q)
                                 | or_intror px => px
                                 end)
                  end)
               (fun q_or_forall_x_p_x: (Q \/ forall x, P x) =>
                  match q_or_forall_x_p_x with
                  | or_introl q => (fun x => or_introl q) : (forall x, Q \/ P x)
                  | or_intror forall_x_p_x => (fun x => or_intror (forall_x_p_x x)) : (forall x, Q \/ P x)
                  end).

Definition lem_iff_Frobenius2 :
  LEM <-> Frobenius2
  := conj lem_impl_Frobenius2 Frobenius2_impl_lem.

End Quantifiers.

Section Equality.

(** exercise: *)
Definition f_congr {A B} (f : A -> B) (x y : A) :
  x = y  ->  f x = f y
  := fun x_eq_y =>
        match x_eq_y with
        | eq_refl => eq_refl (f x)
        end.

Definition f_congr' A B (f g : A -> B) (x y : A) :
  f = g  ->  x = y  ->  f x = g y
  := fun f_eq_g x_eq_y =>
       match f_eq_g in _ = g return f x = g y with
       | eq_refl =>
         match x_eq_y in _ = y return f x = f y with
         | eq_refl => eq_refl (f x)
         end
       end.

(** extra exercise *)
(* Idk what I'm supposed to construct here, so I am commenting it out *)
(* Definition congId A {x y : A} (p : x = y) : *)
(*   @f_congr A A (fun x => x) x y. *)

(* exercise *)
Definition pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2)
  := fun a1_b1_eq_a2_b2 =>
       match a1_b1_eq_a2_b2 with
       | eq_refl => conj eq_refl eq_refl
       end.

End Equality.



Section ExtensionalEqualityAndComposition.

Variables A B C D : Type.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

(* PHI: stopped here 2021-04-23 *)

(** Exercise 2a *)
(** [\o] is a notation for function composition in MathComp, prove that it's associative *)


Definition compA (f : A -> B) (g : B -> C) (h : C -> D) :
  (h \o g) \o f = h \o (g \o f)
  :=
    erefl.


(** [=1] stands for extensional equality on unary functions,
    i.e. [f =1 g] means [forall x, f x = g x].
    This means it's an equivalence relation, i.e. it's reflexive, symmetric and transitive.
    Let us prove a number of facts about [=1]. *)


(** Exercise: Reflexivity *)
Definition eqext_refl :
  forall (f : A -> B), f =1 f
:=

(** Exercise: Symmetry *)
Definition eqext_sym :
  forall (f g : A -> B), f =1 g -> g =1 f
:=

(** Exercise: Transitivity *)
Definition eqext_trans :
  forall (f g h : A -> B), f =1 g -> g =1 h -> f =1 h
:=

(** Exercise: left congruence *)
Definition eq_compl :
  forall (f g : A -> B) (h : B -> C),
    f =1 g -> h \o f =1 h \o g
:=

(** Exercise: right congruence *)
Definition eq_compr :
  forall (f g : B -> C) (h : A -> B),
    f =1 g -> f \o h =1 g \o h
:=

End ExtensionalEqualityAndComposition.


From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

(* After importing `eqtype` you need to either use a qualified name for
`eq_refl`: `Logic.eq_refl`, or use the `erefl` notation.
This is because `eqtype` reuses the `eq_refl` identifier for a
different lemma.
 *)

Definition iff_is_if_and_only_if :
  forall a b : bool, (a ==> b) && (b ==> a) = (a == b)
:=

Definition negbNE :
  forall b : bool, ~~ ~~ b = true -> b = true
:=
