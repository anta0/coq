Module MineSweeper.

Require Import Arith Omega.

Set Implicit Arguments.

Section vector.
Variable A: Type.
Inductive vector : nat -> Type :=
  | vnil : vector 0
  | vcons : forall (a:A) (n:nat), vector n -> vector (S n)
.
End vector.
Implicit Arguments vnil [A].
Delimit Scope vector_scope with vec.
Open Scope vector_scope.
Infix "::" := vcons
              (at level 60, right associativity)
              : vector_scope.
Notation "[]" := vnil: vector_scope.
Notation "[ x , .. , z ]" :=
         (x :: .. (z :: []) ..)
         (at level 0)
         : vector_scope.
Section vmap.
Variables X Y: Type.
Variable f: X -> Y.
Fixpoint vmap {n} (v: vector X n): vector Y n :=
 match v with
 | vnil => vnil
 | vcons a _ v' => vcons (f a) (vmap v')
 end.
End vmap.
Section vzip.
Variables X Y Z: Type.
Variable f: X -> Y -> Z.

Fixpoint vzip {n} (v1: vector X n) (v2: vector Y n): vector Z n.
 destruct v1.
  constructor.
 inversion v2.
  constructor.
   apply f. exact a. exact a0.
   apply vzip. exact v1. exact X0.
Defined.
End vzip.

Definition vi0 {m}: 0 < S m := lt_0_Sn m.
Definition viS {n m}: n < m -> S n < S m := lt_n_S n m.

Notation "!0" := vi0.
Notation "!+ i" := (viS i)
                   (at level 5, right associativity).

Section viget.
Variable A: Type.
Lemma lt_0_False: forall n, n < 0 -> False. intros. omega. Qed.
Fixpoint viget {n} (v: vector A n) m (H: m < n): A.
 destruct v.
 (* vnil *)
  apply lt_0_False in H. destruct H.
 destruct m.
 (* 0 *)
  exact a.
 (* (S _) *)
  apply viget with (n:=n) (m:=m).
  exact v. apply lt_S_n. exact H.
Defined.
End viget.
Notation "v '_[' i ]" := (viget v i)
                      (at level 7, left associativity)
                      : vector_scope.
Section viset.
Variable A: Type.
Fixpoint viset {n} (v: vector A n) m (H: m < n) (b:A) {struct v}: vector A n.
 destruct v as [|a n' v'].
 (* vnil => False *)
  apply lt_0_False in H. destruct H.
 destruct m.
 (* 0 *)
  exact (b::v').
 (* S _ *)
  apply (fun v''=> a::v'').
  apply viset with m; try assumption.
   apply lt_S_n. assumption.
Defined.
End viset.
Notation "v '_[' i ] / b" := (viset v i b)
                          (at level 7, b at level 50, left associativity)
                          : vector_scope.
Delimit Scope matrix_scope with mat.
Open Scope matrix_scope.
Notation "'mlengths'" := (vector nat)
                         (at level 0)
                         : matrix_scope.
Section matrix.
Variable A: Type.
Inductive matrix: forall n, mlengths n -> Type :=
  | mscalar: A -> matrix []
  | mvector: forall n m v,
             vector (@matrix n v) m ->
             @matrix (S n) (m::v)
.
End matrix.
Notation "''{}'" := (mvector []%vec): matrix_scope.
Notation "'#{' x , .. , z }" :=
         (mvector (x :: .. (z :: []) ..)%vec)
         (at level 0)
         : matrix_scope.
Notation "''{' x , .. , z }" :=
         (mvector (mscalar x :: .. (mscalar z :: []) ..)%vec)
         (at level 0)
         : matrix_scope.
Section fillvec.
Variable A: Type.
Variable a: A.
Fixpoint fillvec n: vector A n :=
 match n with
 | O => vnil
 | S n' => a :: fillvec n'
 end.
End fillvec.

Section fillmat.
Variable A: Type.
Variable a: A.
Fixpoint fillmat n (v: mlengths n): matrix A v.
 destruct n as [|n'].
 (* n = O *)
  dependent inversion v. constructor. assumption.
 (* n = S n' *)
 dependent inversion v; subst.
  constructor.
  apply fillvec.
  apply fillmat.
Defined.
End fillmat.

Section mmap.
Variables A B: Type.
Variable f: A -> B.
Fixpoint mmap n (v: mlengths n) (m: matrix A v): matrix B v.
 destruct n as [|n'].
 (* n = O *)
  dependent inversion v; subst.
  inversion m; subst.
  apply mscalar. apply f. assumption.
 (* n = S n' *)
 inversion m as [|l'' m'' v'']; subst. clear H.
 constructor.
 specialize (mmap n' v'').
 apply (vmap mmap).
 exact X.
Defined.
End mmap.

Require Import Eqdep_dec.

Section mzip.
Variables A B C: Type.
Variable f: A -> B -> C.
Fixpoint mzip n (v: mlengths n)
              (m1: matrix A v) (m2: matrix B v): matrix C v.
 destruct n as [|n'].
 (* n = 0 *)
  inversion m1. inversion m2.
  apply mscalar; apply f; assumption.
 (* n = S n' *)
  inversion m1 as [|? m1' l1 v1 H1 Heq1]; subst.
  inversion m2 as [|? m2' l2 v2 H2 Heq2]; subst.
  apply (inj_pair2_eq_dec _ eq_nat_dec _ _ _) in Heq1.
  apply (inj_pair2_eq_dec _ eq_nat_dec _ _ _) in Heq2.
  assert (Heq: m1' :: l1 = m2' :: l2).
   eapply eq_trans. apply Heq1. symmetry. exact Heq2.
   clear Heq1. clear Heq2.
  assert (Heqm: m1' = m2') by (inversion Heq; reflexivity).
  assert (Heql: l1 = l2).
   inversion Heq.
   apply (Eqdep_dec.inj_pair2_eq_dec _ eq_nat_dec _ _ _) in H1.
   exact H1.
  clear Heq. rename l2 into l. rename m2' into m'. subst.
  apply mvector.
  specialize (mzip n' l).
  apply (vzip mzip); assumption.
Defined.
End mzip.

Example mzip_ex1: mzip plus '{1,2} '{3,4} = '{4,6}.
Proof.
 simpl.
 (*
1 subgoal
______________________________________(1/1)
eq_rect_r
  (fun l1 : mlengths 0 => vector (matrix nat l1) 2 -> matrix nat (2 :: l1))
  (fun v1 : vector (matrix nat []) 2 =>
   eq_rect_r
     (fun m1' : nat => vector (matrix nat []) m1' -> matrix nat [m1'])
     (fun v0 : vector (matrix nat []) 2 =>
      mvector
......
*)
 Abort.
