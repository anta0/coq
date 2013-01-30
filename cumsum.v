Set Implicit Arguments.
Require Import Arith ZArith QArith.
Require Import List SetoidList SetoidPermutation.
Import ListNotations.
Require Import Program Recdef.
Require Import RelationClasses.

Open Scope nat_scope.

Class AbelianGroup (G: Set) (g_op: G -> G -> G) (g_eq: G -> G -> Prop): Set :=
 { g_equivalence: Equivalence g_eq
 ; g_associative: forall x y z, g_eq (g_op x (g_op y z)) (g_op (g_op x y) z)
 ; g_id: G
 ; g_identity_r: forall x, g_eq (g_op x g_id) x
 ; g_inv: G -> G
 ; g_inverse_r: forall x, g_eq (g_op x (g_inv x)) g_id
 ; g_commutative: forall x y, g_eq (g_op x y) (g_op y x)
 ; g_op_morphism: forall x x', g_eq x x' -> forall y y', g_eq y y' -> g_eq (g_op x y) (g_op x' y')
 ; g_inv_morphism: forall x x', g_eq x x' -> g_eq (g_inv x) (g_inv x')
 }.

Global Add Parametric Relation (G: Set) g_op g_eq (g: AbelianGroup g_op g_eq): G g_eq
 reflexivity proved by (@Equivalence_Reflexive _ _ (g_equivalence (g_eq:=g_eq)))
 symmetry proved by (@Equivalence_Symmetric _ _ (g_equivalence (g_eq:=g_eq)))
 transitivity proved by (@Equivalence_Transitive _ _ (g_equivalence (g_eq:=g_eq)))
 as g_eq_rel.
Global Add Parametric Morphism (G: Set) g_op g_eq (g: @AbelianGroup G g_op g_eq):
 g_op with
 signature g_eq ==> g_eq ==> g_eq as g_op_morph.
Proof. exact g_op_morphism. Qed.
Global Add Parametric Morphism (G: Set) g_op g_eq (g: @AbelianGroup G g_op g_eq):
 (g_inv (g_eq:=g_eq)) with
 signature g_eq ==> g_eq as g_inv_morph.
Proof. exact g_inv_morphism. Qed.

Instance AbelianGroup_Zplus: AbelianGroup Zplus eq :=
 { g_equivalence := gen_st Z
 ; g_id := 0%Z
 ; g_inv := Zopp
 ; g_associative := Zplus_assoc
 ; g_identity_r := Z.add_0_r
 ; g_inverse_r := Z.add_opp_diag_r
 ; g_commutative := Zplus_comm
 }.
 intros; subst; auto.
 intros; subst; auto.
Defined.

Inductive QZ: Set :=
 | Qz: forall q: Q, ~ q == 0%Q -> Z -> QZ.

Definition QZeq (x y: QZ): Prop :=
 let (xq, _, xz) := x in
 let (yq, _, yz) := y in
 xq == yq /\ xz = yz.

Theorem QZeq_refl: forall x, QZeq x x.
Proof.
 intros.
 destruct x.
 split; reflexivity.
Qed.

Theorem QZeq_sym: forall x y, QZeq x y -> QZeq y x.
Proof.
 intros.
 destruct x, y, H.
 unfold QZeq. rewrite H0. rewrite H.
 split; reflexivity.
Qed.

Theorem QZeq_trans: forall x y z, QZeq x y -> QZeq y z -> QZeq x z.
Proof.
 intros.
 unfold QZeq in *.
 destruct x, y, z.
 destruct H, H0. subst.
 rewrite H. rewrite H0.
 split; reflexivity.
Qed.

Instance QZeq_equivalence: @Equivalence QZ QZeq :=
 { Equivalence_Reflexive := QZeq_refl
 ; Equivalence_Symmetric := QZeq_sym
 ; Equivalence_Transitive := QZeq_trans
 }.
Add Setoid QZ QZeq QZeq_equivalence as QZeq_setoid_reg.

Program Definition QZmult (x y: QZ): QZ :=
 let (xq, Hx, xz) := x in
 let (yq, Hy, yz) := y in
 @Qz (xq * yq)%Q _ (xz + yz)%Z.
Next Obligation.
 intro.
 destruct (Qmult_integral _ _ H); auto.
Defined.

Program Definition QZinv (x: QZ): QZ :=
 let (q, H, z) := x in
 @Qz (/q)%Q _ (-z)%Z.
Next Obligation.
 intro.
 specialize (Qmult_inv_r _ H); intro.
 rewrite H0 in H1.
 rewrite Qmult_0_r in H1.
 apply Q_apart_0_1.
 symmetry.
 assumption.
Defined.

Definition QZfromQ (q: Q) (Hq: ~ q == 0): QZ :=
 @Qz q Hq 0.

Program Definition QZ0 := @Qz 1%Q _ 1%Z.

Program Definition QZ1 := @QZfromQ 1%Q _.

Theorem QZmult_associative: forall x y z,
        QZeq (QZmult x (QZmult y z)) (QZmult (QZmult x y) z).
Proof.
 intros. unfold QZeq.
 destruct x, y, z; simpl.
 split.
  ring.
 ring.
Qed.

Theorem QZmult_identity_r: forall x,
        QZeq (QZmult x QZ1) x.
Proof.
 intros.
 destruct x; simpl.
 split; ring.
Qed.

Theorem QZinv_inverse_r: forall x,
        QZeq (QZmult x (QZinv x)) QZ1.
Proof.
 intros.
 destruct x; simpl.
 split.
  apply Qmult_inv_r. assumption.
 apply Z.add_opp_diag_r.
Qed.

Theorem QZmult_commutative: forall x y,
        QZeq (QZmult x y) (QZmult y x).
Proof.
 intros.
 destruct x, y; simpl.
 split; ring.
Qed.

Theorem QZmult_well_defined:
        forall x x', QZeq x x' ->
        forall y y', QZeq y y' ->
        QZeq (QZmult x y) (QZmult x' y').
Proof.
 intros.
 destruct x, x', y, y'; unfold QZeq in *; simpl in *.
 destruct H, H0. subst.
 rewrite H; rewrite H0.
 split; reflexivity.
Qed.

Theorem QZinv_well_defined:
        forall x x', QZeq x x' ->
        QZeq (QZinv x) (QZinv x').
Proof.
 intros.
 destruct x, x'; unfold QZeq in *; simpl in *.
 destruct H; subst.
 rewrite H.
 split; reflexivity.
Qed.

Instance AbelianGroup_QZmult: AbelianGroup QZmult QZeq :=
 { g_equivalence := QZeq_equivalence
 ; g_id := QZ1
 ; g_inv := QZinv
 ; g_associative := QZmult_associative
 ; g_identity_r := QZmult_identity_r
 ; g_inverse_r := QZinv_inverse_r
 ; g_commutative := QZmult_commutative
 ; g_op_morphism := QZmult_well_defined
 ; g_inv_morphism := QZinv_well_defined
 }.

Section g_thems.
Variable (G: Set)
         (g_op: G -> G -> G)
         (g_eq: G -> G -> Prop)
         (abeliangroup: AbelianGroup g_op g_eq).

Infix ".+" := g_op (at level 50, left associativity).
Infix ".=" := g_eq (at level 70, no associativity).
Notation ".- x" := (g_inv x) (at level 35, right associativity).
Notation "'.0'" := g_id.
Notation "x .- y" := (x .+ .- y) (at level 50, left associativity).

Theorem g_identity_l: forall x, .0 .+ x .= x.
Proof.
 intros.
 rewrite g_commutative.
 rewrite g_identity_r.
 reflexivity.
Qed.

Theorem g_inverse_l: forall x, .-x .+ x .= .0.
Proof.
 intros.
 rewrite g_commutative.
 rewrite g_inverse_r.
 reflexivity.
Qed.

Theorem g_id_unique: forall e,
        (forall x, x .+ e .= x) ->
        e .= g_id.
Proof.
 intros.
 rewrite <- (H .0).
 rewrite g_identity_l.
 reflexivity.
Qed.
Implicit Arguments g_id_unique [e].

Theorem g_inv_unique: forall g,
        forall h, g .+ h .= .0 -> .-g .= h.
Proof.
 intros.
 symmetry.
 rewrite <- g_identity_r at 1.
 rewrite <- (g_inverse_r g).
 rewrite g_associative.
 rewrite (g_commutative h g).
 rewrite H.
 rewrite g_identity_l.
 reflexivity.
Qed.
Implicit Arguments g_inv_unique [g h].

Theorem g_inv_twice: forall a,
        .- .- a .= a.
Proof.
 intros.
 assert (A: .-a  .+ a .= .0).
  rewrite g_inverse_l.
  reflexivity.
 exact (g_inv_unique A).
Qed.

Theorem g_op_inv: forall a b,
        .-(a .+ b) .= (.-a) .+ (.-b).
Proof.
 intros.
 assert (A: (a.+b).+(.-a .+ .-b) .= .0).
  rewrite (g_commutative (.-a) (.-b)).
  assert (B: a.+b.+(.-b.-a) .= a.+(b.+.-b).-a).
   do 3 rewrite <- g_associative.
   reflexivity.
  rewrite B.
  rewrite g_inverse_r.
  rewrite g_identity_r.
  rewrite g_inverse_r.
  reflexivity.
 exact (g_inv_unique A).
Qed.

Theorem g_invop_identity_r: forall x, x .- .0 .= x.
Proof.
 intros.
 rewrite <- (g_inverse_l x).
 rewrite g_commutative.
 rewrite g_op_inv.
 rewrite g_inv_twice.
 rewrite <- g_associative.
 rewrite (g_commutative (.-x) x).
 rewrite g_inverse_r.
 rewrite g_identity_r.
 reflexivity.
Qed.

Theorem g_invid_id: .-.0 .= .0.
Proof.
 intros.
 exact (g_id_unique g_invop_identity_r).
Qed.

Definition g_sum (xs: list G): G :=
 fold_right g_op .0 xs.
End g_thems.
Arguments g_sum [G g_op g_eq abeliangroup] xs.

Section AbelianGroup.
Variable (G: Set)
         (g_op: G -> G -> G)
         (g_eq: G -> G -> Prop)
         (abeliangroup: AbelianGroup g_op g_eq).

Infix ".+" := g_op (at level 50, left associativity).
Infix ".=" := g_eq (at level 70, no associativity).
Notation ".- x" := (g_inv x) (at level 35, right associativity).
Notation "'.0'" := g_id.
Notation "x .- y" := (x .+ .- y) (at level 50, left associativity).

Section tactic_lemmas.
Variable X: Set.
Variable op: X -> X -> X.
Variable qq: X -> X -> Prop.
Variable AG: AbelianGroup op qq.
Lemma g_movetohead_lemma1: forall x, qq x x.
Proof. reflexivity. Qed.
Lemma g_movetohead_lemma2: forall x y x' y', qq x x' -> qq y y' -> qq (op x y) (op x' y').
Proof. intros. apply g_op_morphism; auto. Qed.
Lemma g_movetohead_lemma3: forall x y x' y', qq x x' -> qq y y' -> qq (op x y) (op y' x').
Proof. intros. rewrite (g_commutative y' _). apply g_op_morphism; auto. Qed.
Lemma g_movetohead_lemma4: forall t x y x' z, qq x x' -> qq y (op t z) -> qq (op x y) (op (op t x') z).
Proof. intros. rewrite (g_commutative t _). rewrite <- g_associative. apply g_op_morphism; auto. Qed.
Lemma g_movetohead_lemma5: forall x y z, qq x y -> qq y z -> qq x z.
Proof. intros. rewrite H. assumption. Qed.
Lemma g_leftfhead_lemma1:  forall x y z x' y', qq (op x y) (op x' y') -> qq (op (op x y) z) (op x' (op y' z)).
Proof. intros. rewrite H. rewrite g_associative. reflexivity. Qed.
End tactic_lemmas.

Ltac idtact s := fun x => let t := type of x in idtac s t.

Ltac g_lefthead_AG op qq AG e :=
 match e with
 | op (op ?x ?y) ?z => let R := g_lefthead_AG op qq AG (op x y) in
                       constr:(@g_leftfhead_lemma1 _ op qq AG x y z _ _ R)
 | ?x               => constr:(g_movetohead_lemma1 AG x)
 end.

(* e .= ? を返す *)
Ltac g_movetohead_AG_rec op qq AG e t f :=
 match e with
 | op ?x ?y => g_movetohead_AG_rec op qq AG x t ltac:(fun p =>
               g_movetohead_AG_rec op qq AG y t ltac:(fun q =>
               match constr:(p, q) with
               | ((true, ?pR), (_, ?qR)) =>
                 f (true, @g_movetohead_lemma2 _ op qq AG x y _ _ pR qR)
               | ((false, ?pR), (true, ?qR)) =>
                 match type of qR with qq _ ?qRr =>
                 let qT := g_lefthead_AG op qq AG qRr in
                 let qR' := constr:(@g_movetohead_lemma5 _ op qq AG _ _ _ qR qT) in
                 match type of qR' with
                 | qq (op _ _) _ =>
                   f (true, @g_movetohead_lemma4 _ op qq AG t x y _ _ pR qR')
                 | _           =>
                   f (true, @g_movetohead_lemma3 _ op qq AG x y _ _ pR qR')
                 end end
               | ((false, ?pR), (false, ?qR)) =>
                 f (false, @g_movetohead_lemma2 _ op qq AG x y _ _ pR qR)
               end))
 | t        => f (true, g_movetohead_lemma1 AG t)
 | ?x       => f (false, g_movetohead_lemma1 AG x)
 end.
Ltac g_movetohead_eq_AG op qq AG t :=
 match goal with
 | [ |- qq ?e _ ] => g_movetohead_AG_rec op qq AG e t ltac:(fun p =>
                     match p with (_, ?R) => rewrite R end)
 end.

Ltac g_simplify :=
 repeat (
  rewrite <- g_associative ||
  rewrite g_op_inv ||
  rewrite g_inv_twice ||
  rewrite g_identity_l || rewrite g_identity_r ||
  rewrite g_inverse_l || rewrite g_inverse_r
 ).

Ltac g_eq_auto_AG op qq AG n :=
 do n (
  g_simplify;
  try (match goal with
  | |- qq (op ?y _) (op ?y _) => apply g_op_morphism
  | |- qq _ (op ?y _) => g_movetohead_eq_AG op qq AG y;
                       repeat (rewrite <- g_associative);
                       apply g_op_morphism
  | |- qq (op ?y _) _ => g_movetohead_eq_AG op qq AG (g_inv y);
                       repeat (rewrite    g_associative);
                       try (rewrite g_inv_twice);
                       (rewrite g_inverse_l || rewrite g_inverse_r)
  end);
  try (try solve [auto | reflexivity]);
  try (repeat (rewrite g_associative);
       apply g_commutative)
 ).
Tactic Notation "g_eq_auto" integer(n) := g_eq_auto_AG g_op g_eq abeliangroup n.
Tactic Notation "g_eq_auto_AG" constr(op) constr(qq) constr(AG) integer(n) := g_eq_auto_AG op qq AG n.

Goal forall x1 x2 x3, x1 .- (x3 .- x2 .+ x1) .= x2 .- x3.
Proof.
 intros.
 g_eq_auto 3.
Qed.

Goal forall (X: Set) (op: X -> X -> X) qq (AG: AbelianGroup op qq), forall x1 x2 x3, qq (op x1 (g_inv (op (op x3 (g_inv x2)) x1))) (op x2 (g_inv x3)).
Proof.
 intros.
 g_eq_auto_AG op qq AG 3.
Qed.

Ltac aomega := abstract omega.

Section enumto_list.
Variables (A: Type) (nmax: nat) (f: forall i, i < nmax -> A).

Program Definition enumto_list_acc_spec (n: nat) (l: list A) :=
 length l = nmax - n /\
 forall i d, i < nmax - n ->
        exists H, nth i l d = @f (n+i) H.
Definition enumto_list_spec := enumto_list_acc_spec 0.

Program Fixpoint enumto_list_acc (n: nat) (Hn: n <= nmax) (acc: {l | enumto_list_acc_spec n l}):
 {l | enumto_list_spec l} :=
 match n with
 | O => acc
 | S n' => @enumto_list_acc n' _ (@f n' _ :: acc)
 end.
Next Obligation.
 aomega.
Defined.
Next Obligation.
 destruct H.
 split.
  simpl. aomega.
 intros. simpl.
 destruct i.
  unfold lt. rewrite <- plus_n_O.
  exists Hn. reflexivity.
 apply lt_pred in H. rewrite <- NPeano.Nat.sub_succ_r in H.
 specialize (e0 i d H).
 rewrite <- plus_Snm_nSm.
 exact e0.
Defined.

Program Definition enumto_list := @enumto_list_acc nmax _ [].
Next Obligation.
 split.
  simpl. aomega.
 intros.
  exfalso. aomega.
Defined.

End enumto_list.

Section DAG.
Definition Vertex := nat.

Inductive Edge: Set :=
 | edge: forall v u: Vertex, v < u -> Edge.
Definition Edges := list Edge.

Definition Edgeeq (e f: Edge) :=
 let (i , j , _) := e in
 let (i', j', _) := f in
 i = i' /\ j = j'.

Definition Edgeseq :=
 eqlistA Edgeeq.

Definition EdgeIn (e: Edge) (l: Edges): Prop :=
 InA Edgeeq e l.

Definition Parent E (v u: Vertex): Prop :=
 exists (H: v < u), EdgeIn (edge H) E.
End DAG.

Section cumsum_diffs.
Definition Val := G.

Section lenV.
Variable lenV: nat.
Definition Vertex_ok v := v < lenV.
Definition Vertex' := { v: Vertex | Vertex_ok v }.

Definition Vertex'_eq (v w: Vertex'): Prop :=
 ` v = ` w.

Lemma Forall_Parent_cons: forall e v l x,
 Forall (fun u: Vertex' => Parent e (`u) v) l ->
 Forall (fun u: Vertex' => Parent (x::e) (`u) v) l.
Proof.
 intros.
 induction H.
  apply Forall_nil.
 constructor.
 destruct H as [Hltx HIn].
 exists Hltx. destruct x. simpl. right. assumption.
 apply IHForall.
Qed.

Program Fixpoint getparents (e: Edges) (v: Vertex'):
 {  l: list Vertex'
 |  Forall (fun u: Vertex' => Parent e (` u) (` v)) l
 /\ forall u: Vertex', Parent e (` u) (` v) -> InA Vertex'_eq u l
 } :=
 match e with
 | [] => []
 | edge u v' Hlt :: e' => _ (getparents e' v)
 end.
Next Obligation.
 split.
  constructor.
 intros.
 unfold Parent in H.
 destruct H.
 simpl in H.
 inversion_clear H.
Defined.
Next Obligation.
 destruct v as [v Hv']. simpl in *.
 destruct (eq_nat_dec v v').
  subst.
  specialize (lt_trans _ _ _ Hlt Hv'); intro Hu.
  exists (exist Vertex_ok u Hu :: x).
  split.
  (* -> *)
  constructor.
   unfold Parent.
   simpl. exists Hlt.
   left. split; reflexivity.
  apply Forall_Parent_cons. assumption.
  (* <- *)
  intros.
  unfold Vertex'_eq.
  destruct (eq_nat_dec u (` u0)).
   subst.
   constructor.
   simpl. reflexivity.
  apply InA_cons_tl.
  apply H0.
  unfold Parent in H1.
  destruct H1.
  simpl in H1.
  inversion_clear H1.
   destruct H2. destruct (n (eq_sym H1)).
  unfold Parent.
  exists x0. assumption.
 exists x.
 split.
 (* -> *)
 apply Forall_Parent_cons. assumption.
 (* <- *)
 intros.
 apply H0.
 unfold Parent in *.
 destruct H1.
 inversion_clear H1.
  destruct H2.
  destruct (n H2).
 exists x0.
 assumption.
Defined.

Notation "'Σ[' F , i ] ( 'fun' j => f )" := (g_sum (map (fun j => f) (` (getparents F i))))
                          (at level 10, F at level 20, i at level 20, j ident, f at level 99, no associativity
                          ,format "Σ[ F ,  i ]  ( fun  j  =>  f )").

Theorem getparents_spec1: forall (e: Edges) (v v': Vertex'),
        Vertex'_eq v v' ->
        eqlistA Vertex'_eq (` (getparents e v)) (` (getparents e v')).
Proof.
 intros e v v' Heqv'.
 induction e.
  simpl. constructor.
 destruct a.
 simpl. unfold getparents_obligation_2. simpl.
 destruct (getparents e v) as [? [? ?]].
 destruct (getparents e v') as [? [? ?]].
 destruct v as [v Hv]. destruct v' as [v' Hv'].
 destruct (eq_nat_dec v u), (eq_nat_dec v' u); simpl in *.
 (* = *)
 subst. simpl.
 constructor.
  unfold Vertex'_eq. simpl.
  reflexivity.
 assumption.
  assert (C: u <> u).
   unfold Vertex'_eq in Heqv'. simpl in Heqv'.
   rewrite <- e0 at 1. rewrite Heqv' at 1. assumption.
  exfalso; apply C; reflexivity.
  assert (C: u <> u).
   unfold Vertex'_eq in Heqv'. simpl in Heqv'.
   rewrite <- e0 at 1. rewrite <- Heqv' at 1. assumption.
  exfalso; apply C; reflexivity.
 (* <> *)
 assumption.
Qed.


Section mainops.
Definition Values := { vs: list Val | length vs = lenV }.
Variable values: Values.
Variable E: Edges.

Definition value_spec (v: Vertex') (x: Val) := forall d, x = nth (`v) (`values) d.

Program Definition value (v: Vertex'): { x: Val | value_spec v x } :=
 match nth (`v) (map Some values) None with
 | None => False_rec _ _
 | Some x => x
 end.
Next Obligation.
 destruct v as [v Hv].
 assert (Hlen: v < length (map Some (`values))).
  rewrite map_length. rewrite (proj2_sig values). assumption.
 specialize (nth_In (map Some (`values)) None Hlen).
 intro H.
 simpl in Heq_anonymous. rewrite <- Heq_anonymous in H.
 clear Heq_anonymous; clear Hv; clear Hlen.
 destruct values as [values' Hvalues']. simpl in H. clear Hvalues'. clear values.
 induction values'; simpl in *.
  exact H.
 apply IHvalues'.
 destruct H; [inversion H|].
 assumption.
Defined.
Next Obligation.
 unfold value_spec. intros.
 destruct v as [v Hv].
 unfold Vertex_ok in Hv.
 destruct values as [vs Hvs].
 simpl in *.
 rename Heq_anonymous into H.
 assert (Hlen: v < length (map Some vs)).
  rewrite map_length. rewrite Hvs. assumption.
 rewrite (nth_indep (map Some vs) None (Some d) Hlen) in H.
 rewrite (map_nth Some vs d v) in H.
 inversion H.
 reflexivity.
Qed.

Theorem value_eq': forall v v': Vertex',
        Vertex'_eq v v' ->
        ` (value v) = ` (value v').
Proof.
 intros.
 assert (A: forall w, ` (value w) = nth (` w) (` values) g_id).
  intros.
  apply (@proj2_sig _ (value_spec w)).
 do 2 rewrite A.
 destruct v, v'. simpl.
 unfold Vertex'_eq in H. simpl in H. rewrite H.
 reflexivity.
Qed.

Program Fixpoint getparents_lt_rec (i: Vertex)
  (ps: list Vertex') (Hps: Forall (fun u: Vertex' => Parent E (`u) i) ps):
  list {v: Vertex' | v < i} :=
 match ps with
 | [] => []
 | p::ps' => p :: @getparents_lt_rec i ps' _
 end.
Next Obligation.
 apply proj2_sig.
Defined.
Next Obligation.
 apply Forall_inv in Hps.
 unfold Parent in Hps.
 destruct Hps as [H HH].
 assumption.
Defined.
Next Obligation.
 generalize (refl_equal (p::ps')).
 pattern (p::ps') at 1.
 destruct Hps; intros Heq.
  discriminate Heq.
 injection Heq; intros; subst.
 assumption.
Defined.

Definition getparents_lt (i: Vertex'):
 list { v: Vertex' | ` v < ` i } :=
 let 'exist ps (conj Hps _) := getparents E i in
 @getparents_lt_rec (` i) ps Hps.

Theorem getparents_lt_spec1: forall i,
        map (fun x => proj1_sig x) (getparents_lt i) = ` (getparents E i).
Proof.
 intros.
 unfold getparents_lt.
 destruct (getparents E i) as [? [? ?]]. simpl.
 clear i0.
 induction x.
  simpl.
  reflexivity.
 simpl.
 destruct i as [i Hi]. destruct a as [a Ha].
 simpl in *.
 rewrite IHx.
 reflexivity.
Qed.

Section getparents_ind.
Variable P: Vertex' -> Prop.

Hypothesis H: forall v,
  Forall P (` (getparents E v)) -> P v.
Program Fixpoint getparents_ind (v: Vertex') {measure (` v)}: P v :=
 _.
Next Obligation.
 apply H.
 destruct (getparents E v) as [ps [Hps Hps2]]. simpl in *. clear Hps2.
 induction ps.
  constructor.
 constructor.
  inversion_clear Hps.
  destruct H0.
  apply getparents_ind.
  assumption.
 apply IHps.
 inversion_clear Hps.
 assumption.
Defined.
End getparents_ind.


Inductive cumsum_i_spec: Vertex' -> Val -> Prop :=
 | cumsum_i_spec_rec: forall v (x: Val),
   cumsum_i_spec_sub v (` (getparents E v)) x ->
   cumsum_i_spec v (` (value v) .+ x)
with cumsum_i_spec_sub: Vertex' -> list Vertex' -> Val -> Prop :=
 | cumsum_i_spec_sub_nil: forall v, cumsum_i_spec_sub v [] g_id
 | cumsum_i_spec_sub_cons: forall v t l (x y: Val),
                           cumsum_i_spec_sub v l x ->
                           cumsum_i_spec t y ->
                           cumsum_i_spec_sub v (t::l) (y .+ x).

Program Fixpoint cumsum_i (i: Vertex') {measure (` i)}:
 { x: Val | cumsum_i_spec i x /\ forall y, cumsum_i_spec i y -> x = y } :=
  ` (value i) .+
  g_sum ((fix F (ps: list {v: Vertex' | ` v < ` i}): list Val :=
  match ps with
  | [] => []
  | p::ps' => cumsum_i (` p) :: F ps'
  end) (getparents_lt i)).
Next Obligation.
 split.
 (* spec *)
 apply cumsum_i_spec_rec with (x:=g_sum
        ((fix F (ps : list {v : Vertex' | ` v < ` i}) : list G :=
            match ps as ps0 return (ps0 = ps -> list G) with
            | nil => fun _ : [] = ps => []
            | p :: ps' =>
                fun Heq_ps : p :: ps' = ps =>
                `
                (cumsum_i (` p) (cumsum_i_obligation_1 i cumsum_i F Heq_ps))
                :: F ps'
            end eq_refl) (getparents_lt i))).
 rewrite <- getparents_lt_spec1.
 induction (getparents_lt i).
  simpl. apply cumsum_i_spec_sub_nil.
 simpl.
 destruct a as [a Ha]. simpl.
 eapply cumsum_i_spec_sub_cons with (y:=` (cumsum_i a Ha)).
  apply IHl.
 destruct (cumsum_i a Ha). simpl. destruct a0. assumption.
 (* inv *)
 intros.
 inversion_clear H.
 clear y.
 f_equal.
 rewrite <- getparents_lt_spec1 in H0.
 generalize dependent x.
 induction (getparents_lt i); intros.
  simpl. simpl in H0.
  inversion_clear H0.
  reflexivity.
 inversion_clear H0.
 destruct a as [a Ha].
 destruct (cumsum_i a Ha) as [z [Hz Hz2]].
 simpl in H1.
 rewrite <- (Hz2 _ H1).
 simpl.
 specialize (IHl x0 H).
 rewrite IHl. clear IHl.
 destruct (cumsum_i a Ha) as [? [? ?]].
 simpl.
 rewrite <- (Hz2 _ c).
 reflexivity.
Defined.

Theorem cumsum_i_spec_inv: forall (i: Vertex') (x: Val),
        cumsum_i_spec i x -> ` (cumsum_i i) = x.
Proof.
 intros.
 destruct (cumsum_i i) as [? [? ?]].
 simpl.
 apply e.
 assumption.
Qed.

Definition cumsum_i_simple (i: Vertex'): Val :=
 ` (value i) .+ Σ[E, i] (fun j => ` (cumsum_i j)).

Theorem cumsum_i_simple_spec: forall (i: Vertex'),
        ` (cumsum_i i) = cumsum_i_simple i.
Proof.
 intros.
 apply cumsum_i_spec_inv.
 unfold cumsum_i_simple.
 apply cumsum_i_spec_rec with
   (x:=Σ[E, i] (fun j => ` (cumsum_i j))).
 induction (` (getparents E i)).
  simpl. constructor.
 remember cumsum_i as F.
 simpl.
 apply cumsum_i_spec_sub_cons with
   (y := ` (F a))
   (x := g_sum (map (fun v : Vertex' => ` (F v)) l)).
  apply IHl.
 destruct (F a) as [? [? ?]].
 simpl. assumption.
Qed.

Theorem cumsum_i_simple_eq'_sub: forall (v v': Vertex'),
        Vertex'_eq v v' ->
        map (fun v => ` (cumsum_i v)) (` (getparents E v)) =
        map (fun v => ` (cumsum_i v)) (` (getparents E v')).
Proof.
 intros v.
 induction v using getparents_ind; intros v' Heqv'.
 remember cumsum_i as F.
 destruct v as [v H1]. destruct v' as [v' H2]. 
 simpl in *.
 change (fun v0=>Vertex_ok v0) with Vertex_ok in *.
 specialize (getparents_spec1 E Heqv'); intros Heqlist0.
 rewrite HeqF in H.
 rename H into Hparents0.
 refine ((fix Fix (l1 l2: list Vertex')
                  (Hparents: Forall (fun u: Vertex' => forall u': Vertex', Vertex'_eq u u' ->
                                     map (fun v => ` (cumsum_i v)) (` (getparents E u)) =
                                     map (fun v => ` (cumsum_i v)) (` (getparents E u'))) l1)
                  (Heqlist: eqlistA Vertex'_eq l1 l2)
                  {struct Heqlist} :=
   match Heqlist in eqlistA _ ll1 ll2 
                 return l1 = ll1 -> l2 = ll2 ->
                        map (fun v => ` (F v)) ll1 = map (fun v => ` (F v)) ll2 with
   | eqlistA_nil => _
   | eqlistA_cons x x' l l' HeqA Hl => _
   end refl_equal refl_equal
 ) (` (getparents E (exist _ v H1))) (` (getparents E (exist _ v' H2))) Hparents0 Heqlist0);
   clear Heqlist0; clear Hparents0; intros Heql1 Heql2.
  simpl. reflexivity.
 simpl.
 rewrite Heql1 in Hparents.
 inversion_clear Hparents.
 rewrite (Fix l l' H0 Hl). clear Fix; clear H0; clear Hl.
 clear dependent l1. clear dependent l2.
 rewrite HeqF. do 2 rewrite cumsum_i_simple_spec. clear dependent F.
 unfold cumsum_i_simple. remember cumsum_i as F.
 rewrite (value_eq' HeqA).
 f_equal. f_equal.
 rewrite (H _ HeqA).
 reflexivity.
Qed.

Theorem cumsum_i_simple_eq': forall (v v': Vertex'),
        Vertex'_eq v v' ->
        cumsum_i_simple v = cumsum_i_simple v'.
Proof.
 intros v v' Heqv'.
 unfold cumsum_i_simple.
 rewrite (value_eq' Heqv').
 rewrite (cumsum_i_simple_eq'_sub Heqv').
 reflexivity.
Qed.

Program Definition cumsum: Values :=
 let (l, Hl) := @enumto_list Val lenV (fun i Hi => cumsum_i _) in l.
Next Obligation.
 exists i; assumption.
Defined.
Next Obligation.
 destruct Hl.
 aomega.
Defined.

Definition diffs_i (i: Vertex'): Val :=
 ` (value i) .-
 g_sum (map (fun v => ` (value v)) (` (getparents E i))).

Theorem diffs_i_eq': forall v v': Vertex',
        Vertex'_eq v v' -> diffs_i v = diffs_i v'.
Proof.
 intros v v' Heqv'.
 unfold diffs_i.
 rewrite (value_eq' Heqv').
 assert (A: forall x y y', y = y' -> x .- y = x .- y').
  intros. rewrite H. reflexivity.
 apply A. clear A.
 specialize (getparents_spec1 E Heqv'); intros Heqlist.
 induction Heqlist.
  simpl. reflexivity.
 simpl.
 rewrite IHHeqlist.
 rewrite (value_eq' H).
 reflexivity.
Qed.

Theorem diffs_i_eq'_sub: forall (v v': Vertex'),
        Vertex'_eq v v' ->
        map (fun v => ` (value v)) (` (getparents E v)) =
        map (fun v => ` (value v)) (` (getparents E v')).
Proof.
 intros v v' Heqv'.
 specialize (getparents_spec1 E Heqv'); intros Heqlist0.
 induction Heqlist0.
  simpl. reflexivity.
 simpl.
 rewrite (value_eq' H).
 f_equal.
 apply IHHeqlist0.
Qed.

Program Definition diffs: Values :=
 let (l, Hl) := @enumto_list Val lenV (fun i Hi => diffs_i _) in l.
Next Obligation.
 exists i; assumption.
Defined.
Next Obligation.
 destruct Hl.
 aomega.
Defined.

Theorem cumsum_list_spec1: forall (v: Vertex') d,
        exists H: Vertex_ok (`v),
        nth (`v) (`cumsum) d =
        ` (cumsum_i (exist Vertex_ok (`v) H)).
Proof.
 intros.
 unfold cumsum.
 destruct (enumto_list _).
 destruct e.
 destruct v as [v Hv].
 unfold Vertex_ok in Hv.
 unfold proj1_sig.
 rewrite <- minus_n_O in e0.
 specialize (e0 v d Hv).
 destruct e0.
 rewrite H.
 exists x0.
 assert (A: forall A P (x: {y:A|P y}), (let(a,_):=x in a) = ` x).
  intros. unfold proj1_sig. reflexivity.
 rewrite (A _ _ (cumsum_i (exist Vertex_ok v x0))).
 do 2 rewrite cumsum_i_simple_spec.
 unfold cumsum_obligation_1.
 unfold cumsum_i_simple.
 change (0 + v) with v.
 change (fun v0 => Vertex_ok v0) with Vertex_ok.
 reflexivity.
Qed.

Theorem diffs_list_spec1: forall (v: Vertex') d,
        exists H: Vertex_ok (`v), nth (`v) (`diffs) d = diffs_i (exist Vertex_ok (`v) H).
Proof.
 intros.
 unfold diffs.
 destruct (enumto_list _).
 simpl in *.
 destruct e.
 destruct v as [v Hv]. simpl.
 unfold Vertex_ok in Hv.
 rewrite <- minus_n_O in H0.
 specialize (H0 v d Hv).
 destruct H0.
 rewrite H0.
 unfold diffs_obligation_1. simpl.
 exists x0.
 unfold Vertex_ok.
 reflexivity.
Qed.

End mainops.

End lenV.

Notation "'Σ[' F , i ] ( 'fun' j => f )" := (g_sum (map (fun j => f) (` (getparents F i))))
                          (at level 10, F at level 20, i at level 20, j ident, f at level 99, no associativity
                          ,format "Σ[ F ,  i ]  ( fun  j  =>  f )").

Definition Values_eq l (V W: Values l) := (eqlistA g_eq (` V) (` W)).
Local Notation "v @= w" := (Values_eq v w) (at level 70, no associativity).

Local Notation "v #+ e" := (@cumsum _ v e) (at level 50, left associativity).
Local Notation "v #- e" := (@diffs _ v e) (at level 50, left associativity).

Lemma Values_eq_refl: forall l (V: Values l), V @= V.
Proof. intros. unfold Values_eq. reflexivity. Qed.
Lemma Values_eq_sym: forall l (V W: Values l), V @= W -> W @= V.
Proof. intros. unfold Values_eq in *. rewrite H. reflexivity. Qed.
Lemma Values_eq_trans: forall l (V W X: Values l), V @= W -> W @= X -> V @= X.
Proof. intros. unfold Values_eq in *. rewrite H. rewrite H0. reflexivity. Qed.

Global Add Parametric Relation (l: nat): (@Values l) (@Values_eq l)
 reflexivity proved by (@Values_eq_refl l)
 symmetry proved by (@Values_eq_sym l)
 transitivity proved by (@Values_eq_trans l) as Values_eq_rel.


Section propertys.

Lemma value_spec_sig: forall l (V: Values l) (v: Vertex' l) d,
      (` (value V v)) = nth (`v) (`V) d.
Proof.
 intros.
 generalize dependent d.
 apply proj2_sig.
Qed.

Lemma Values_eq_value: forall l (V U: Values l),
      (forall (v: Vertex' l), ` (value V v) .= ` (value U v)) ->
       V @= U.
Proof.
 intros.
 destruct V as [V HV].
 destruct U as [U HU].
 unfold proj1_sig.
 generalize dependent U.
 generalize dependent l.
 induction V; intros.
  induction U.
   unfold Values_eq. simpl. reflexivity.
  pose HV as T. rewrite <- HU in T. simpl in T. inversion T.
 induction U.
  pose HV as T. rewrite <- HU in T. simpl in T. inversion T.
 clear IHU.
 assert (v0: Vertex_ok l 0).
  unfold Vertex_ok.
  simpl in HV. rewrite <- HV. auto with arith.
 pose (H (exist _ 0 v0)) as H0.
 unfold value in H0. simpl in H0.
 constructor. assumption. clear H0.
 destruct l.
  simpl in HV. inversion HV.
 simpl in HV, HU.
 pose (eq_add_S _ _ HV) as HV'.
 pose (eq_add_S _ _ HU) as HU'.
 assert (forall v: Vertex' l, ` (value (exist _ V HV') v) .= ` (value (exist _ U HU') v)).
  intros. clear IHV.
  destruct v as [v Hv].
  unfold Vertex_ok in Hv.
  assert (Hv': S v < S l) by omega.
  specialize (H (exist _ (S v) Hv')).
  pose (d := a).
  rewrite (value_spec_sig (exist _ (a::V) HV) (exist _ (S v) Hv') d) in H.
  rewrite (value_spec_sig (exist _ (a0::U) HU) (exist _ (S v) Hv') d) in H.
  simpl in H.
  rewrite (value_spec_sig (exist _ V HV') (exist _ v Hv) d).
  rewrite (value_spec_sig (exist _ U HU') (exist _ v Hv) d).
  simpl.
  assumption.
 specialize (IHV l HV' U HU' H0).
 assumption.
Qed.

Section V.
Variable l: nat.
Implicit Type V: Values l.


(* しっかりとしたrewrite Lemmaを作っておこう *)

Lemma value_cumsum_i_simple: forall (V: Values l) E v,
      ` (value (V #+ E) v) = cumsum_i_simple V E v.
Proof.
 intros.
 rewrite (value_spec_sig _ v g_id).
 destruct (cumsum_list_spec1 V E v g_id). rewrite H. clear H.
 rewrite cumsum_i_simple_spec.
 rewrite cumsum_i_simple_eq' with (v':=v);
  reflexivity.
Qed.

Lemma value_diffs_i: forall (V: Values l) E v,
      ` (value (V #- E) v) = diffs_i V E v.
Proof.
 intros.
 rewrite (value_spec_sig _ v g_id).
 destruct (diffs_list_spec1 V E v g_id). rewrite H. clear H.
 rewrite diffs_i_eq' with (v':=v);
  reflexivity.
Qed.

Lemma g_sum_map_op_distr: forall A (e: list A) (f g: A -> G),
      g_sum (map (fun x => f x .+ g x) e) .=
      g_sum (map f e) .+ g_sum (map g e).
Proof.
 intros.
 induction e.
  simpl. rewrite g_identity_r. reflexivity.
 simpl.
 repeat rewrite <- g_associative. apply g_op_morphism; [reflexivity|].
 rewrite (g_commutative (g_sum _)).
 repeat rewrite <- g_associative. apply g_op_morphism; [reflexivity|].
 rewrite (g_commutative (g_sum _)).
 apply IHe.
Qed.

Lemma g_sum_map_inv: forall A (e: list A) (f: A -> G),
      g_sum (map (fun x => .- f x) e) .=
      .- g_sum (map (fun x => f x) e).
Proof.
 intros.
 induction e.
  simpl. rewrite g_invid_id. reflexivity.
 simpl.
 rewrite g_op_inv.
 rewrite IHe.
 reflexivity.
Qed.

Lemma g_sum_map_invop_distr: forall A (e: list A) (f g: A -> G),
      g_sum (map (fun x => f x .- g x) e) .=
      g_sum (map f e) .- g_sum (map g e).
Proof.
 intros.
 rewrite g_sum_map_op_distr.
 rewrite g_sum_map_inv.
 change (fun x => g x) with g.
 reflexivity.
Qed.

Lemma g_sum_map_Forall_eq_ext: forall A (e: list A) (f g: A -> G),
      Forall (fun i => f i .= g i) e ->
      g_sum (map f e) .= g_sum (map g e).
Proof.
 intros.
 induction e.
  simpl. reflexivity.
 simpl.
 inversion_clear H.
 rewrite H0.
 rewrite (IHe H1).
 reflexivity.
Qed.

Lemma map_ext_2: forall A B C D (f: A -> list B) (g g': B -> C) (h: list C -> D),
      (forall x, g x = g' x) ->
      forall l: list A,
      map (fun x => h (map g  (f x))) l =
      map (fun x => h (map g' (f x))) l.
Proof.
 intros.
 apply map_ext.
 intros.
 f_equal.
 apply map_ext.
 assumption.
Qed.

Lemma g_map_ext: forall A (f g: A -> G),
      (forall x, f x .= g x) ->
      forall e, eqlistA g_eq (map f e) (map g e).
Proof.
 intros.
 induction e.
  simpl. constructor.
 simpl.
 constructor.
  apply H.
 assumption.
Qed.

Global Add Parametric Morphism:
 (@g_sum _ _ _ abeliangroup) with
 signature (eqlistA g_eq) ==> g_eq as g_sum_morph.
Proof.
 intros.
 induction H.
  simpl. reflexivity.
 simpl.
 rewrite IHeqlistA.
 rewrite H.
 reflexivity.
Qed.

Section concat.
Variable A: Type.
Fixpoint concat (xs: list (list A)): list A :=
 match xs with
 | [] => []
 | x::xs' => x ++ concat xs'
 end.
End concat.

Definition parentstrans E F (i: Vertex' l): list (Vertex' l) :=
 flat_map (fun j => ` (getparents F j)) (` (getparents E i)).

Definition parentstrans_comm E F :=
 forall i, PermutationA (@Vertex'_eq l)
   (parentstrans E F i) (parentstrans F E i).

Lemma g_sum_app: forall xs ys,
      g_sum (xs ++ ys) .= g_sum xs .+ g_sum ys.
Proof.
 intros.
 induction xs.
  simpl. rewrite g_identity_l. reflexivity.
 simpl.
 rewrite IHxs.
 apply g_associative.
Qed.

Lemma g_sum_PermutationA: forall A (eqA: A -> A -> Prop) (f: A -> G) xs ys,
 (forall x y, eqA x y -> f x .= f y) ->
 PermutationA eqA xs ys ->
 g_sum (map (fun i => f i) xs) .=
 g_sum (map (fun j => f j) ys).
Proof.
 intros.
 induction H0.
    simpl. reflexivity.
   simpl.
   rewrite (H _ _ H0).
   rewrite IHPermutationA.
   reflexivity.
  simpl.
  do 2 rewrite g_associative.
  rewrite (g_commutative (f y) _).
  reflexivity.
 rewrite IHPermutationA1.
 rewrite IHPermutationA2.
 reflexivity.
Qed.

Lemma g_sum_map_flat_map_g_sum_map_g_sum: forall A B (xs: list A) f (g: A -> list B),
      g_sum (map f (flat_map g xs)) .= g_sum (map (fun x => g_sum (map f (g x))) xs).
Proof.
 intros.
 induction xs.
  simpl. reflexivity.
 simpl.
 rewrite map_app.
 rewrite g_sum_app.
 rewrite IHxs.
 reflexivity.
Qed.

Theorem parentstrans_comm_f_comm:
        forall E F (f: Vertex' l -> Val)
        (Hfeq': forall x y, Vertex'_eq x y -> f x .= f y),
        parentstrans_comm E F ->
        forall i,
        g_sum (map (fun j => g_sum (map (fun k => f k) (` (getparents F j)))) (` (getparents E i))) .=
        g_sum (map (fun j => g_sum (map (fun k => f k) (` (getparents E j)))) (` (getparents F i))).
Proof.
 intros.
 specialize (H i).
 unfold parentstrans in H.
 apply g_sum_PermutationA with (f:=f) in H
  ; [|intros x y Heq'; rewrite (Hfeq' _ _ Heq'); reflexivity].
 do 2 rewrite g_sum_map_flat_map_g_sum_map_g_sum in H.
 assumption.
Qed.

Theorem g_sum_inv: forall A (xs: list A) (f: A -> G),
        g_sum (map (fun x => .- f x) xs) .=
        .- g_sum (map f xs).
Proof.
 intros.
 induction xs.
  simpl. rewrite g_invid_id. reflexivity.
 simpl.
 rewrite IHxs.
 rewrite <- g_op_inv.
 reflexivity.
Qed.

Lemma map_ext_g: forall A (f g: A -> Val)
      (Heq: forall x, f x .= g x),
      forall e, eqlistA g_eq (map f e) (map g e).
Proof.
 intros.
 induction e.
  simpl. constructor.
 simpl.
 constructor.
  apply Heq.
 assumption.
Qed.

Lemma Vertex'_eq_refl: forall (l: nat) (v: Vertex' l),
      Vertex'_eq v v.
Proof. intros. unfold Vertex'_eq. reflexivity. Qed.
Lemma Vertex'_eq_sym: forall (l: nat) (v u: Vertex' l),
      Vertex'_eq v u -> Vertex'_eq u v.
Proof. intros. unfold Vertex'_eq in *. rewrite H. reflexivity. Qed.
Lemma Vertex'_eq_trans: forall (l: nat) (v u w: Vertex' l),
      Vertex'_eq v u -> Vertex'_eq u w -> Vertex'_eq v w.
Proof. intros. unfold Vertex'_eq in *. rewrite H. rewrite H0. reflexivity. Qed.

Global Add Parametric Relation (l: nat): (Vertex' l) (@Vertex'_eq l)
 reflexivity proved by (@Vertex'_eq_refl l)
 symmetry proved by (@Vertex'_eq_sym l)
 transitivity proved by (@Vertex'_eq_trans l)
 as Vertex'_eq_rel.

Instance Equivalence_Permutation_Vertex'_eq:
        Equivalence (PermutationA (Vertex'_eq (lenV:=l))).
 apply Equivalence_instance_0.
 constructor.
  unfold Reflexive. apply (@Vertex'_eq_refl l).
  unfold Symmetric. apply (@Vertex'_eq_sym l).
  unfold Transitive. apply (@Vertex'_eq_trans l).
Defined.

Lemma parentstrans_comm_sym: forall E1 E2,
      parentstrans_comm E1 E2 ->
      parentstrans_comm E2 E1.
Proof.
 intros.
 unfold parentstrans_comm in *.
 intros. specialize (H i).
 apply Equivalence_Symmetric.
 assumption.
Qed.

Lemma parentssum_eq': forall E (v u: Vertex' l) f
      (Hf: forall v u, Vertex'_eq v u -> f v = f u)
      (Heq': Vertex'_eq v u),
      Σ[E, v](fun j => f j) = Σ[E, u](fun j => f j).
Proof.
 intros.
 specialize (getparents_spec1 E Heq'). intro H.
 induction H.
  simpl. reflexivity.
 simpl.
 rewrite (Hf x x'); [|assumption].
 rewrite IHeqlistA.
 reflexivity.
Qed.

Theorem cumsum_empty_id: forall V: Values l, V #+ [] @= V.
Proof.
 intros.
 apply Values_eq_value.
 intros.
 pose (d := g_id (G:=Val)).
 rewrite (value_spec_sig V v d).
 rewrite (value_spec_sig _ v d).
 destruct (cumsum_list_spec1 V [] v d).
 rewrite H.
 rewrite cumsum_i_simple_spec.
 unfold cumsum_i_simple.
 simpl.
 rewrite (value_spec_sig V _ d).
 simpl.
 apply (g_identity_r (nth (`v) (`V) d)).
Qed.
(* やっと！超簡単な命題が証明できた！しかし少しでも難しい命題が証明できる気がしない…！ *)
Theorem diffs_empty_id: forall V: Values l, V #- [] @= V.
Proof.
 intros.
 apply Values_eq_value.
 intros.
 pose (d := g_id (G:=Val)).
 rewrite (value_spec_sig V v d).
 rewrite (value_spec_sig _ v d).
 destruct (diffs_list_spec1 V [] v d).
 rewrite H.
 unfold diffs_i.
 simpl.
 rewrite (value_spec_sig V _ d).
 simpl.
 rewrite g_invop_identity_r.
 reflexivity.
Qed.

(* こっちにはtransの仮定がいらない！ *)
Theorem cumsum_diffs: forall (V: Values l) E, V #+ E #- E @= V.
Proof.
 intros.
 apply Values_eq_value; intros i.
 rewrite value_diffs_i.
 unfold diffs_i.
 rewrite value_cumsum_i_simple.
 rewrite map_ext with (g:=fun j=>cumsum_i_simple V E j); [|apply value_cumsum_i_simple].
 unfold cumsum_i_simple at 1.
 rewrite map_ext with (f:=fun j=> ` (cumsum_i V E j)) (g:=fun j => cumsum_i_simple V E j)
  ; [|apply cumsum_i_simple_spec].
 g_eq_auto 2.
Qed.

Theorem diffs_cumsum: forall (V: Values l) E, V #- E #+ E @= V.
Proof.
 intros.
 apply Values_eq_value; intros i.
 rewrite value_cumsum_i_simple.
 unfold cumsum_i_simple.
 rewrite value_diffs_i.
 unfold diffs_i.
 cut (g_sum (map (fun v => ` (value V v)) (` (getparents E i))) .=
      g_sum (map (fun v => ` (cumsum_i (V #- E) E v)) (` (getparents E i)))).
  intros. rewrite H. g_eq_auto 2.
 induction i using getparents_ind with (E:=E); intros.
 rewrite map_ext with (f:=fun j=>` (cumsum_i (V#-E) E j)) (g:=fun j=>cumsum_i_simple (V#-E) E j)
  ; [|apply cumsum_i_simple_spec].
 unfold cumsum_i_simple.
 rewrite g_sum_map_op_distr.
 rewrite map_ext with (f:=fun j=>` (value (V#-E) j)) (g:=fun j=>diffs_i V E j)
  ; [|apply value_diffs_i].
 unfold diffs_i.
 rewrite g_sum_map_invop_distr.
 cut (g_sum (map (fun j => g_sum (map (fun k => ` (value V k)) (` (getparents E j)))) (` (getparents E i))) .=
      g_sum (map (fun j => g_sum (map (fun k => ` (cumsum_i (V #- E) E k)) (` (getparents E j)))) (` (getparents E i)))).
  intros. rewrite H0. g_eq_auto 2.
 rewrite (g_sum_map_Forall_eq_ext _ _ H).
 reflexivity.
Qed.
(* map_extなどを活用して, なるべくgetparentsに対するlistのinductionをなくすかんじだね *)

(* Σ_E Σ_F V_k = Σ_F Σ_E V_k であることが必要. これは(E #* F = F #* E where #* = 辺の推移)であることが必要っぽい？ *)
Theorem diffs_diffs_ord: forall (V: Values l) E1 E2,
                         parentstrans_comm E1 E2 ->
                         V #- E1 #- E2 @= V #- E2 #- E1.
Proof.
 intros.
 apply Values_eq_value; intros i.
 do 2 rewrite value_diffs_i.
 unfold diffs_i.
 rewrite map_ext with (f:=(fun j=>` (value (V #- E2) j))) (g:=fun j=>diffs_i V E2 j)
  ; [|apply value_diffs_i].
 rewrite map_ext with (f:=fun j=>` (value (V #- E1) j)) (g:=fun j=>diffs_i V E1 j)
  ; [|apply value_diffs_i].
 unfold diffs_i.
 do 2 rewrite g_sum_map_invop_distr with (f:=fun j=> ` (value V j)) (g:=fun j=> g_sum _).
 do 2 rewrite value_diffs_i. unfold diffs_i.
 g_simplify.
 assert (R: forall x1 x2 x3 x4, x1 .+ (x2 .+ (x3 .+ x4)) .= x1 .+ (x3 .+ (x2 .+ x4))).
  intros. g_eq_auto 5.
 rewrite R at 1.
 repeat (apply g_op_morphism; [reflexivity|]).
 rewrite (@parentstrans_comm_f_comm E1 E2).
  reflexivity.
 intros. rewrite value_eq' with (v':=y). reflexivity.
 assumption.
 assumption.
Qed.

Theorem cumsum_diffs_ord: forall (V: Values l) E1 E2,
                          parentstrans_comm E1 E2 ->
                          V #+ E1 #- E2 @= V #- E2 #+ E1.
Proof.
 intros.
 apply Values_eq_value; intros.
 rewrite value_diffs_i. rewrite value_cumsum_i_simple.
 unfold diffs_i.
 rewrite value_cumsum_i_simple.
 unfold cumsum_i_simple at 1.
 unfold cumsum_i_simple.
 rewrite value_diffs_i.
 unfold diffs_i.
 g_simplify. apply g_op_morphism. reflexivity.
 rewrite map_ext with (f:=fun j=>` (value (V #+ E1) j)) (g:=fun j=>` (cumsum_i V E1 j))
  ; [|intros; rewrite value_cumsum_i_simple; rewrite cumsum_i_simple_spec; reflexivity].
 induction v using getparents_ind with (E:=E1).
 apply g_sum_map_Forall_eq_ext in H0.
 do 2 (rewrite map_ext with (f:=fun j=>` (cumsum_i V E1 j)) (g:=fun j=>cumsum_i_simple V E1 j)
  ; [|apply cumsum_i_simple_spec]).
 rewrite map_ext with (f:=fun j=>` (cumsum_i (V#-E2) E1 j)) (g:=fun j=>cumsum_i_simple (V#-E2) E1 j)
  ; [|apply cumsum_i_simple_spec].
 unfold cumsum_i_simple.
 repeat rewrite g_sum_map_op_distr.
 rewrite map_ext with (f:=fun j=>` (value (V#-E2) j)) (g:=fun j=>diffs_i V E2 j)
  ; [|apply value_diffs_i].
 unfold diffs_i.
 rewrite g_sum_map_invop_distr.
 rewrite g_sum_map_invop_distr in H0.
 rewrite g_sum_map_op_distr in H0.
 rewrite (@parentstrans_comm_f_comm E1 E2) in H0.
 assert (R: forall x1 x2 x3 x4, x1 .+ x2 .- (x3 .+ x4) .= .-x3 .+ (x1 .+ (x2 .- x4))).
  intros.
  g_eq_auto 2.
 rewrite R. clear R.
 repeat rewrite <- g_associative.
 repeat (apply g_op_morphism; [reflexivity|]).
 rewrite H0.
 rewrite g_sum_inv.
 reflexivity.
  intros.
  do 2 rewrite cumsum_i_simple_spec.
  rewrite cumsum_i_simple_eq' with (v':=y).
  reflexivity.
 assumption.
 assumption.
Qed.

Theorem cumsum_cumsum_ord: forall V E1 E2,
                           parentstrans_comm E1 E2 ->
                           V #+ E1 #+ E2 @= V #+ E2 #+ E1.
Proof.
 intros.
 apply Values_eq_value; intros i.
 do 2 rewrite value_cumsum_i_simple.
 unfold cumsum_i_simple.
 do 2 rewrite value_cumsum_i_simple.
 unfold cumsum_i_simple.
 repeat rewrite <- g_associative.
 apply g_op_morphism.
  reflexivity.
 induction i using getparents_ind with (E:=E1).
 apply g_sum_map_Forall_eq_ext in H0.
 do 2 rewrite g_sum_map_op_distr in H0.
 rewrite map_ext with (f:=fun j=>` (cumsum_i (V #+ E1) E2 j)) (g:=fun j=>cumsum_i_simple (V #+ E1) E2 j)
  ; [|apply cumsum_i_simple_spec].
 rewrite map_ext with (f:=fun j=>` (cumsum_i (V #+ E2) E1 j)) (g:=fun j=>cumsum_i_simple (V #+ E2) E1 j)
  ; [|apply cumsum_i_simple_spec].
 unfold cumsum_i_simple.
 do 2 rewrite g_sum_map_op_distr.
 rewrite map_ext with (f:=fun j=>` (value (V #+ E1) j)) (g:=fun j=>` (cumsum_i V E1 j))
  ; [|intros; rewrite value_cumsum_i_simple; rewrite cumsum_i_simple_spec; reflexivity].
 rewrite map_ext with (f:=fun j=>` (value (V #+ E2) j)) (g:=fun j=>` (cumsum_i V E2 j))
  ; [|intros; rewrite value_cumsum_i_simple; rewrite cumsum_i_simple_spec; reflexivity].
 do 2 (rewrite map_ext with (f:=fun j=>` (cumsum_i V E1 j)) (g:=fun j=>cumsum_i_simple V E1 j)
  ; [|apply cumsum_i_simple_spec]).
 do 2 (rewrite map_ext with (f:=fun j=>` (cumsum_i V E2 j)) (g:=fun j=>cumsum_i_simple V E2 j)
  ; [|apply cumsum_i_simple_spec]).
 unfold cumsum_i_simple.
 repeat rewrite g_sum_map_op_distr.
 repeat rewrite <- g_associative.
 assert (R1: forall x1 x2 x3 x4 x5, x1.+(x2.+(x3.+(x4.+x5))).=x1.+(x3.+(x2.+(x5.+x4)))).
  intros. g_eq_auto 3.
 assert (R2: forall x1 x2 x3 x4 x5, x1.+(x2.+(x3.+(x4.+x5))).=x3.+(x1.+((x4.+x5).+x2))).
  intros. g_eq_auto 3.
 rewrite R1. rewrite (R2 (Σ[E2, i] (fun x => ` (value V x)))). clear R1; clear R2.
 do 2 (apply g_op_morphism; [reflexivity|]).
 rewrite <- H0. clear H0.
 repeat rewrite <- g_associative.
 apply g_op_morphism. reflexivity.
 induction i using getparents_ind with (E:=E2).
 apply g_sum_map_Forall_eq_ext in H0.
 do 2 rewrite g_sum_map_op_distr in H0.
 do 2 (rewrite map_ext_2 with (g:=fun j=>` (cumsum_i (V#+E1) E2 j)) (g':=fun j=>cumsum_i_simple (V#+E1) E2 j)
  ; [|apply cumsum_i_simple_spec]).
 unfold cumsum_i_simple.
 do 2 (rewrite g_map_ext with (f:=fun j=>Σ[E2,j](fun k=>_.+_)) (g:=fun j=>Σ[E2,j](fun k=>` (value(V#+E1)k)).+Σ[E2,j](fun k=>Σ[E2,k](fun l=>` (cumsum_i(V#+E1)E2 l))))
  ; [|intros; rewrite g_sum_map_op_distr; reflexivity]).
 do 2 (rewrite g_sum_map_op_distr).
 rewrite map_ext_2 with (g:=fun j=>` (cumsum_i V E1 j)) (g':=fun j=>cumsum_i_simple V E1 j)
  ; [|apply cumsum_i_simple_spec].
 rewrite map_ext_2 with (g:=fun j=>` (cumsum_i V E2 j)) (g':=fun j=>cumsum_i_simple V E2 j)
  ; [|apply cumsum_i_simple_spec].
 unfold cumsum_i_simple.
 rewrite g_map_ext with (f:=fun j=>Σ[E1,j](fun k=>_.+_)) (g:=fun j=>Σ[E1,j](fun k=>` (value V k)).+Σ[E1,j](fun k=>Σ[E1,k](fun l=>` (cumsum_i V E1 l))))
  ; [|intros; rewrite g_sum_map_op_distr; reflexivity].
 rewrite g_map_ext with (f:=fun j=>Σ[E2,j](fun k=>_.+_)) (g:=fun j=>Σ[E2,j](fun k=>` (value V k)).+Σ[E2,j](fun k=>Σ[E2,k](fun l=>` (cumsum_i V E2 l))))
  ; [|intros; rewrite g_sum_map_op_distr; reflexivity].
 do 2 (rewrite g_sum_map_op_distr).
 do 2 (rewrite map_ext_2 with (g:=fun k=>` (value (_#+_) k)) (g':=fun k=>cumsum_i_simple V E1 k)
  ; [|apply value_cumsum_i_simple]).
 unfold cumsum_i_simple.
 do 2 (rewrite g_map_ext with (f:=fun j=>Σ[E2,j](fun k=>_.+_)) (g:=fun j=>Σ[E2,j](fun k=>` (value V k)).+Σ[E2,j](fun k=>Σ[E1,k](fun l=>` (cumsum_i V E1 l))))
  ; [|intros; rewrite g_sum_map_op_distr; reflexivity]).
 do 2 (rewrite g_sum_map_op_distr).
 repeat rewrite g_associative.
 assert (R1: forall x1 x2 x3 x4 x5, x1.+x2.+x3.+x4.+x5.=x1.+(x4.+(x5.+(x3.+x2)))).
  intros. g_eq_auto 3.
 assert (R2: forall x1 x2 x3 x4 x5, x1.+x2.+x3.+x4.+x5.=x4.+(x1.+(x2.+(x3.+x5)))).
  intros. g_eq_auto 3.
 rewrite R1. rewrite R2. clear R1; clear R2.
 apply g_op_morphism. reflexivity.
 apply g_op_morphism.
  apply parentstrans_comm_f_comm.
   intros. rewrite (@value_eq' _ _ _ _ H1). reflexivity.
   apply parentstrans_comm_sym.
   assumption.
 apply g_op_morphism.
  apply parentstrans_comm_f_comm.
  intros. rewrite parentssum_eq' with (u:=y). reflexivity.
  intros. do 2 rewrite cumsum_i_simple_spec. apply cumsum_i_simple_eq'. assumption.
  assumption.
  apply parentstrans_comm_sym. assumption.
 rewrite H0.
 rewrite parentstrans_comm_f_comm.
 reflexivity.
 intros. rewrite parentssum_eq' with (u:=y). reflexivity.
 intros. do 2 rewrite cumsum_i_simple_spec. apply cumsum_i_simple_eq'. assumption.
 assumption.
 apply parentstrans_comm_sym. assumption.
Qed.

End V.

Lemma Values_eq_value_eq': forall l (V W: Values l),
      V @= W -> forall i, ` (value V i) .= ` (value W i).
Proof.
 intros.
 do 2 (rewrite value_spec_sig with (d:=.0)).
 destruct V as [V HV]. destruct W as [W HW].
 destruct i as [i Hi].
 unfold Values_eq in H.
 simpl in *.
 generalize dependent l.
 generalize dependent i.
 induction H; intros.
  simpl in HV. subst.
  unfold Vertex_ok in Hi. exfalso. omega.
 simpl in *.
 subst. inversion HW.
 destruct i.
  assumption.
 apply IHeqlistA with (l0:=length l).
  reflexivity. assumption.
 unfold Vertex_ok in *.
 apply lt_S_n in Hi. assumption.
Qed.

Global Add Parametric Morphism (l: nat): (@cumsum l)
 with signature (@Values_eq l) ==> (@eq Edges) ==> (@Values_eq l)
 as cumsum_morph.
Proof.
 intros V W Heq E.
 apply Values_eq_value.
 intros i.
 do 2 rewrite value_cumsum_i_simple.
 do 2 rewrite <- cumsum_i_simple_spec.
 induction i using getparents_ind with (E:=E).
 apply g_sum_map_Forall_eq_ext in H.
 do 2 rewrite cumsum_i_simple_spec.
 unfold cumsum_i_simple.
 rewrite Values_eq_value_eq' with (W:=W); [|assumption].
 apply g_op_morphism.
  reflexivity.
 assumption.
Qed.

Global Add Parametric Morphism (l: nat): (@diffs l)
 with signature (@Values_eq l) ==> (@eq Edges) ==> (@Values_eq l)
 as diffs_morph.
Proof.
 intros V W Heq E.
 apply Values_eq_value.
 intros i.
 do 2 rewrite value_diffs_i.
 unfold diffs_i.
 rewrite Values_eq_value_eq'; [|apply Heq].
 apply g_op_morphism.
  reflexivity.
 induction (` (getparents E i)).
  simpl. reflexivity.
 simpl.
 do 2 rewrite g_op_inv.
 rewrite IHl0.
 rewrite Values_eq_value_eq'; [|apply Heq].
 reflexivity.
Qed.

Goal forall l E1 E2 E3 (V: Values l)
     (H12: parentstrans_comm l E1 E2)
     (H13: parentstrans_comm l E1 E3),
     V #+ E1 #+ E2 #+ E3 @= V #+ E2 #+ E3 #+ E1.
Proof.
 intros.
 rewrite cumsum_cumsum_ord with (E1:=E1) (E2:=E2).
 rewrite cumsum_cumsum_ord with (E1:=E1) (E2:=E3).
 reflexivity.
 assumption.
 assumption.
Qed.
End propertys.

Section decomposition_composition.

Definition decomposition_spec l (V W: Values l) (Xs: Values l * Values l) :=
 forall i,
 ` (value (fst Xs) i) = ` (value W i) /\
 ` (value (snd Xs) i) = ` (value V i) .- ` (value W i).

Program Definition decomposition_prg l (V W: Values l): { Xs: Values l * Values l | decomposition_spec V W Xs } :=
 (W, map (fun p => fst p .- snd p) (combine (` V) (` W))).
Next Obligation.
 rewrite map_length.
 rewrite combine_length.
 destruct V as [V HV]. destruct W as [W HW].
 simpl in *. unfold Val in *. rewrite HV. rewrite HW.
 apply Min.min_idempotent.
Defined.
Next Obligation.
 unfold decomposition_spec.
 simpl.
 split.
  reflexivity.
 intros.
 set (d := .0).
 do 3 (rewrite value_spec_sig with (d:=d)).
 destruct i as [i Hi].
 simpl.
 remember (fun p: G * G=> fst p.-snd p) as f.
 rewrite nth_indep with (d':=f(.0,.0)).
 rewrite map_nth.
 rewrite combine_nth.
 rewrite Heqf. simpl. reflexivity.
 destruct V as [V HV]. destruct W as [W HW]. simpl. unfold Val in *. rewrite HV. rewrite HW. reflexivity.
 rewrite map_length. rewrite combine_length.
 specialize (proj2_sig V); specialize (proj2_sig W). intros. unfold Val in *. rewrite H. rewrite H0.
 rewrite Min.min_idempotent. apply Hi.
Defined.

Definition composition_spec l (V W X: Values l) :=
 forall i,
 ` (value X i) = ` (value V i) .+ ` (value W i).

Program Definition composition_prg l (V W: Values l): { X: Values l | composition_spec V W X } :=
 map (fun p => fst p .+ snd p) (combine (` V) (` W)).
Next Obligation.
 rewrite map_length. rewrite combine_length.
 specialize (proj2_sig V); specialize (proj2_sig W). intros. unfold Val in *. rewrite H. rewrite H0.
 apply Min.min_idempotent.
Defined.
Next Obligation.
 unfold composition_spec.
 intros.
 set (d := .0).
 do 3 (rewrite value_spec_sig with (d:=d)).
 simpl.
 remember (fun p: G * G=> fst p.+snd p) as f.
 rewrite nth_indep with (d':=f(.0,.0)).
 rewrite map_nth.
 rewrite combine_nth.
 rewrite Heqf. simpl. reflexivity.
 specialize (proj2_sig V); specialize (proj2_sig W). intros. unfold Val in *. rewrite H. rewrite H0.
 reflexivity.
 rewrite map_length. rewrite combine_length.
 specialize (proj2_sig V); specialize (proj2_sig W). intros. unfold Val in *. rewrite H. rewrite H0.
 rewrite Min.min_idempotent. apply (proj2_sig i).
Defined.

Definition composition l (V W: Values l) := ` (composition_prg V W).
Definition decomposition l (V W: Values l) := ` (decomposition_prg V W).
Definition decomposition_fst l (V W: Values l) := fst (decomposition V W).
Definition decomposition_snd l (V W: Values l) := snd (decomposition V W).

Infix ">@<" := (@composition _) (at level 31, left associativity).
Infix "<@" := (@decomposition_fst _) (at level 31, left associativity).
Infix "@>" := (@decomposition_snd _) (at level 31, left associativity).

Lemma value_composition: forall l (V W: Values l) i,
      ` (value (V >@< W) i) = ` (value V i) .+ ` (value W i).
Proof.
 intros.
 unfold composition.
 specialize (proj2_sig (composition_prg V W)); intros.
 unfold composition_spec in H.
 rewrite H.
 reflexivity.
Qed.

Lemma value_decomposition_fst: forall l (V W: Values l) i,
      ` (value (V <@ W) i) = ` (value W i).
Proof.
 intros.
 unfold decomposition.
 specialize (proj2_sig (decomposition_prg V W)); intros.
 unfold decomposition_spec in H.
 destruct (H i).
 assumption.
Qed.

Lemma value_decomposition_snd: forall l (V W: Values l) i,
      ` (value (V @> W) i) = ` (value V i) .- ` (value W i).
Proof.
 intros.
 unfold decomposition.
 specialize (proj2_sig (decomposition_prg V W)); intros.
 unfold decomposition_spec in H.
 destruct (H i).
 assumption.
Qed.

Lemma cumsum_i_simple_unfold_2: forall l (V: Values l) E i,
      cumsum_i_simple V E i =
      ` (value V i) .+
      Σ[E, i](fun j => cumsum_i_simple V E j).
Proof.
 intros.
 unfold cumsum_i_simple at 1.
 rewrite map_ext with (g:=fun j=>cumsum_i_simple V E j).
  reflexivity.
 apply cumsum_i_simple_spec.
Qed.

Theorem composition_cumsum_distr: forall l (V W: Values l) (E: Edges),
        V >@< W #+ E @= (V #+ E) >@< (W #+ E).
Proof.
 intros.
 apply Values_eq_value.
 intros i.
 rewrite value_cumsum_i_simple.
 rewrite value_composition.
 do 2 (rewrite value_cumsum_i_simple).
 induction i using getparents_ind with (E:=E).
 apply g_sum_map_Forall_eq_ext in H.
 rewrite g_sum_map_op_distr in H.
 repeat rewrite cumsum_i_simple_unfold_2.
 rewrite value_composition.
 assert (R: forall x1 x2 x3 x4, x1.+x2.+(x3.+x4) .= x1.+(x3.+(x2.+x4))).
  intros. g_eq_auto 2.
 rewrite R. clear R.
 repeat rewrite <- g_associative.
 do 2 (apply g_op_morphism; [reflexivity|]).
 assumption.
Qed.

Theorem composition_diffs_distr: forall l (V W: Values l) (E: Edges),
        V >@< W #- E @= (V #- E) >@< (W #- E).
Proof.
 intros.
 apply Values_eq_value.
 intros i.
 rewrite value_diffs_i.
 rewrite value_composition.
 do 2 rewrite value_diffs_i.
 unfold diffs_i.
 rewrite value_composition.
 rewrite map_ext with (g:=fun j=>` (value V j) .+ ` (value W j))
  ; [|apply value_composition].
 rewrite g_sum_map_op_distr.
 rewrite g_op_inv.
 assert (R: forall x1 x2 x3 x4, x1.+x2.+(x3.+x4) .= x1.+x3.+x2.+x4)
  by (intros; g_eq_auto 2).
 rewrite R. clear R.
 repeat rewrite <- g_associative.
 reflexivity.
Qed.

Theorem decomposition_composition: forall l (V W: Values l),
        (V <@ W) >@< (V @> W) @= V.
Proof.
 intros.
 apply Values_eq_value.
 intros i.
 rewrite value_composition.
 rewrite value_decomposition_fst.
 rewrite value_decomposition_snd.
 g_eq_auto 2.
Qed.

Theorem composition_decomposition: forall l (V W: Values l),
        (V >@< W) @> V @= W.
Proof.
 intros.
 apply Values_eq_value. intros i.
 rewrite value_decomposition_snd.
 rewrite value_composition.
 g_eq_auto 2.
Qed.

Theorem composition_comm: forall l (V W: Values l),
        V >@< W @= W >@< V.
Proof.
 intros.
 apply Values_eq_value. intros i.
 do 2 rewrite value_composition.
 apply g_commutative.
Qed.

Theorem composition_assoc: forall l (V W X: Values l),
        V >@< (W >@< X) @= (V >@< W) >@< X.
Proof.
 intros.
 apply Values_eq_value. intros i.
 repeat rewrite value_composition.
 apply g_associative.
Qed.

Program Fixpoint Values_id_prg (l: nat): { V: Values l | forall i, ` (value V i) = .0 } :=
 match l with
 | O => []
 | S l' => .0 :: Values_id_prg l'
 end.
Next Obligation.
 rewrite value_spec_sig with (d:=.0).
 simpl. destruct (` i); reflexivity.
Defined.
Next Obligation.
 destruct x. subst.
 simpl. reflexivity.
Defined.
Next Obligation.
 rewrite value_spec_sig with (d:=.0).
 simpl.
 destruct i.
 simpl.
 destruct x.
  reflexivity.
 destruct (Values_id_prg l').
 simpl.
 assert (Vertex_ok l' x).
  apply lt_S_n. assumption.
 specialize (e (exist _ x H)).
 rewrite value_spec_sig with (d:=.0) in e.
 simpl in e.
 assumption.
Defined.

Definition Values_id (l: nat) := ` (Values_id_prg l).

Notation "@0" := (@Values_id _).

Theorem composition_identity_l: forall l (V: Values l),
        @0 >@< V @= V.
Proof.
 intros.
 apply Values_eq_value. intros i.
 rewrite value_composition.
 rewrite (proj2_sig (Values_id_prg l)).
 rewrite g_identity_l.
 reflexivity.
Qed.

Theorem composition_identity_r: forall l (V: Values l),
        V >@< @0 @= V.
Proof.
 intros.
 apply Values_eq_value. intros i.
 rewrite value_composition.
 rewrite (proj2_sig (Values_id_prg l)).
 rewrite g_identity_r.
 reflexivity.
Qed.

(* compositionをAbelianGroupにするだけ *)
Definition Values_inv_spec l (V W: Values l) :=
 forall i, ` (value W i) = .- ` (value V i).

Program Definition Values_inv_prg l (V: Values l): { W: Values l | Values_inv_spec V W } :=
 map g_inv (` V).
Next Obligation.
 rewrite map_length.
 rewrite (proj2_sig V).
 reflexivity.
Defined.
Next Obligation.
 unfold Values_inv_spec.
 intros i.
 do 2 rewrite value_spec_sig with (d:=.0).
 simpl.
 destruct V as [V HV].
 simpl.
 generalize dependent l.
 induction V; intros.
  simpl in HV.
  simpl. destruct i. unfold Vertex_ok in v. simpl. rewrite <- HV in v. exfalso. omega.
 simpl in *.
 destruct i as [i Hi].
 simpl in *.
 destruct i.
  reflexivity.
 destruct l.
  inversion HV.
 injection HV; intro.
 assert (Vertex_ok l i).
  unfold Vertex_ok in *.
  omega.
 specialize (IHV l H (exist _ i H0)).
 simpl in IHV.
 assumption.
Defined.

Definition Values_inv l (V: Values l) := ` (Values_inv_prg V).

Theorem value_Values_inv: forall l (V: Values l) i,
        ` (value (Values_inv V) i) = .- ` (value V i).
Proof.
 intros.
 rewrite (proj2_sig (Values_inv_prg V)).
 reflexivity.
Qed.

Theorem composition_inverse_r: forall l (V: Values l),
        V >@< Values_inv V @= @0.
Proof.
 intros.
 apply Values_eq_value. intros i.
 rewrite value_composition.
 rewrite value_Values_inv.
 rewrite (proj2_sig (Values_id_prg l)).
 apply g_inverse_r.
Qed.

Instance AbelianGroup_composition (l: nat): AbelianGroup (@composition l) (@Values_eq l) :=
 { g_equivalence := @Values_eq_rel l
 ; g_id := @Values_id l
 ; g_inv := @Values_inv l
 ; g_associative := @composition_assoc l
 ; g_identity_r := @composition_identity_r l
 ; g_inverse_r := @composition_inverse_r l
 ; g_commutative := @composition_comm l
 }.
Proof.
 intros.
 apply Values_eq_value. intros i.
 apply Values_eq_value_eq' with (i:=i) in H.
 apply Values_eq_value_eq' with (i:=i) in H0.
 do 2 rewrite value_composition.
 rewrite H. rewrite H0.
 reflexivity.
Proof.
 intros.
 apply Values_eq_value. intros i.
 apply Values_eq_value_eq' with (i:=i) in H.
 do 2 rewrite value_Values_inv.
 rewrite H.
 reflexivity.
Qed.

Global Add Parametric Morphism (l: nat): (@composition l)
 with signature (@Values_eq l) ==> (@Values_eq l) ==> (@Values_eq l) as composition_morph.
Proof. apply g_op_morph. exact (AbelianGroup_composition l). Qed.

Global Add Parametric Morphism (l: nat): (@decomposition_fst l)
 with signature (@Values_eq l) ==> (@Values_eq l) ==> (@Values_eq l) as decomposition_fst_morph.
Proof.
 intros.
 apply Values_eq_value. intros i.
 apply Values_eq_value_eq' with (i:=i) in H.
 apply Values_eq_value_eq' with (i:=i) in H0.
 do 2 rewrite value_decomposition_fst.
 assumption.
Qed.

Global Add Parametric Morphism (l: nat): (@decomposition_snd l)
 with signature (@Values_eq l) ==> (@Values_eq l) ==> (@Values_eq l) as decomposition_snd_morph.
Proof.
 intros.
 apply Values_eq_value. intros i.
 apply Values_eq_value_eq' with (i:=i) in H.
 apply Values_eq_value_eq' with (i:=i) in H0.
 do 2 rewrite value_decomposition_snd.
 rewrite H. rewrite H0.
 reflexivity.
Qed.


Lemma composition_decomposition_snd: forall l (V W D: Values l),
      (V >@< W) @> D @= (V @> D) >@< (W @> D) >@< D.
Proof.
 intros.
 apply Values_eq_value. intros i.
 do 2 rewrite value_composition.
 do 3 rewrite value_decomposition_snd.
 rewrite value_composition.
 g_eq_auto 3.
Qed.

(* 分解してdiffs取ってそれの足し算をしてそれを最後にcumsumして合成するやつ！ *)
Theorem decomposition_diffs_composition_cumsum_composition: forall l (V W D: Values l) (E F: Edges),
        V >@< W @=
        ((V <@ D #- E) >@< (W <@ D #- E) #+ E) >@<
        ((V @> D #- F) >@< (W @> D #- F) #+ F).
Proof.
 intros.
 do 2 rewrite composition_cumsum_distr.
 do 4 rewrite diffs_cumsum.
 assert (R: forall (x1 x2 x3 x4: Values l), x1 >@< x2 >@< (x3 >@< x4) @= (x1 >@< x3) >@< (x2 >@< x4)).
  intros.
  g_eq_auto_AG (@composition l) (@Values_eq l) (@AbelianGroup_composition l) 10.
 rewrite R.
 do 2 rewrite decomposition_composition.
 reflexivity.
Qed.

Goal forall l (V W D: Values l) (E1 E2 F: Edges),
        V >@< W @=
        ((V <@ D #- E1 #- E2) >@< (W <@ D #- E1 #- E2) #+ E2 #+ E1) >@<
        ((V @> D #- F) >@< (W @> D #- F) #+ F).
Proof.
 intros.
 do 3 rewrite composition_cumsum_distr.
 do 6 rewrite diffs_cumsum.
 assert (R: forall (x1 x2 x3 x4: Values l), x1 >@< x2 >@< (x3 >@< x4) @= (x1 >@< x3) >@< (x2 >@< x4)).
  intros.
  g_eq_auto_AG (@composition l) (@Values_eq l) (@AbelianGroup_composition l) 10.
 rewrite R.
 do 2 rewrite decomposition_composition.
 reflexivity.
Qed.

End decomposition_composition.

Section more.

Section implicitl.
Variable l: nat.
Implicit Type V W: Values l.

Inductive EdgeOp: Set :=
 | op_cumsum: Edges -> EdgeOp
 | op_diffs:  Edges -> EdgeOp
.

Definition EdgeOps := list EdgeOp.

Definition applyEdgeOp V (op: EdgeOp) :=
 match op with
 | op_cumsum E => V #+ E
 | op_diffs E => V #- E
 end.

Fixpoint applyEdgeOps V (ops: EdgeOps) :=
 match ops with
 | [] => V
 | op::ops' => applyEdgeOps (applyEdgeOp V op) ops'
 end.

Theorem applyEdgeOps_app: forall V ops1 ops2,
        applyEdgeOps V (ops1 ++ ops2) =
        applyEdgeOps (applyEdgeOps V ops1) ops2.
Proof.
 intros.
 generalize dependent V.
 induction ops1; intros.
  simpl. reflexivity.
 simpl.
 rewrite IHops1.
 reflexivity.
Qed.

Definition inverseEdgeOp (op: EdgeOp): EdgeOp :=
 match op with
 | op_cumsum E => op_diffs E
 | op_diffs E => op_cumsum E
 end.

Definition inverseEdgeOps (ops: EdgeOps): EdgeOps :=
 rev (map inverseEdgeOp ops).

Fixpoint applyEdgeOps_rev V (ops: EdgeOps) :=
 match ops with
 | [] => V
 | op::ops' => applyEdgeOp (applyEdgeOps_rev V ops') op
 end.

Theorem applyEdgeOps_rev_spec: forall V ops,
        applyEdgeOps V (rev ops) = applyEdgeOps_rev V ops.
Proof.
 intros.
 generalize dependent V.
 induction ops; intros.
  simpl. reflexivity.
 simpl.
 rewrite applyEdgeOps_app.
 rewrite IHops.
 simpl.
 reflexivity.
Qed.
End implicitl.

Global Add Parametric Morphism (l: nat): (@applyEdgeOp l)
 with signature (@Values_eq l) ==> eq ==> (@Values_eq l) as applyEdgeOp_morph.
Proof.
 intros.
 destruct y0; simpl;
  rewrite H; reflexivity.
Qed.

Global Add Parametric Morphism (l: nat): (@applyEdgeOps l)
 with signature (@Values_eq l) ==> eq ==> (@Values_eq l) as applyEdgeOps_morph.
Proof.
 intros.
 generalize dependent x.
 generalize dependent y.
 induction y0; intros.
  simpl. assumption.
 simpl.
 rewrite IHy0.
 reflexivity.
 rewrite H.
 reflexivity.
Qed.

Section implicitl2.
Variable l: nat.
Implicit Type V W: Values l.

Theorem EdgeOp_inverse: forall V op,
        applyEdgeOp (applyEdgeOp V op) (inverseEdgeOp op) @= V.
Proof.
 intros.
 destruct op; simpl.
  apply cumsum_diffs.
 apply diffs_cumsum.
Qed.

Theorem EdgeOps_inverse: forall V ops,
        applyEdgeOps (applyEdgeOps V ops) (inverseEdgeOps ops) @= V.
Proof.
 intros.
 generalize dependent V.
 induction ops; intros.
  simpl.
  reflexivity.
 simpl. unfold inverseEdgeOps. simpl.
 rewrite applyEdgeOps_app. simpl.
 rewrite IHops.
 apply EdgeOp_inverse.
Qed.

Definition EdgeOp_Edges (op: EdgeOp): Edges :=
 match op with
 | op_cumsum E => E
 | op_diffs E => E
 end.

Theorem EdgeOp_ord: forall V (op1 op2: EdgeOp),
        parentstrans_comm l (EdgeOp_Edges op1) (EdgeOp_Edges op2) ->
        applyEdgeOp (applyEdgeOp V op1) op2 @=
        applyEdgeOp (applyEdgeOp V op2) op1.
Proof.
 intros.
 destruct op1; destruct op2; simpl in *.
  apply (cumsum_cumsum_ord _ H).
  apply (cumsum_diffs_ord _ H).
  apply parentstrans_comm_sym in H. rewrite (cumsum_diffs_ord _ H). reflexivity.
  apply (diffs_diffs_ord _ H).
Qed.

Definition parentstrans_comm_all l ops ops' :=
 forall E F: Edges, In E (map EdgeOp_Edges ops) ->
                    In F (map EdgeOp_Edges ops') ->
                    parentstrans_comm l E F.

Lemma In_Permutation: forall A (xs ys: list A) (x: A),
      PermutationA eq xs ys ->
      In x xs -> In x ys.
Proof.
 intros.
 induction H.
  assumption.
 subst. simpl in *.
 destruct H0; auto.
 simpl in *.
 destruct H0 as [?|[?|?]]; subst; auto.
 auto.
Qed.

Lemma In_map_Permutation: forall A B (xs ys: list A) (f: A -> B) (x: B),
      PermutationA eq xs ys ->
      In x (map f xs) -> In x (map f ys).
Proof.
 intros.
 apply in_map_iff in H0.
 destruct H0 as [? [? ?]].
 apply in_map_iff.
 exists x0.
 split; [assumption|].
 apply In_Permutation with (xs:=xs); auto.
Qed.

Theorem EdgeOps_Permutation: forall V (ops ops': EdgeOps),
        parentstrans_comm_all l ops ops' ->
        PermutationA eq ops ops' ->
        applyEdgeOps V ops @= applyEdgeOps V ops'.
Proof.
 intros.
 generalize dependent V.
 induction H0; intros; simpl in *.
 (* nil *)
 reflexivity.
 (* cons *)
 rewrite H0.
 rewrite IHPermutationA.
 reflexivity.
 unfold parentstrans_comm_all in *. simpl in H.
 intros.
 apply H; auto.
 (* swap *)
 rewrite EdgeOp_ord.
 reflexivity.
 specialize (H (EdgeOp_Edges y) (EdgeOp_Edges x)).
 simpl in H.
 auto.
 (* trans *)
 rewrite IHPermutationA1.
 rewrite IHPermutationA2.
 reflexivity.
 unfold parentstrans_comm_all in *.
 intros. apply H.
 apply In_map_Permutation with (xs:=l₂). symmetry. assumption.
 assumption. assumption.
 unfold parentstrans_comm_all in *.
 intros. apply H.
 assumption.
 apply In_map_Permutation with (xs:=l₂). assumption.
 assumption.
Qed.

End implicitl2.

End more.

End cumsum_diffs.

End AbelianGroup.

Program Definition line_E (n0: nat): Edges :=
 (fix F (n m: nat) :=
  match n with
  | O => []
  | S n' => @edge m (S m) _ :: F n' (S m)
  end
 ) n0 0.
Require Import Div2.

Lemma n_plus_n_pow2_even: forall x, Even.even (x + x * x).
 intros.
 destruct (Even.even_odd_dec x).
  apply Even.even_even_plus; auto.
  apply Even.even_mult_l; auto.
 apply Even.odd_even_plus; auto.
 apply Even.odd_mult; auto.
Qed.

Program Fixpoint triangle_E (n: nat): Edges :=
 match n with
 | O => []
 | S n' => (fix F m :=
   match m with
   | O => []
   | S m' => ((if eq_nat_dec m' n' then id else if eq_nat_dec n' 0 then id else cons (@edge (div2(pred n'*n')+m') (div2(n'*n)+m') _)) ∘
             (if eq_nat_dec m' 0  then id else cons (@edge (div2(pred n'*n')+pred m') (div2(n'*n)+m') _))
             ) (F m')
   end) n ++ triangle_E n'
 end.
Next Obligation.
 clear H.
 destruct n'.
  exfalso; auto.
 clear H0.
 simpl.
 rewrite mult_comm. simpl.
 specialize (n_plus_n_pow2_even n'); intros Heven.
 rewrite (mult_comm _ (S _)). simpl.
 assert (R: (n'+(n'+(n'+n'*n'))) = ((n'+n'*n')+(n'+n'))).
  abstract ring.
 rewrite R; clear R.
 assert (Adouble: forall x, x+x=2*x) by (intros; abstract ring).
 rewrite (even_double _ Heven) at 2.
 unfold double.
 rewrite Adouble. rewrite (Adouble n').
 assert (R: 2*div2 (n'+n'*n')+2*n' = 2*(div2 (n'+n'*n')+n')) by abstract ring.
 rewrite R; clear R.
 rewrite div2_double.
 abstract omega.
Defined.
Next Obligation.
 destruct m'.
  exfalso; apply H; reflexivity.
 clear H.
 destruct n'.
  simpl. abstract omega.
 simpl.
 rewrite mult_comm. simpl.
 specialize (n_plus_n_pow2_even n'); intros Heven.
 rewrite (mult_comm _ (S _)). simpl.
 assert (R: (n'+(n'+(n'+n'*n'))) = ((n'+n'*n')+(n'+n'))).
  abstract ring.
 rewrite R; clear R.
 assert (Adouble: forall x, x+x=2*x) by (intros; abstract ring).
 rewrite (even_double _ Heven) at 2.
 unfold double.
 rewrite Adouble. rewrite (Adouble n').
 assert (R: 2*div2 (n'+n'*n')+2*n' = 2*(div2 (n'+n'*n')+n')) by abstract ring.
 rewrite R; clear R.
 rewrite div2_double.
 abstract omega.
Defined.

Eval compute in map (fun x: Edge => let (v,u,_):= x in (v,u)) (triangle_E 5).

Definition Zcumsum V E := cumsum AbelianGroup_Zplus (exist _ V refl_equal) E.
Definition Zdiffs V E := diffs AbelianGroup_Zplus (exist _ V refl_equal) E.

Fixpoint replicate A n (a: A): list A := match n with O => [] | S n' => a :: replicate n' a end.
Definition values_line_01_range (l n r: nat): list Z :=
 replicate l 0%Z ++ replicate n 1%Z ++ replicate r 0%Z.

Example values_example_line1: list Z := values_line_01_range 2 3 2.

(*Eval compute in ` (Zcumsum values_example_line1 (line_E 6)).*)
Eval compute in ` (Zdiffs values_example_line1 (line_E 6)).

Example values_example_triangle1: list Z :=
        [ 1;
         0; 0;
        0; 0; 0;
       0; 0; 0; 0;
      0; 0; 0; 0; 0;
     0; 0; 0; 0; 0; 0]%Z.
(*Eval compute in ` (Zcumsum values_example_triangle1 (triangle_E 6)).*)
Example values_example_triangle2: list Z :=
        [ 1;
         1; 1;
        1; 2; 1;
       1; 3; 3; 1;
      0; 0; 0; 0; 0]%Z.
Eval compute in ` (Zdiffs values_example_triangle2 (triangle_E 5)).
(*Eval compute in ` (Zcumsum values_example_triangle2 (triangle_E 5)).
Eval compute in ` (Zcumsum_simple values_example_triangle2 (triangle_E 5)).*)


Extraction Language Haskell.
Definition aaa := Zcumsum values_example_triangle2 (triangle_E 5).
Recursive Extraction aaa.
