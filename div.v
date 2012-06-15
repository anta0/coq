Require Import Arith Omega.

Reserved Notation "x / y == z" (at level 40).
Inductive Div: nat -> nat -> nat -> Prop :=
 | Div0:  forall y,      y <> 0   -> Div 0 y 0
 | DivSz: forall x y z, Div x y z -> Div (x+y)   y (S z)
 | DivSy: forall x y z, Div x y z -> Div (x+z)(S y)   z
where "x / y == z" := (Div x y z).
Hint Constructors Div.
Theorem DivSzE: forall y x z x',
        x / y == z -> x' = (x+y) -> x' / y == S z.
Proof. intros. rewrite H0; auto. Qed.
Theorem DivSyE: forall y x z x',
        x / y == z -> x' = (x+z) -> x' / (S y) == z.
Proof. intros. rewrite H0; auto. Qed.
Hint Resolve DivSzE DivSyE.
Theorem Div0': forall y,
        0 / (S y) == 0.
Proof. intros y. apply Div0. auto. Qed.
Hint Resolve Div0'.
Theorem Div_xx1: forall x,
        x <> 0 -> x / x == 1.
Proof.
 intros x H.
 destruct x.
  elim H. reflexivity.
  eapply DivSzE. apply Div0.
  intros C. inversion C.
  simpl. reflexivity.
Qed.
Theorem Div_xx1': forall x,
        S x / S x == 1.
Proof.
 intros x.
 apply Div_xx1.
 auto.
Qed.
Hint Resolve Div_xx1 Div_xx1'.
Theorem Div_x0z: forall x z,
        x / 0 == z -> False.
Proof.
 intros x z C.
 generalize (refl_equal 0).
 refine (
 match C in Div x y z
   return y = 0 -> False with
 | Div0 y' Hy' => _
 | DivSz x' y' z' HC => _
 | DivSy x' y' z' HC => _
 end); intros Hy.
  exact (Hy' Hy).
 induction HC.
  exact (H Hy). apply IHHC; exact Hy. inversion Hy.
  inversion Hy.
Qed.
Hint Resolve Div_x0z.
Theorem Div0_a: forall y z,
        0 / y == z -> z = 0.
Proof.
 intros.
 inversion H; subst.
  reflexivity.
  destruct (plus_is_O _ _ H0) as [Hx0 Hy0]. subst.
  exact (False_ind _ (Div_x0z _ _ H1)).
 destruct (plus_is_O _ _ H0) as [Hx0 Hy0]. subst.
 reflexivity.
Qed.
Hint Resolve Div0_a.
Theorem Div_le: forall x y z,
        x / y == z -> z <= x.
Proof.
 intros.
 destruct y. exact (False_ind _ (Div_x0z x z H)).
 induction H.
  omega.
  
  destruct y0. exact (False_ind _ (Div_x0z _ _ H)).
  rewrite plus_comm. simpl. apply le_n_S.
  rewrite plus_comm. apply le_plus_trans. auto.
  
  rewrite plus_comm. apply le_plus_trans. omega.
Qed.
Hint Resolve Div_le.
Theorem Div_xyx_a: forall x y,
        x <> 0 -> x / y == x -> y = 1.
Proof.
 intros x y Hx H.
 destruct y.
  exact (False_ind _ (Div_x0z x x H)).
 destruct y. reflexivity.
 apply False_ind.
 destruct x. apply Hx. reflexivity.
 clear Hx.
 inversion H.
  rewrite plus_comm in H1. inversion H1.
  subst. simpl in H1. clear H1.
  rewrite plus_comm in H0. inversion H0. clear H0. subst.
  apply Div_le in H. apply Div_le in H3.
  omega.
 assert (x0 = 0) by omega. clear H3. subst.
 rewrite plus_0_l in H0, H2. subst.
 apply Div0_a in H2. inversion H2.
Qed.
Hint Resolve Div_xyx_a.
Theorem S_O: forall n, S n <> 0. Proof. auto. Qed.
Hint Resolve S_O.
Theorem Div_xyx_a': forall x y,
        S x / y == S x -> y = 1.
Proof. eauto. Qed.
Hint Resolve Div_xyx_a'.

Theorem Div_xy0_a: forall x y,
        x / y == 0 -> x = 0.
Proof.
 intros x y H.
 inversion H; subst.
  reflexivity.
  rewrite plus_0_r in H.
  subst.
  destruct x0. reflexivity.
  apply False_ind.
  clear H.
  induction y0. eauto.
  apply IHy0. inversion H0; subst.
  rewrite plus_0_r in H. subst.
  rewrite plus_0_r. exact H2.
Qed.

Theorem Div_x0z_a: forall x y z,
        x / y == z -> y <> 0.
Proof.
 intros.
 destruct y.
  eauto.
 omega.
Qed.
Hint Resolve Div_x0z_a.

Theorem Div_mult: forall y n,
        y <> 0 -> (n*y) / y == n.
Proof.
 intros.
 induction n as [|n'].
  simpl. constructor. exact H.
 simpl. rewrite plus_comm. constructor. exact IHn'.
Qed.
Hint Resolve Div_mult.

Theorem Div_mult_a: forall x y z,
        x / y == z -> x = z*y.
Proof.
 intros.
 induction H.
  reflexivity.
  simpl. omega.
  rewrite IHDiv. ring.
Qed.
Hint Resolve Div_mult_a.

Theorem Div_multE: forall x y z,
        y <> 0 -> x = (z*y) -> x / y == z.
Proof.
 intros.
 rewrite H0.
 eauto.
Qed.
Hint Resolve Div_multE.

Theorem Div_xy1_a: forall x y,
        x / y == 1 -> x = y.
Proof.
 intros x y H.
 specialize (Div_mult_a _ _ _ H). intros Hx.
 rewrite Hx. omega.
Qed. (* 想像以上に証明が短くなった！ *)
Hint Resolve Div_xy1_a.

Example Div_ex1: 12 / 6 == 2.
Proof.
 eauto.
Qed.
Example Div_ex2: ~ 12 / 5 == 2.
Proof.
 intros C.
 specialize (Div_mult_a _ _ _ C).
 intros C2. omega.
Qed.

Theorem Div_inv: forall x y z w a,
        x / y == z -> z / w == a -> x / (y*w) == a.
Proof.
 intros.
 specialize (Div_mult_a _ _ _ H).
 specialize (Div_mult_a _ _ _ H0).
 intros. subst.
 replace (a*w*y) with (a*(y*w)).
 apply Div_mult.
 destruct y. apply False_ind. eauto.
 destruct w. apply False_ind. eauto.
 simpl. auto.
 ring.
Qed.
Hint Resolve Div_inv.

Theorem Div_lt: forall x y z,
        x < y /\ x <> 0 -> x / y == z -> False.
Proof.
 intros.
 destruct H as [Hlt Hneq].
 specialize (Div_mult_a _ _ _ H0). intros Hmult.
 clear H0. subst.
 destruct y.
  auto.
 destruct z.
  simpl in Hneq. omega.
 induction z as [|z'].
  simpl in Hlt. omega.
 apply IHz'. simpl. simpl in Hlt. omega.
 simpl. auto.
Qed.
Hint Resolve Div_lt.

Require Program.
Program Fixpoint div_sig (x y: nat) (Hy: y <> 0) {measure x}:
                 {n: option nat |
                  match n with
                  | None   => ~ exists z, x / y == z
                  | Some z =>             x / y == z
                  end} :=
 match y with
 | O => None
 | S y' =>
   match x with
   | O => Some 0
   | S _ =>
     match le_gt_dec x y with
     | left Hle =>
       match eq_nat_dec x y with
       | left Heq => Some 1
       | right Hneq => None
       end
     | right Hgt =>
       match div_sig (x-y) y Hy with
       | None => None
       | Some z => Some (S z)
       end
     end
   end
 end.
Next Obligation.
Proof.
 rewrite Heq. apply Div_xx1'.
Qed.
Next Obligation.
Proof.
 intros Cex. destruct Cex as [z Cex].
 rename wildcard' into w.
 assert (S w < S y'). omega.
 exact (Div_lt _ _ z (conj H (S_O _)) Cex).
Qed.
Next Obligation.
Proof.
 simpl. omega.
Qed.
Next Obligation.
Proof.
 intros Cex. destruct Cex as [z Cex].
 rename wildcard' into w.
 assert (Hltw: S w - S y' < S w).
  omega.
 remember (proj1_sig (
                   (div_sig (S w - S y') (S y') Hy
                      (div_sig_func_obligation_5 (S w) (S y') Hy
                         div_sig y' eq_refl w eq_refl Hgt Heq_anonymous))
 )) as d. destruct d.
 inversion Heq_anonymous0.
 remember (proj2_sig (
         (div_sig (S w - S y') (S y') Hy
            (div_sig_func_obligation_5 (S w) (S y') Hy div_sig y'
               eq_refl w eq_refl Hgt Heq_anonymous))
 )) as d2. clear Heqd2. rewrite <- Heqd in d2. (* やっとなんか出た！ *)
 clear Heqd. clear Heq_anonymous0.
 unfold gt in Hgt. unfold lt in Hgt.
 apply d2. clear d2. clear Heq_anonymous.
 apply le_Sn_le in Hgt. rename Hgt into Hle.
 specialize (le_plus_minus _ _ Hle). intros Rpm.
 rewrite Rpm in Cex.
 specialize (Div_mult_a _ _ _ Cex). intros Hexm.
 Lemma Div_mult_minus_ex: (forall y' w z, y' <= w -> (y' + (w - y')) / y' == z -> y' + (w - y') = z * y' -> exists z', w - y' = z' * y').
  intros y' w z Hle Cex Hexm.
  rewrite plus_comm in Hexm.
  destruct Cex.
   simpl in Hexm. destruct y. apply False_ind. auto.
    apply False_ind. omega.
   exists z. simpl in Hexm.
   destruct y. apply False_ind. eauto.
   simpl. omega.
  rewrite plus_comm in Hexm.
  rewrite (le_plus_minus_r _ _ Hle) in Hexm.
  destruct z.
   rewrite mult_0_l in Hexm.
   destruct w. apply False_ind. omega.
   inversion Hexm.
  exists z. simpl in Hexm. omega.
 Qed.
 specialize ( Div_mult_minus_ex (S y') (S w) z Hle Cex Hexm). intros H.
 destruct H as [z' H].
 rewrite H.
 exists z'.
 apply Div_mult. auto.
Qed. (* やったあ！ *)
Next Obligation.
Proof.
 (* さて最後だ *)
 rename wildcard' into w.
 remember (proj2_sig (
         (div_sig (S w - S y') (S y') Hy
                      (div_sig_func_obligation_5 (S w) (S y') Hy
                         div_sig y' eq_refl w eq_refl Hgt Heq_anonymous))
 )) as HDiv. clear HeqHDiv. rewrite <- Heq_anonymous0 in HDiv.
 clear Heq_anonymous0. clear Heq_anonymous. clear Hy.
 unfold gt, lt in Hgt. apply le_Sn_le in Hgt. rename Hgt into Hle.
 rewrite (le_plus_minus _ _ Hle).
 rewrite plus_comm. constructor. exact HDiv.
Qed.
(* やったあ！ *)
Definition div x y (Hy:y <> 0): option nat := proj1_sig (div_sig x y Hy).
Hint Unfold div.
Theorem div_Div: forall x y Hy z,
        div x y Hy = Some z -> x / y == z.
Proof.
 intros.
 unfold div in H.
 specialize (proj2_sig (div_sig x y Hy)). intros p.
 simpl in p. (* 結構時間がかかる(Qed.の時にも) *)
 rewrite H in p.
 exact p.
Qed.
Hint Resolve div_Div.
Theorem div_Div': forall x y z,
        div x (S y) (S_O y) = Some z -> x / S y == z.
Proof.
 eauto.
Qed.
Hint Resolve div_Div'.
Lemma plus_reg_r: forall n m p,
      n + p = m + p -> n = m.
Proof.
 intros.
 omega.
Qed.
Theorem DivSz_a: forall x y z,
        Div (x+y) y (S z) -> Div x y z.
Proof.
 intros.
 destruct y. apply False_ind. eauto.
 apply Div_multE. omega.
 apply Div_mult_a in H.
 rewrite mult_succ_l in H.
 apply plus_reg_r in H.
 exact H.
Qed.
Hint Resolve DivSz_a.
Theorem DivSy_a: forall x y z,
        y <> 0 -> Div (x+z) (S y) z -> Div x y z.
Proof.
 intros.
 destruct y. apply False_ind. eauto. clear H.
 apply Div_multE. omega.
 apply Div_mult_a in H0.
 rewrite mult_succ_r in H0.
 apply plus_reg_r in H0.
 exact H0.
Qed.
Hint Resolve DivSy_a.
Theorem Div_xyz_xyz'_a: forall x y z z',
        x / y == z -> x / y == z' -> z = z'.
Proof.
 intros.
 destruct y. apply False_ind. eauto.
 generalize dependent z'.
 induction H; intros.
  apply Div0_a in H0. subst. reflexivity.
  inversion H0; subst.
   symmetry in H1. destruct (plus_is_O _ _  H1). subst. omega.
   assert (x0 = x) by omega. subst. clear H1.
   f_equal. apply IHDiv. exact H2.
   destruct z'.
    apply Div_xy0_a in H0. omega.
   f_equal. apply IHDiv.
   apply DivSz_a in H0. exact H0.
 inversion H0; subst.
  symmetry in H1. destruct (plus_is_O _ _ H1). subst. auto.
  apply Div_mult_a in H. subst.
  apply Div_mult_a in H0.
  rewrite H0 in H1.
  clear H1. clear H2.
  destruct y0.
   rewrite mult_0_r in H0. rewrite mult_1_r in H0. simpl in H0.
   inversion H0. subst. reflexivity.
  rewrite <- mult_succ_r in H0.
  Lemma mult_reg: (forall n m p, n * S p = m * S p -> n = m).
   intros.
   generalize dependent m.
   induction n; intros.
    induction m.
     reflexivity.
    simpl in H. inversion H.
   induction m.
    simpl in H. inversion H.
   f_equal. apply IHn.
   rewrite mult_succ_l in H. rewrite mult_succ_l in H.
   apply plus_reg_r in H. exact H.
  Qed.
  Hint Resolve mult_reg.
  apply mult_reg in H0. exact H0.
 apply Div_mult_a in H. subst.
 apply Div_mult_a in H0.
 rewrite <- mult_succ_r in H0.
 apply mult_reg in H0. subst.
 reflexivity.
Qed.
Hint Resolve Div_xyz_xyz'_a.

Theorem div_NotDiv: forall x y Hy z,
        div x y Hy <> Some z -> ~ x / y == z.
 intros.
 intro. apply H.
 specialize (proj2_sig (div_sig x y Hy)). intros p.
 simpl in p.
 change (proj1_sig (div_sig x y Hy)) with (div x y Hy) in p.
 destruct (div x y Hy).
  rewrite (Div_xyz_xyz'_a _ _ _ _ H0 p). reflexivity.
 apply False_ind. apply p. eauto.
Qed.
Hint Resolve div_NotDiv.
Theorem div_NotDiv': forall x y z,
        div x (S y) (S_O y) <> Some z -> ~ x / S y == z.
Proof. eauto. Qed.
Hint Resolve div_NotDiv'.

Example divDiv_ex1: 18 / 6 == 3.
Proof.
 apply div_Div'.
 unfold div.
(*
 simplしたらメモリ食いつぶして帰ってこないｗｗｗｗ
 でもcbvなら大丈夫。何故？ バグか？
*)
 cbv.
 reflexivity.
Qed.
Example divDiv_ex2: 153 / 9 == 17.
Proof. auto. Qed.
Example divDiv_ex3: ~ 12 / 6 == 3.
Proof.
 apply div_NotDiv'.
 cbv. intro. inversion H.
Qed.
