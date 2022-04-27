Require Import Coq.QArith.QArith.
Require Import Coq.QArith.QOrderedType.
Require Import Coq.QArith.Qminmax.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qround.
Require Import Coq.Lists.Streams.
Require Import Coq.Logic.ChoiceFacts.
Require Import Coq.Logic.ConstructiveEpsilon.
Require Import Coq.Bool.Sumbool.
Global Close Scope Q_scope.
Local Close Scope nat_scope.

Definition set (A : Type) : Type := A -> Prop.

Declare Scope set_scope.
Delimit Scope set_scope with set.
Local Open Scope set_scope.

Definition is_element_of {A : Type} (x : A) (s : set A) := s x.
Infix "∈" := is_element_of (at level 70, no associativity) : set_scope.

Record Qinterval : Set := make_Qinterval {
  min : Q;
  max : Q;
}.

Definition QIcontents (rs : Qinterval) : set Q :=
  fun q => (min rs <= q <= max rs)%Q.

Declare Scope QI_scope.
Delimit Scope QI_scope with QI.
Bind Scope QI_scope with Qinterval.
Local Open Scope QI_scope.
Notation "[ a , b ]Q" := (make_Qinterval a b) (at level 0, format "[ a ,  b ]Q") : QI_scope.
Notation "s .[ k ]" := (Str_nth k s) (at level 2, left associativity, format "s .[ k ]") : QI_scope.

Coercion QIcontents : Qinterval >-> set.

Definition QIeq rs ss := (min rs == min ss /\ max rs == max ss)%Q.
Infix "==" := QIeq : QI_scope.

Lemma QIeq_refl : forall rs, (rs == rs)%QI.
Proof.
  intros.
  split; apply Qeq_refl.
Qed.

Lemma QIeq_sym : forall rs ss, (rs == ss -> ss == rs)%QI.
Proof.
  unfold QIeq.
  intros.
  split; apply Qeq_sym; tauto.
Qed.

Lemma QIeq_trans : forall rs ss ts, (rs == ss -> ss == ts -> rs == ts)%QI.
Proof.
  unfold QIeq.
  intros.
  split; [apply (Qeq_trans _ (min ss))|apply (Qeq_trans _ (max ss))]; tauto.
Qed.

Add Relation Qinterval QIeq
  reflexivity proved by QIeq_refl
  symmetry proved by QIeq_sym
  transitivity proved by QIeq_trans
  as QIeq_rel.

Add Morphism QIcontents with signature (QIeq ==> Qeq ==> iff) as QIcontents_mor.
Proof.
  intros i1 i2 [Hi1 Hi2] r1 r2 Hr.
  unfold QIcontents.
  rewrite Hi1, Hi2, Hr.
  reflexivity.
Qed.

Add Morphism (@is_element_of Q) with signature (Qeq ==> (Qeq ==> iff) ==> iff) as is_element_of_mor_Q.
Proof.
  firstorder.
Qed.

Definition width (xs : Qinterval) : Q :=
  max xs - min xs.

Definition nonempty (xs : Qinterval) : Prop :=
  (min xs <= max xs)%Q.

Lemma nonempty_min_max : forall xs, nonempty xs -> min xs ∈ xs /\ max xs ∈ xs.
Proof.
  intros xs H.
  repeat split; trivial; q_order.
Qed.

CoFixpoint make_Stream' {A : Type} (f : nat -> A) (k : nat) : Stream A :=
  Cons (f k) (make_Stream' f (S k)).

Definition make_Stream {A : Type} (f : nat -> A) : Stream A :=
  make_Stream' f 0.

Lemma make_Stream_spec : forall A (f : nat -> A) k, (make_Stream f).[k] = f k.
Proof.
  intros A f k.
  assert (forall n, (make_Stream' f n).[k] = f (n + k)%nat) as H; [|apply H].
  unfold Str_nth.
  induction k as [|k IH]; intro n; cbn; auto.
  rewrite IH, Nat.add_succ_r; trivial.
Qed.

CoFixpoint make_Stream_rect' {A : Type} (x0 : A) (f : nat -> A -> A) (k : nat) : Stream A :=
  Cons x0 (make_Stream_rect' (f k x0) f (S k)).

Definition make_Stream_rect {A : Type} (x0 : A) (f : nat -> A -> A) : Stream A :=
  make_Stream_rect' x0 f 0.

Lemma make_Stream_rect_spec1 :
  forall A (x0 : A) f, (make_Stream_rect x0 f).[0] = x0.
Proof.
  trivial.
Qed.

Lemma make_Stream_rect_spec2 :
  forall A (x0 : A) f k, (make_Stream_rect x0 f).[S k] = f k (make_Stream_rect x0 f).[k].
Proof.
  intros A x0 f k.
  revert x0.
  assert (forall n x0, (make_Stream_rect' x0 f n).[S k] = f (n + k)%nat (make_Stream_rect' x0 f n).[k]) as H; [|apply H].
  unfold Str_nth.
  induction k as [|k IH]; intros n x0; cbn; [f_equal; auto|].
  specialize (IH (S n)).
  cbn in IH.
  rewrite IH.
  f_equal; auto.
Qed.

Definition nested (x : Stream Qinterval) :=
  forall k1 k2, (k2 >= k1)%nat -> min x.[k2] ∈ x.[k1] /\ max x.[k2] ∈ x.[k1].

Definition convergent (x : Stream Qinterval) :=
  (forall eps, eps > 0 -> exists k, width x.[k] < eps)%Q.

Record R : Set := make_R {
  bounds : Stream Qinterval;
  bounds_nested : nested bounds;
  bounds_convergent : convergent bounds;
}.

Declare Scope R_scope.
Delimit Scope R_scope with R.
Bind Scope R_scope with R.
Local Open Scope R_scope.

Coercion bounds : R >-> Stream.

Lemma bounds_consistent : forall (x : R) k1 k2, (min x.[k1] <= max x.[k2])%Q.
Proof.
  intros x k1 k2.
  destruct (Nat.le_ge_cases k1 k2) as [H|H];
    apply (bounds_nested x) in H;
    unfold is_element_of, QIcontents in H;
    tauto.
Qed.

Lemma bounds_nonempty : forall (x : R) k, nonempty x.[k].
  intros x k.
  apply bounds_nested, Peano.le_n.
Qed.

Lemma bounds_min_elem : forall (x : R) k, min x.[k] ∈ x.[k].
Proof.
  intros x k.
  apply bounds_nested, Peano.le_n.
Qed.

Lemma bounds_max_elem : forall (x : R) k, max x.[k] ∈ x.[k].
Proof.
  intros x k.
  apply bounds_nested, Peano.le_n.
Qed.

Lemma bounds_nested_elem : forall (x : R) k1 k2 r, (k2 >= k1)%nat -> r ∈ x.[k2] -> r ∈ x.[k1].
Proof.
  intros x k1 k2 r Hk [H1 H2].
  destruct (bounds_nested x k1 k2 Hk) as [[H3 _] [_ H4]].
  split; q_order.
Qed.

Lemma bounds_width_decr : forall (x : R) k1 k2, (k2 >= k1)%nat -> (width x.[k2] <= width x.[k1])%Q.
Proof.
  intros x k1 k2 Hk.
  apply Qplus_le_compat.
  - apply bounds_nested, Hk.
  - apply Qopp_le_compat, bounds_nested, Hk.
Qed.

Lemma bounds_width_lt : forall (x : R) k1 k2 eps, (k2 >= k1)%nat -> (width x.[k1] < eps -> width x.[k2] < eps)%Q.
Proof.
  intros x k1 k2 eps Hk H.
  apply (Qle_lt_trans _ (width x.[k1])); trivial.
  apply bounds_width_decr; trivial.
Qed.

Lemma bounds_width_nonneg : forall (x : R) k, (width x.[k] >= 0)%Q.
Proof.
  intros x k.
  apply -> Qle_minus_iff.
  apply bounds_nonempty.
Qed.

Definition QIlt (rs ss : Qinterval) := (max rs < min ss)%Q.

Infix "<" := QIlt : QI_scope.
Notation "x > y" := (QIlt y x) (only parsing) : QI_scope.

Definition lt (x y : R) :=
  exists k, (x.[k] < y.[k])%QI.

Infix "<" := lt : R_scope.
Notation "x > y" := (lt y x) (only parsing) : R_scope.

Lemma lt_from_bounds : forall (x y : R) k1 k2, (max x.[k1] < min y.[k2])%Q -> x < y.
Proof.
  intros x y k1 k2 H.
  set (k := Nat.max k1 k2).
  exists k.
  eapply Qle_lt_trans, Qlt_le_trans; [|exact H|]; apply bounds_nested.
  - apply Nat.le_max_l.
  - apply Nat.le_max_r.
Defined.

Lemma lt_common_witness : forall a b c d, a < b -> c < d -> exists k, (a.[k] < b.[k] /\ c.[k] < d.[k])%QI.
Proof.
  intros a b c d [k1 H1] [k2 H2].
  set (k3 := Nat.max k1 k2).
  exists k3.
  split;
    [apply (Qle_lt_trans _ (max a.[k1])), (Qlt_le_trans _ (min b.[k1]))
    |apply (Qle_lt_trans _ (max c.[k2])), (Qlt_le_trans _ (min d.[k2]))];
  trivial;
  apply bounds_nested;
  (apply Nat.le_max_l || apply Nat.le_max_r).
Defined.

Theorem lt_trans : forall x y z, x < y -> y < z -> x < z.
Proof.
  intros x y z H1 H2.
  destruct (lt_common_witness x y y z H1 H2) as [k [H3 H4]].
  exists k.
  apply (Qlt_trans _ (min y.[k])), (Qle_lt_trans _ (max y.[k])); trivial.
  apply bounds_consistent.
Defined.

Theorem lt_irrefl : forall x, ~ x < x.
Proof.
  intros x [k H].
  apply Qlt_not_le in H.
  apply H, bounds_nonempty.
Qed.

Theorem lt_not_gt : forall x y, x < y -> ~ x > y.
Proof.
  intros x y H1 H2.
  apply (lt_irrefl x), (lt_trans _ y); trivial.
Qed.

Lemma lt_gap :
  forall x y, x < y -> exists k eps, (eps > 0)%Q /\
    forall n r s, (n >= k)%nat -> r ∈ x.[n] -> s ∈ y.[n] -> (s - r >= eps)%Q.
Proof.
  intros x y [k Hk].
  exists k, (min y.[k] - max x.[k])%Q.
  split; [apply (Qlt_minus_iff (max x.[k])), Hk|].
  intros n r s Hn Hr Hs.
  apply (bounds_nested_elem _ k) in Hr, Hs; trivial.
  destruct Hr as [_ Hr], Hs as [Hs _].
  apply Qplus_le_compat; trivial.
  apply Qopp_le_compat; trivial.
Defined.

Theorem lt_or : forall x y z, x < y -> z < y \/ z > x.
Proof.
  intros x y z H.
  apply lt_gap in H.
  destruct H as [k1 [eps [Heps H]]].
  destruct (bounds_convergent z eps Heps) as [k2 Hk2].
  set (k3 := Nat.max k1 k2).
  apply (bounds_width_lt _ _ k3) in Hk2; [|apply Nat.le_max_r].
  destruct (Qlt_le_dec (max x.[k3]) (min z.[k3])) as [HC|HC].
  - right. exists k3. trivial.
  - left. exists k3.
    apply (Qplus_lt_l _ _ (- min z.[k3])).
    apply (Qlt_le_trans _ eps), (Qle_trans _ (min y.[k3] - max x.[k3])); trivial.
    + apply (H k3).
      * apply Nat.le_max_l.
      * apply bounds_max_elem.
      * apply bounds_min_elem.
    + apply Qplus_le_r, Qopp_le_compat, HC.
Defined.

Definition apart x y := x < y \/ x > y.
Infix "=/=" := apart (no associativity, at level 70) : R_scope.

Definition eqv x y := ~ x =/= y.
Infix "==" := eqv : R_scope.

Definition atm x y := ~ x > y.
Infix "<=" := atm : R_scope.
Notation "x >= y" := (atm y x) (only parsing) : R_scope.

Theorem atm_refl : forall x, x <= x.
Proof.
  exact lt_irrefl.
Qed.

Theorem apart_irrefl : forall x, ~ x =/= x.
Proof.
  intros x [H|H]; apply lt_irrefl in H; trivial.
Qed.

Theorem eqv_refl : forall x, x == x.
Proof.
  exact apart_irrefl.
Qed.

Theorem apart_sym : forall x y, x =/= y -> y =/= x.
Proof.
  intros x y [H|H]; [right|left]; exact H.
Defined.

Theorem apart_sym_iff : forall x y, x =/= y <-> y =/= x.
Proof.
  intros. split; apply apart_sym; assumption.
Defined.

Theorem eqv_sym : forall x y, x == y -> y == x.
Proof.
  intros x y H HN.
  apply apart_sym in HN.
  apply H, HN.
Qed.

Theorem lt_apart : forall x y, x < y -> x =/= y.
Proof.
  intros x y H.
  left; exact H.
Defined.

Theorem gt_apart : forall x y, x > y -> x =/= y.
Proof.
  intros x y H.
  right; exact H.
Defined.

Theorem lt_atm : forall x y, x < y -> x <= y.
Proof.
  exact lt_not_gt.
Qed.

Theorem eqv_atm : forall x y, x == y -> x <= y.
Proof.
  intros x y H HN.
  apply gt_apart in HN.
  apply H, HN.
Qed.

Theorem eqv_atl : forall x y, x == y -> x >= y.
Proof.
  intros x y H HN.
  apply lt_apart in HN.
  apply H, HN.
Qed.

Theorem atm_atl_eqv : forall x y, x <= y -> x >= y -> x == y.
Proof.
  intros x y H1 H2 [HN|HN].
  - apply H2, HN.
  - apply H1, HN.
Qed.

Theorem atm_atl_iff_eqv : forall x y, x <= y /\ x >= y <-> x == y.
Proof.
  intros x y.
  split.
  - intros [H1 H2].
    apply atm_atl_eqv; trivial.
  - intro H.
    split.
    + apply eqv_atm, H.
    + apply eqv_atl, H.
Qed.

Theorem atm_apart_lt : forall x y, x <= y -> x =/= y -> x < y.
Proof.
  intros x y H1 [H2|H2].
  - exact H2.
  - contradict H2.
    exact H1.
Defined.

Theorem atm_apart_iff_lt : forall x y, x <= y /\ x =/= y <-> x < y.
Proof.
  intros x y.
  split.
  - intros [H1 H2].
    apply atm_apart_lt; trivial.
  - intro H.
    split.
    + apply lt_atm, H.
    + apply lt_apart, H.
Defined.

Theorem atl_apart_gt : forall x y, x >= y -> x =/= y -> x > y.
Proof.
  intros x y H1 [H2|H2].
  - contradict H2.
    exact H1.
  - exact H2.
Defined.

Theorem atl_apart_iff_gt : forall x y, x >= y /\ x =/= y <-> x > y.
Proof.
  intros x y.
  split.
  - intros [H1 H2].
    apply atl_apart_gt; trivial.
  - intro H.
    split.
    + apply lt_atm, H.
    + apply gt_apart, H.
Defined.

Theorem atm_trans : forall x y z, x <= y -> y <= z -> x <= z.
Proof.
  intros x y z H1 H2 HN.
  apply (lt_or _ _ y) in HN.
  destruct HN as [HN|HN].
  - apply H1, HN.
  - apply H2, HN.
Qed.

Theorem lt_atm_trans : forall x y z, x < y -> y <= z -> x < z.
Proof.
  intros x y z H1 H2.
  apply (lt_or _ _ z) in H1.
  destruct H1 as [H1|H1].
  - contradict H1.
    exact H2.
  - exact H1.
Defined.

Theorem atm_lt_trans : forall x y z, x <= y -> y < z -> x < z.
Proof.
  intros x y z H1 H2.
  apply (lt_or _ _ x) in H2.
  destruct H2 as [H2|H2].
  - exact H2.
  - contradict H2.
    exact H1.
Defined.

Theorem eqv_trans : forall x y z, x == y -> y == z -> x == z.
Proof.
  intros x y z H1 H2.
  apply atm_atl_eqv.
  - apply (atm_trans _ y); apply eqv_atm; trivial.
  - apply (atm_trans _ y); apply eqv_atl; trivial.
Qed.

Theorem lt_eqv_trans : forall x y z, x < y -> y == z -> x < z.
Proof.
  intros x y z H1 H2.
  apply eqv_atm in H2.
  apply (lt_atm_trans _ y); trivial.
Defined.

Theorem eqv_lt_trans : forall x y z, x == y -> y < z -> x < z.
Proof.
  intros x y z H1 H2.
  apply eqv_atm in H1.
  apply (atm_lt_trans _ y); trivial.
Defined.

Definition equivalence_class_of (x : R) : set R :=
  fun y => y == x.

Theorem ec_own : forall x, x ∈ equivalence_class_of x.
Proof.
  exact eqv_refl.
Qed.

Theorem ec_unique :
  forall x y, x ∈ equivalence_class_of y ->
    forall z, z ∈ equivalence_class_of x <-> z ∈ equivalence_class_of y.
Proof.
  intros x y H z.
  split; intro H2.
  - apply (eqv_trans _ x); trivial.
  - apply eqv_sym in H.
    apply (eqv_trans _ y); trivial.
Qed.

Theorem eqv_same_ec :
  forall x y, x == y <-> exists z, x ∈ equivalence_class_of z /\ y ∈ equivalence_class_of z.
Proof.
  intros x y.
  split; intro H.
  - exists y.
    split; trivial.
    apply eqv_refl.
  - destruct H as [z [H1 H2]].
    apply eqv_sym in H2.
    apply (eqv_trans _ z); trivial.
Defined.

Add Relation R eqv
  reflexivity proved by eqv_refl
  symmetry proved by eqv_sym
  transitivity proved by eqv_trans
  as eqv_rel.

Add Morphism lt with signature (eqv ==> eqv ==> iff) as lt_mor.
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  split; intro H;
    [apply (atm_lt_trans _ x1), (lt_atm_trans _ y1) | apply (atm_lt_trans _ x2), (lt_atm_trans _ y2)];
    assumption || (apply eqv_atl; assumption) || (apply eqv_atm; assumption).
Defined.

Add Morphism apart with signature (eqv ==> eqv ==> iff) as apart_mor.
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  apply Morphisms_Prop.or_iff_morphism;
    apply lt_mor_Proper; trivial.
Defined.

Add Morphism atm with signature (eqv ==> eqv ==> iff) as atm_mor.
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  apply Morphisms_Prop.not_iff_morphism;
    apply lt_mor_Proper; trivial.
Qed.

Theorem eqv_compatible : Proper (eqv ==> eqv ==> iff) eqv.
  intros x1 x2 Hx y1 y2 Hy.
  split; intro H;
    [apply (eqv_trans _ x1), (eqv_trans _ y1) | apply (eqv_trans _ x2), (eqv_trans _ y2)];
    assumption || (apply eqv_sym; assumption).
Qed.

Lemma lem_dn :
  ExcludedMiddle -> forall P : Prop, ~ ~ P <-> P.
Proof.
  intros EM P.
  split; [|tauto].
  intro H.
  destruct (EM P) as [H2|H2].
  - exact H2.
  - contradict H.
    exact H2.
Qed.

Theorem lem_not_atm_gt : ExcludedMiddle -> forall x y, ~ x <= y -> x > y.
Proof.
  intros.
  apply lem_dn; trivial.
Qed.

Theorem lem_not_eqv_apart : ExcludedMiddle -> forall x y, ~ x == y -> x =/= y.
Proof.
  intros.
  apply lem_dn; trivial.
Qed.

Theorem dn_trichotomy : forall x y, ~ ~ (x < y \/ x == y \/ x > y).
  intros x y HN.
  assert (x == y) as HE.
  - intros [H2|H2]; contradict HN.
    + left. exact H2.
    + right. right. exact H2.
  - contradict HN.
    right. left. exact HE.
Qed.

Theorem lem_trichotomy : ExcludedMiddle -> forall x y, x < y \/ x == y \/ x > y.
  intros. apply lem_dn, dn_trichotomy; trivial.
Qed.

Lemma dn_imp_dn : forall P Q : Prop, ~ ~ P -> (P -> Q) -> ~ ~ Q.
Proof.
  intros P Q H1 H2 HN.
  assert (~ P) as H3.
  - intro H4.
    apply HN, H2, H4.
  - apply H1, H3.
Qed.

Theorem dn_lt_or_eqv : forall x y, x <= y -> ~ ~ (x < y \/ x == y).
Proof.
  intros x y H.
  apply (dn_imp_dn (x < y \/ x == y \/ x > y)).
  - apply dn_trichotomy.
  - unfold atm in H.
    tauto.
Qed.

Theorem lem_lt_or_eqv : ExcludedMiddle -> forall x y, x <= y -> x < y \/ x == y.
Proof.
  intros. apply lem_dn, dn_lt_or_eqv; trivial.
Qed.

Theorem dn_gt_or_eqv : forall x y, x >= y -> ~ ~ (x > y \/ x == y).
Proof.
  intros x y H.
  apply (dn_imp_dn (x < y \/ x == y \/ x > y)).
  - apply dn_trichotomy.
  - unfold atm in H.
    tauto.
Qed.

Theorem lem_gt_or_eqv : ExcludedMiddle -> forall x y, x >= y -> x > y \/ x == y.
Proof.
  intros. apply lem_dn, dn_gt_or_eqv; trivial.
Qed.

Lemma dn_lem : forall P : Prop, ~ ~ (P \/ ~ P).
Proof.
  tauto.
Qed.

Theorem dn_lt_or_atl : forall x y, ~ ~ (x < y \/ x >= y).
Proof.
  intros. apply dn_lem.
Qed.

Theorem lem_lt_or_atl : ExcludedMiddle -> forall x y, x < y \/ x >= y.
Proof.
  intros H x y. apply H.
Qed.

Theorem dn_apart_or_eqv : forall x y, ~ ~ (x =/= y \/ x == y).
Proof.
  intros. apply dn_lem.
Qed.

Theorem lem_apart_or_eqv : ExcludedMiddle -> forall x y, x =/= y \/ x == y.
Proof.
  intros H x y. apply H.
Qed.

Theorem dn_atm_or_atl : forall x y, ~ ~ (x <= y \/ x >= y).
Proof.
  intros x y.
  apply (dn_imp_dn (x < y \/ x >= y)).
  - apply dn_lem.
  - intros [H|H].
    + left.
      apply lt_atm, H.
    + tauto.
Qed.

Theorem lem_atm_or_atl : ExcludedMiddle -> forall x y, x <= y \/ x >= y.
Proof.
  intros. apply lem_dn, dn_atm_or_atl; trivial.
Qed.

Theorem dn_apart_or_atm : forall x y, ~ ~ (x =/= y \/ x <= y).
Proof.
  intros x y.
  apply (dn_imp_dn (x =/= y \/ x == y)).
  - apply dn_lem.
  - intros [H|H].
    + tauto.
    + right.
      apply eqv_atm, H.
Qed.

Theorem lem_apart_or_atm : ExcludedMiddle -> forall x y, x =/= y \/ x <= y.
Proof.
  intros. apply lem_dn, dn_apart_or_atm; trivial.
Qed.

Theorem dn_apart_or_atl : forall x y, ~ ~ (x =/= y \/ x >= y).
Proof.
  intros x y.
  apply (dn_imp_dn (x =/= y \/ x == y)).
  - apply dn_lem.
  - intros [H|H].
    + tauto.
    + right.
      apply eqv_atl, H.
Qed.

Theorem lem_apart_or_atl : ExcludedMiddle -> forall x y, x =/= y \/ x >= y.
Proof.
  intros. apply lem_dn, dn_apart_or_atl; trivial.
Qed.

Definition decidable (P : Prop) := {P} + {~ P}.

Definition QIlt_dec (rs ss : Qinterval) : decidable (rs < ss)%QI :=
  match Qlt_le_dec (max rs) (min ss) with
  | left p => left p
  | right p => right (Qle_not_lt _ _ p)
  end.

Lemma refute_or : forall A B : Prop, ~ A -> ~ B -> ~ (A \/ B).
Proof.
  tauto.
Qed.

Definition or_dec {A B : Prop} (d : decidable A) (e : decidable B) : decidable (A \/ B) :=
  match d with
  | left p => left (or_introl p)
  | right p =>
      match e with
      | left q => left (or_intror q)
      | right q => right (refute_or _ _ p q)
      end
  end.

Lemma or_ex_ex_or :
  forall (A : Type) (P Q : A -> Prop),
    (exists x, P x) \/ (exists x, Q x) -> exists x, P x \/ Q x.
Proof.
  intros A P Q [[x H]|[x H]]; exists x; [left|right]; exact H.
Defined.

Definition find_lt_witness (w x y z : R) (p : w < x \/ y < z) : nat :=
  constructive_ground_epsilon_nat _
    (fun k => or_dec (QIlt_dec w.[k] x.[k]) (QIlt_dec y.[k] z.[k]))
    (or_ex_ex_or _ _ _ p).

Lemma find_lt_witness_spec :
  forall w x y z p, let k := find_lt_witness w x y z p in (w.[k] < x.[k] \/ y.[k] < z.[k])%QI.
Proof.
  intros.
  unfold find_lt_witness in k.
  apply constructive_ground_epsilon_spec_nat.
Defined.

Lemma contradict_left : forall A B : Prop, A \/ B -> ~A -> B.
Proof.
  intros A B [H1|H1] H2.
  - contradict H2.
    exact H1.
  - exact H1.
Defined.

Definition lt_or_dec (w x y z : R) (p : w < x \/ y < z) : {w < x} + {y < z} :=
  let k := find_lt_witness w x y z p in
    match QIlt_dec w.[k] x.[k] with
    | left q => left (ex_intro _ k q)
    | right q => right (ex_intro _ k (contradict_left _ _ (find_lt_witness_spec w x y z p) q))
    end.

Definition compare (x y : R) (p : x =/= y) : {x < y} + {x > y} :=
  lt_or_dec x y y x p.

Definition sum2bool {A B : Prop} (u : {A} + {B}) : bool := proj1_sig (bool_of_sumbool u).

Theorem compare_compatible :
  forall x1 x2, x1 == x2 -> forall y1 y2, y1 == y2 -> forall p1 p2,
    sum2bool (compare x1 y1 p1) = sum2bool (compare x2 y2 p2).
Proof.
  intros x1 x2 Hx y1 y2 Hy p1 p2.
  destruct (compare x1 y1 p1) as [H1|H1];
    destruct (compare x2 y2 p2) as [H2|H2]; trivial;
    cbn; rewrite Hx, Hy in H1;
    contradict H2;
    apply lt_not_gt, H1.
Qed.

Definition Markov :=
  forall P : nat -> Prop, (forall n, P n \/ ~ P n) -> ~ (forall n, ~ P n) -> exists n, P n.

Lemma lem_markov : ExcludedMiddle -> Markov.
Proof.
  intros ExcludedMiddle P D H.
  destruct (ExcludedMiddle (exists n, P n)) as [H2|H2]; trivial.
  contradict H.
  intros n Hn.
  contradict H2.
  exists n.
  trivial.
Qed.

Lemma markov_sum_dn :
  Markov -> forall P : nat -> Prop, (forall n, {P n} + {~ P n}) -> ~ ~ (exists n, P n) -> exists n, P n.
Proof.
  firstorder.
Qed.

Theorem markov_not_atm_gt : Markov -> forall x y, ~ x <= y <-> x > y.
Proof.
  intros HM x y.
  split; [|unfold atm; tauto].
  intro H.
  apply markov_sum_dn; trivial.
  intro n.
  apply QIlt_dec.
Qed.

Lemma ex_or_or_ex :
  forall (A : Type) (P Q : A -> Prop),
    (exists x, P x \/ Q x) -> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros A P Q [x [H|H]]; [left|right]; exists x; exact H.
Defined.

Theorem markov_or_lt_stable :
  Markov -> forall w x y z, ~ ~ (w < x \/ y < z) <-> w < x \/ y < z.
Proof.
  intros HM w x y z.
  split; [|tauto].
  intro H.
  apply ex_or_or_ex, markov_sum_dn; trivial.
  - intro n.
    apply or_dec; apply QIlt_dec.
  - apply (dn_imp_dn (w < x \/ y < z)); trivial.
    apply or_ex_ex_or.
Qed.

Theorem markov_not_eqv_apart : Markov -> forall x y, ~ x == y <-> x =/= y.
Proof.
  intros.
  apply markov_or_lt_stable; trivial.
Qed.

Definition Q2R_bounds (r : Q) := make_Stream (fun k => [r, r]Q).

Lemma Q2R_nth : forall r k, (Q2R_bounds r).[k] = [r, r]Q.
Proof.
  intros r k.
  unfold Q2R_bounds.
  rewrite make_Stream_spec.
  trivial.
Qed.

Lemma Q2R_nested : forall r, nested (Q2R_bounds r).
Proof.
  intros r k1 k2 Hk.
  repeat rewrite Q2R_nth.
  repeat split; cbn; q_order.
Qed.

Lemma Q2R_width : forall r k, (width (Q2R_bounds r).[k] == 0)%Q.
  intros r k.
  rewrite Q2R_nth.
  apply Qplus_opp_r.
Qed.

Lemma Q2R_convergent : forall r, convergent (Q2R_bounds r).
Proof.
  intros r eps Heps.
  exists 0%nat.
  eapply QOrder.eq_lt; try eassumption.
  apply Q2R_width; trivial.
Defined.

Definition Q2R (r : Q) := make_R (Q2R_bounds r) (Q2R_nested r) (Q2R_convergent r).

Notation "-1" := (Q2R (-1)) : R_scope.
Notation "0" := (Q2R 0) : R_scope.
Notation "1" := (Q2R 1) : R_scope.

Lemma Q2R_in_nth : forall r k, r ∈ (Q2R r).[k].
Proof.
  intros.
  setoid_rewrite Q2R_nth.
  split; apply Qle_refl.
Qed.

Theorem Q2R_lt : forall r s, (r < s)%Q <-> Q2R r < Q2R s.
Proof.
  intros r s.
  split; intro H.
  - exists 0%nat.
    setoid_rewrite Q2R_nth.
    exact H.
  - destruct H as [k H].
    setoid_rewrite Q2R_nth in H.
    exact H.
Defined.

Theorem Q2R_apart : forall r s, ~ (r == s)%Q <-> Q2R r =/= Q2R s.
Proof.
  intros r s.
  split; intro H.
  - destruct (QOrder.TO.lt_total r s) as [HC|[HC|HC]];
      try (contradict H; apply HC);
      [left|right]; exists 0%nat; exact HC.
  - destruct H as [H|H]; apply Q2R_lt in H; q_order.
Defined.

Theorem Q2R_eqv : forall r s, (r == s)%Q <-> Q2R r == Q2R s.
Proof.
  intros r s.
  split; intro H.
  - unfold eqv.
    rewrite <- Q2R_apart.
    contradict H.
    exact H.
  - apply QOrder.not_neq_eq.
    rewrite Q2R_apart.
    exact H.
Qed.

Theorem Q2R_atm : forall r s, (r <= s)%Q <-> Q2R r <= Q2R s.
Proof.
  intros r s.
  unfold atm.
  rewrite <- Q2R_lt.
  split; q_order.
Qed.

Add Morphism Q2R with signature (Qeq ==> eqv) as Q2R_mor.
Proof.
  apply Q2R_eqv.
Qed.

Theorem lt_0_1 : 0 < 1.
Proof. apply Q2R_lt. reflexivity. Defined.

Theorem apart_0_1 : 0 =/= 1.
Proof. apply Q2R_apart. discriminate. Defined.

Theorem bounds_correct : forall (x : R) k, Q2R (min x.[k]) <= x /\ x <= Q2R (max x.[k]).
Proof.
  intros x k.
  split; intros [k2 HN];
    setoid_rewrite Q2R_nth in HN;
    contradict HN;
    apply Qle_not_lt, bounds_consistent.
Qed.

Lemma eqv_common_point1 :
  forall x y, x == y -> forall k, let r := Qmax (min x.[k]) (min y.[k]) in r ∈ x.[k] /\ r ∈ y.[k].
Proof.
  intros x y H k r.
  subst r.
  split; split; try (apply Q.le_max_l || apply Q.le_max_r);
    destruct (Q.max_spec (min x.[k]) (min y.[k])) as [[_ H2]|[_ H2]];
    rewrite H2;
    try apply bounds_consistent;
    apply Qnot_lt_le;
    intro H3; apply H;
    [left|right]; exists k; exact H3.
Qed.

Lemma eqv_common_point2 : forall x y : R, (forall k, exists r, r ∈ x.[k] /\ r ∈ y.[k]) -> x == y.
Proof.
  intros x y H [[k HN]|[k HN]];
    unfold QIlt in HN;
    destruct (H k) as [r [[H1 H2] [H3 H4]]];
    q_order.
Qed.

Lemma eqv_common_point : forall x y, x == y <-> (forall k, exists r, r ∈ x.[k] /\ r ∈ y.[k]).
Proof.
  intros x y.
  split.
  - intros H k.
    exists (Qmax (min x.[k]) (min y.[k])).
    apply eqv_common_point1; trivial.
  - apply eqv_common_point2.
Defined.

Lemma eqv_fromQ : forall x y : R, (forall k, exists r s, (r ∈ x.[k] /\ s ∈ y.[k]) /\ r == s)%Q -> x == y.
Proof.
  intros x y H.
  apply eqv_common_point2.
  intro k.
  destruct (H k) as [r [s [H1 H2]]].
  exists r.
  rewrite H2 at 2.
  exact H1.
Qed.

Create HintDb fromQ.
Global Hint Resolve bounds_min_elem | 2 : fromQ.
Global Hint Resolve Q2R_in_nth | 1 : fromQ.
Ltac fromQ := intros; apply eqv_fromQ; intro k; eexists; eexists; split; [split; auto with fromQ|try field].

Definition QIplus rs ss := [Qred (min rs + min ss), Qred (max rs + max ss)]Q.
Infix "+" := QIplus : QI_scope.

Lemma QIplus_spec : forall r s (rs ss : Qinterval), r ∈ rs -> s ∈ ss -> (r + s)%Q ∈ rs + ss.
Proof.
  intros r s rs ss Hr Hs.
  unfold is_element_of, QIcontents in *.
  cbn -[Qplus].
  repeat rewrite Qred_correct.
  split; apply Qplus_le_compat; tauto.
Qed.

Definition plus_bounds (x y : R) := make_Stream (fun k => x.[k] + y.[k]).

Lemma plus_nth : forall x y k, (plus_bounds x y).[k] = x.[k] + y.[k].
Proof.
  setoid_rewrite make_Stream_spec; trivial.
Qed.

Lemma plus_nested : forall x y, nested (plus_bounds x y).
Proof.
  intros x y k1 k2 Hk.
  repeat rewrite plus_nth.
  cbn -[Qplus].
  repeat rewrite Qred_correct.
  split; apply QIplus_spec; apply bounds_nested, Hk.
Qed.

Lemma Qhalf_pos : forall r, (r > 0 -> r / 2 > 0)%Q.
Proof.
  intros r H.
  apply (Qmult_lt_compat_r _ _ (/ 2)) in H; [|reflexivity].
  setoid_replace (0 / 2)%Q with 0%Q in H; [|reflexivity].
  exact H.
Qed.

Lemma Qplus_lt_compat: forall x y z t, (x < y -> z < t -> x + z < y + t)%Q.
Proof.
  intros.
  apply Qplus_lt_le_compat, Qlt_le_weak; trivial.
Qed.

Lemma plus_convergent' :
  forall (x y : R) eps k1 k2,
    (width x.[k1] < eps / 2 -> width y.[k2] < eps / 2 ->
      width (plus_bounds x y).[Nat.max k1 k2] < eps)%Q.
Proof.
  intros x y eps k1 k2 H1 H2.
  set (k3 := Nat.max k1 k2).
  apply (bounds_width_lt _ _ k3) in H1, H2; try (apply Nat.le_max_l || apply Nat.le_max_r).
  unfold width in *.
  rewrite plus_nth.
  cbn -[Qplus].
  repeat rewrite Qred_correct.
  setoid_replace ((max x.[k3] + max y.[k3]) - (min x.[k3] + min y.[k3]))%Q
    with ((max x.[k3] - min x.[k3]) + (max y.[k3] - min y.[k3]))%Q by ring.
  setoid_replace eps with (eps/2 + eps/2)%Q by field.
  apply Qplus_lt_compat; trivial.
Qed.

Lemma plus_convergent : forall x y, convergent (plus_bounds x y).
Proof.
  intros x y eps Heps.
  apply Qhalf_pos in Heps.
  destruct (bounds_convergent x (eps/2)%Q Heps) as [k1 H1].
  destruct (bounds_convergent y (eps/2)%Q Heps) as [k2 H2].
  exists (Nat.max k1 k2).
  apply plus_convergent'; trivial.
Defined.

Definition plus (x y : R) := make_R (plus_bounds x y) (plus_nested x y) (plus_convergent x y).
Infix "+" := plus : R_scope.

Lemma plus_in_nth : forall r s (x y : R) k, r ∈ x.[k] -> s ∈ y.[k] -> (r + s)%Q ∈ (x + y).[k].
Proof.
  intros.
  setoid_rewrite plus_nth.
  apply QIplus_spec; trivial.
Qed.
Global Hint Resolve plus_in_nth | 1 : fromQ.

Add Morphism plus with signature (eqv ==> eqv ==> eqv) as plus_mor.
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  rewrite eqv_common_point in *.
  intro k.
  destruct (Hx k) as [r Hr], (Hy k) as [s Hs].
  exists (r + s)%Q.
  split; apply plus_in_nth; tauto.
Qed.

Theorem plus_comm: forall x y, x + y == y + x.
Proof. fromQ. Qed.

Theorem plus_assoc: forall x y z, (x + y) + z == x + (y + z).
Proof. fromQ. Qed.

Theorem plus_0_r: forall x, x + 0 == x.
Proof. fromQ. Qed.

Theorem plus_0_l: forall x, 0 + x == x.
Proof. fromQ. Qed.

Theorem Q2R_plus : forall r s, Q2R (r + s) == Q2R r + Q2R s.
Proof. fromQ. Qed.

Definition QIopp rs := [-max rs, -min rs]Q.
Notation "- x" := (QIopp x) : QI_scope.

Lemma QIopp_spec : forall r (rs : Qinterval), r ∈ rs -> (- r)%Q ∈ - rs.
Proof.
  intros r rs [H1 H2].
  split; apply Qopp_le_compat; trivial.
Qed.

Definition opp_bounds (x : R) := make_Stream (fun k => - x.[k]).

Lemma opp_nth : forall x k, (opp_bounds x).[k] = - x.[k].
Proof.
  setoid_rewrite make_Stream_spec; trivial.
Qed.

Lemma opp_nested : forall x, nested (opp_bounds x).
  intros x k1 k2 Hk.
  repeat rewrite opp_nth.
  split; apply QIopp_spec, bounds_nested, Hk.
Qed.

Lemma QIopp_width : forall rs, (width (- rs) == width rs)%Q.
  intro rs.
  setoid_rewrite Qplus_comm at 1.
  setoid_rewrite Qopp_opp.
  reflexivity.
Qed.

Lemma opp_convergent' :
  forall (x : R) k eps, (width x.[k] < eps -> width (opp_bounds x).[k] < eps)%Q.
Proof.
  intros x k eps H.
  rewrite opp_nth, QIopp_width.
  exact H.
Qed.

Lemma opp_convergent : forall x, convergent (opp_bounds x).
Proof.
  intros x eps Heps.
  destruct (bounds_convergent x eps Heps) as [k H].
  exists k.
  apply opp_convergent', H.
Defined.

Definition opp (x : R) := make_R (opp_bounds x) (opp_nested x) (opp_convergent x).
Notation "- x" := (opp x) : R_scope.

Lemma opp_in_nth : forall r (x : R) k, r ∈ x.[k] -> (- r)%Q ∈ (- x).[k].
Proof.
  intros.
  setoid_rewrite opp_nth.
  apply QIopp_spec; trivial.
Qed.
Global Hint Resolve opp_in_nth | 1 : fromQ.

Add Morphism opp with signature (eqv ==> eqv) as opp_mor.
Proof.
  intros x1 x2 Hx.
  rewrite eqv_common_point in *.
  intro k.
  destruct (Hx k) as [r Hr].
  exists (- r)%Q.
  split; apply opp_in_nth; tauto.
Qed.

Theorem Q2R_opp : forall r, Q2R (- r) == - Q2R r.
Proof. fromQ. Qed.

Theorem plus_opp_0_r : forall x, x + (- x) == 0.
Proof. fromQ. Qed.

Theorem plus_opp_0_l : forall x, (- x) + x == 0.
Proof. fromQ. Qed.

Theorem opp_opp : forall x, - (- x) == x.
Proof. fromQ. Qed.

Theorem opp_plus : forall x y, - (x + y) == (- x) + (- y).
Proof. fromQ. Qed.

Theorem opp_0 : - 0 == 0.
Proof. fromQ. Qed.

Theorem opp_shift : forall x y, x == - y -> y == -x.
Proof.
  intros x y H.
  rewrite <- (opp_opp y), H.
  reflexivity.
Qed.

Definition minus (x y : R) := x + (- y).
Infix "-" := minus : R_scope.

Add Morphism minus with signature (eqv ==> eqv ==> eqv) as minus_mor.
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  unfold minus.
  rewrite Hx, Hy.
  reflexivity.
Qed.

Lemma minus_in_nth : forall r s (x y : R) k, r ∈ x.[k] -> s ∈ y.[k] -> (r - s)%Q ∈ (x - y).[k].
Proof.
  intros.
  unfold minus, Qminus.
  auto with fromQ.
Qed.
Global Hint Resolve minus_in_nth | 1 : fromQ.

Theorem Q2R_minus : forall r s, Q2R (r - s) == Q2R r - Q2R s.
Proof. fromQ. Qed.

Theorem plus_minus : forall x y, (x + y) - y == x.
Proof. fromQ. Qed.

Theorem minus_plus : forall x y, (x - y) + y == x.
Proof. fromQ. Qed.

Theorem minus_shift : forall x y z, x - y == z <-> x == z + y.
Proof.
  intros x y z.
  split; intro H.
  - rewrite <- H.
    symmetry.
    apply minus_plus.
  - rewrite H.
    apply plus_minus.
Qed.

Lemma lt_plus_r1' : forall x y z k, ((x + z)%R.[k] < (y + z)%R.[k] -> x.[k] < y.[k])%QI.
Proof.
  intros x y z k H.
  apply (Qplus_lt_l _ _ (min z.[k])).
  apply (Qle_lt_trans _ (max x.[k] + max z.[k])).
  - apply Qplus_le_r, bounds_nonempty.
  - setoid_rewrite plus_nth in H.
    unfold QIplus, QIlt in H.
    setoid_rewrite Qred_correct in H.
    exact H.
Qed.

Lemma lt_plus_r1 : forall x y z, x + z < y + z -> x < y.
Proof.
  intros x y z [k H].
  exists k.
  exact (lt_plus_r1' x y z k H).
Defined.

Lemma lt_plus_r2 : forall x y z, x < y -> x + z < y + z.
Proof.
  intros x y z H.
  apply (lt_plus_r1 _ _ (- z)).
  revert H.
  apply lt_mor_Proper; apply plus_minus.
Defined.

Theorem lt_plus_r : forall x y z, x < y <-> x + z < y + z.
Proof.
  intros.
  split; [apply lt_plus_r2|apply lt_plus_r1].
Defined.

Theorem atm_plus_r : forall x y z, x <= y <-> x + z <= y + z.
Proof.
  intros.
  apply Morphisms_Prop.not_iff_morphism; apply lt_plus_r.
Qed.

Theorem apart_plus_r : forall x y z, x =/= y <-> x + z =/= y + z.
Proof.
  intros.
  apply Morphisms_Prop.or_iff_morphism; apply lt_plus_r.
Defined.

Theorem eqv_plus_r : forall x y z, x == y <-> x + z == y + z.
Proof.
  intros.
  apply Morphisms_Prop.not_iff_morphism; apply apart_plus_r.
Qed.

Lemma iff_trans : forall A B C : Prop, A <-> B -> B <-> C -> A <-> C.
Proof. tauto. Defined.

Theorem lt_plus_l : forall x y z, x < y <-> z + x < z + y.
Proof.
  intros.
  apply (iff_trans _ (x + z < y + z)).
  - apply lt_plus_r.
  - apply lt_mor_Proper; apply plus_comm.
Defined.

Theorem atm_plus_l : forall x y z, x <= y <-> z + x <= z + y.
Proof.
  intros.
  apply Morphisms_Prop.not_iff_morphism; apply lt_plus_l.
Qed.

Theorem apart_plus_l : forall x y z, x =/= y <-> z + x =/= z + y.
Proof.
  intros.
  apply Morphisms_Prop.or_iff_morphism; apply lt_plus_l.
Defined.

Theorem eqv_plus_l : forall x y z, x == y <-> z + x == z + y.
Proof.
  intros.
  apply Morphisms_Prop.not_iff_morphism; apply apart_plus_l.
Qed.

Theorem lt_plus : forall w x y z, w < x -> y < z -> w + y < x + z.
Proof.
  intros w x y z H1 H2.
  apply (lt_trans _ (x + y)); [apply lt_plus_r|apply lt_plus_l]; trivial.
Defined.

Theorem lt_atm_plus : forall w x y z, w < x -> y <= z -> w + y < x + z.
Proof.
  intros w x y z H1 H2.
  apply (lt_atm_trans _ (x + y)); [apply lt_plus_r|apply atm_plus_l]; trivial.
Defined.

Theorem atm_lt_plus : forall w x y z, w <= x -> y < z -> w + y < x + z.
Proof.
  intros w x y z H1 H2.
  apply (atm_lt_trans _ (x + y)); [apply atm_plus_r|apply lt_plus_l]; trivial.
Defined.

Theorem atm_plus : forall w x y z, w <= x -> y <= z -> w + y <= x + z.
Proof.
  intros w x y z H1 H2.
  apply (atm_trans _ (x + y)); [apply atm_plus_r|apply atm_plus_l]; trivial.
Qed.

Theorem plus_pos : forall x y, x > 0 -> y > 0 -> x + y > 0.
Proof.
  intros.
  eapply eqv_lt_trans; [apply eqv_sym, plus_0_r|].
  apply lt_plus; trivial.
Defined.

Theorem plus_neg : forall x y, x < 0 -> y < 0 -> x + y < 0.
Proof.
  intros.
  eapply lt_eqv_trans; [|apply plus_0_r].
  apply lt_plus; trivial.
Defined.

Theorem plus_atl_0 : forall x y, x >= 0 -> y >= 0 -> x + y >= 0.
  intros.
  rewrite <- (plus_0_r 0).
  apply atm_plus; trivial.
Qed.

Theorem plus_atm_0 : forall x y, x <= 0 -> y <= 0 -> x + y <= 0.
  intros.
  rewrite <- (plus_0_r 0).
  apply atm_plus; trivial.
Qed.

Lemma Qlt_opp : forall r s, (r < s <-> - r > - s)%Q.
Proof.
  intros r s.
  split; intro H;
    apply Qnot_le_lt; apply Qlt_not_le in H;
    contradict H;
    [setoid_rewrite <- Qopp_opp|];
    apply Qopp_le_compat, H.
Qed.

Lemma lt_opp1' : forall (x y : R) k, (x.[k] < y.[k] -> (- x)%R.[k] > (- y)%R.[k])%QI.
Proof.
  intros x y k H.
  setoid_rewrite opp_nth.
  revert H.
  apply Qlt_opp.
Qed.

Lemma lt_opp1 : forall x y, x < y -> - x > - y.
Proof.
  intros x y [k H].
  exists k.
  apply lt_opp1', H.
Defined.

Lemma lt_opp2 : forall x y, - x < - y -> x > y.
Proof.
  intros x y H.
  apply lt_opp1 in H.
  revert H.
  apply (lt_mor_Proper (- (- y))); apply opp_opp.
Defined.

Theorem lt_opp : forall x y, x < y <-> - x > - y.
Proof.
  intros; split; [apply lt_opp1|apply lt_opp2].
Defined.

Theorem atm_opp : forall x y, x <= y <-> - x >= - y.
Proof.
  intros.
  apply Morphisms_Prop.not_iff_morphism; apply lt_opp.
Qed.

Theorem apart_opp : forall x y, x =/= y <-> - x =/= - y.
Proof.
  intros.
  apply (iff_trans _ (y =/= x)).
  - split; apply apart_sym.
  - apply Morphisms_Prop.or_iff_morphism; apply lt_opp.
Defined.

Theorem eqv_opp : forall x y, x == y <-> - x == - y.
Proof.
  intros.
  apply Morphisms_Prop.not_iff_morphism; apply apart_opp.
Qed.

Theorem opp_neg_pos : forall x, x > 0 <-> - x < 0.
Proof.
  intro x.
  split; intro H.
  - apply lt_opp in H.
    apply (lt_eqv_trans _ (- 0)); trivial.
    apply opp_0.
  - apply lt_opp.
    apply (lt_eqv_trans _ 0); trivial.
    apply eqv_sym, opp_0.
Defined.

Theorem opp_pos_neg : forall x, x < 0 <-> - x > 0.
Proof.
  intro x.
  split; intro H.
  - apply lt_opp in H.
    apply (eqv_lt_trans _ (- 0)); trivial.
    apply eqv_sym, opp_0.
  - apply lt_opp.
    apply (eqv_lt_trans _ 0); trivial.
    apply opp_0.
Defined.

Lemma or_iff_compat : forall A B C D : Prop, (A <-> C) -> (B <-> D) -> (A \/ B) <-> (C \/ D).
Proof. tauto. Defined.

Theorem opp_apart_0 : forall x, x =/= 0 <-> - x =/= 0.
Proof.
  intro x.
  eapply iff_trans; [|apply apart_sym_iff].
  apply or_iff_compat.
  - apply opp_pos_neg.
  - apply opp_neg_pos.
Defined.

Theorem gt_diff_pos : forall x y, x < y <-> y - x > 0.
Proof.
  intros x y.
  split; intro H.
  - apply (eqv_lt_trans _ (x + - x)).
    + apply eqv_sym, plus_opp_0_r.
    + apply lt_plus_r, H.
  - apply (lt_plus_r _ _ (- x)).
    apply (eqv_lt_trans _ 0); trivial.
    apply plus_opp_0_r.
Defined.

Lemma Qle_or_ge : forall r s, (r <= s \/ r >= s)%Q.
Proof.
  intros r s.
  destruct (Qlt_le_dec r s) as [H|H]; [left; apply Qlt_le_weak|right]; exact H.
Defined.

Lemma Qmult_le_neg_r : forall x y z, (x <= y -> z <= 0 -> x * z >= y * z)%Q.
Proof.
  intros x y z H1 H2.
  setoid_rewrite <- Qopp_opp.
  apply Qopp_le_compat.
  apply Qopp_le_compat in H2.
  setoid_replace (- (x * z))%Q with (x * (- z))%Q by ring.
  setoid_replace (- (y * z))%Q with (y * (- z))%Q by ring.
  setoid_replace (- 0)%Q with 0%Q in H2 by ring.
  apply Qmult_le_compat_r; trivial.
Qed.

Lemma Qmult_between_r : forall r a b c, (a <= r <= b -> Qmin (a*c) (b*c) <= r*c <= Qmax (a*c) (b*c))%Q.
Proof.
  intros r a b c [H1 H2].
  destruct (Qle_or_ge 0 c) as [Hc|Hc]; split;
    eapply Qle_trans;
    try (apply Qmult_le_compat_r; eassumption);
    try (apply Qmult_le_neg_r; eassumption);
    [apply Q.le_min_l|apply Q.le_max_r|apply Q.le_min_r|apply Q.le_max_l].
Qed.

Lemma Qmult_between_l : forall r a b c, (a <= r <= b -> Qmin (c*a) (c*b) <= c*r <= Qmax (c*a) (c*b))%Q.
Proof.
  intros.
  setoid_rewrite Qmult_comm.
  apply Qmult_between_r, H.
Qed.

Definition QImult rs ss :=
  [Qred (Qmin (Qmin (min rs * min ss) (min rs * max ss)) (Qmin (max rs * min ss) (max rs * max ss))),
   Qred (Qmax (Qmax (min rs * min ss) (min rs * max ss)) (Qmax (max rs * min ss) (max rs * max ss)))]Q.
Infix "*" := QImult : QI_scope.

Lemma QImult_spec1 : forall r s (rs ss : Qinterval), r ∈ rs -> s ∈ ss -> (r * s)%Q ∈ rs * ss.
Proof.
  intros r s rs ss Hr Hs.
  unfold is_element_of, QIcontents in *.
  setoid_rewrite Qred_correct.
  split.
  - apply (Qle_trans _ (Qmin (min rs * s) (max rs * s))).
    + apply Q.min_glb;
        (eapply Qle_trans; [|apply Qmult_between_l; eassumption]);
        [apply Q.le_min_l|apply Q.le_min_r].
    + apply Qmult_between_r, Hr.
  - apply (Qle_trans _ (Qmax (min rs * s) (max rs * s))).
    + apply Qmult_between_r, Hr.
    + apply Q.max_lub;
        (eapply Qle_trans; [apply Qmult_between_l; eassumption|]);
        [apply Q.le_max_l|apply Q.le_max_r].
Qed.

Lemma QImult_spec2 :
  forall rs ss : Qinterval, nonempty rs -> nonempty ss ->
    (exists r s, r ∈ rs /\ s ∈ ss /\ (min (rs * ss) == r * s)%Q) /\
    (exists r s, r ∈ rs /\ s ∈ ss /\ (max (rs * ss) == r * s)%Q).
Proof.
  intros rs ss Hrs Hss.
  cbn.
  split;
    [
      unfold Qmin at 1, GenericMinMax.gmin;
      destruct (Qmin (min rs * min ss) (min rs * max ss) ?= Qmin (max rs * min ss) (max rs * max ss))%Q
    |
      unfold Qmax at 1, GenericMinMax.gmax;
      destruct (Qmax (min rs * min ss) (min rs * max ss) ?= Qmax (max rs * min ss) (max rs * max ss))%Q
    ];
    unfold Qmin, GenericMinMax.gmin, Qmax, GenericMinMax.gmax;
    try (
      destruct (min rs * min ss ?= min rs * max ss)%Q;
        eexists; eexists; (split; [|split]; [| |apply Qred_correct]; apply nonempty_min_max; assumption)
    );
    destruct (max rs * min ss ?= max rs * max ss)%Q;
      eexists; eexists; (split; [|split]; [| |apply Qred_correct]; apply nonempty_min_max; assumption).
Defined.

Definition mult_bounds (x y : R) := make_Stream (fun k => x.[k] * y.[k]).

Lemma mult_nth : forall x y k, (mult_bounds x y).[k] = x.[k] * y.[k].
Proof.
  setoid_rewrite make_Stream_spec; trivial.
Qed.

Lemma mult_nested : forall x y, nested (mult_bounds x y).
Proof.
  intros x y k1 k2 Hk.
  repeat rewrite mult_nth.
  split.
  - destruct (QImult_spec2 x.[k2] y.[k2]) as [[r [s [Hr [Hs H]]]] _]; try apply bounds_nonempty.
    rewrite H.
    apply QImult_spec1; eapply bounds_nested_elem; eassumption.
  - destruct (QImult_spec2 x.[k2] y.[k2]) as [_ [r [s [Hr [Hs H]]]]]; try apply bounds_nonempty.
    rewrite H.
    apply QImult_spec1; eapply bounds_nested_elem; eassumption.
Qed.

Lemma distance_le_width : forall r1 r2 (rs : Qinterval), r1 ∈ rs -> r2 ∈ rs -> (Qabs (r2 - r1) <= width rs)%Q.
Proof.
  intros r1 r2 rs [H1 H2] [H3 H4].
  destruct (Qle_or_ge 0 (r2 - r1));
    [rewrite Qabs_pos|unfold Qminus; rewrite Qabs_neg, Qopp_plus, Qopp_opp, Qplus_comm]; trivial;
    apply Qplus_le_compat, Qopp_le_compat; trivial.
Qed.

Lemma QI_Qabs_ub : forall r (rs : Qinterval), r ∈ rs -> (Qabs r <= Qmax (Qabs (min rs)) (Qabs (max rs)))%Q.
Proof.
  intros r rs [H1 H2].
  destruct (Qle_or_ge 0 r).
  - rewrite Qabs_pos; trivial.
    eapply Qle_trans; [eassumption|].
    rewrite <- Qabs_pos at 1; [apply Q.le_max_r|].
    q_order.
  - rewrite Qabs_neg; trivial.
    eapply Qle_trans; [apply Qopp_le_compat; eassumption|].
    rewrite <- Qabs_neg at 1; [apply Q.le_max_l|].
    q_order.
Qed.

Definition mult_delta (eps : Q) (x : R) : Q :=
  (eps / 2) / Qmax (Qmax (Qabs (min x.[0])) (Qabs (max x.[0]))) 1.

Lemma Qmax_1_pos : forall r, (Qmax r 1 > 0)%Q.
Proof.
  intro r.
  apply (Qlt_le_trans _ 1); [reflexivity|].
  apply Q.le_max_r.
Qed.

Lemma Qmax_1_nonzero : forall r, ~ (Qmax r 1 == 0)%Q.
Proof.
  intros r H.
  pose (Qmax_1_pos r) as H2.
  rewrite H in H2.
  discriminate.
Qed.

Lemma mult_delta_pos : forall eps x, (eps > 0 -> mult_delta eps x > 0)%Q.
Proof.
  intros eps x H.
  unfold mult_delta.
  set (den := Qmax (Qmax (Qabs (min x.[0])) (Qabs (max x.[0]))) 1).
  setoid_replace 0%Q with (0 / den)%Q by (field; apply Qmax_1_nonzero).
  apply Qmult_lt_compat_r.
  - apply Qinv_lt_0_compat, Qmax_1_pos.
  - apply Qhalf_pos, H.
Qed.

Lemma mult_convergent'1 :
  forall (x y : R) eps k3 r1 r2 s,
    (width x.[k3] < mult_delta eps y -> r1 ∈ x.[k3] -> r2 ∈ x.[k3] -> s ∈ y.[k3] ->
      s * (r2 - r1) < eps / 2)%Q.
Proof.
  intros x y eps k3 r1 r2 s Hw Hr1 Hr2 Hs.
  set (den := Qmax (Qmax (Qabs (min y.[0])) (Qabs (max y.[0]))) 1).
  apply
    (Qle_lt_trans _ (Qabs (s * (r2 - r1)))),
    (Qle_lt_trans _ (den * Qabs (r2 - r1))).
  - apply Qle_Qabs.
  - rewrite Qabs_Qmult.
    apply Qmult_le_compat_r, Qabs_nonneg.
    eapply Qle_trans; [|apply Q.le_max_l].
    apply QI_Qabs_ub.
    eapply bounds_nested_elem; [|eassumption].
    apply Peano.le_0_n.
  - setoid_replace (eps / 2)%Q with (den * mult_delta eps y)%Q.
    + apply Qmult_lt_l; [apply Qmax_1_pos|].
      eapply Qle_lt_trans; [|eassumption].
      apply distance_le_width; trivial.
    + unfold mult_delta, den.
      field.
      apply Qmax_1_nonzero.
Qed.

Lemma mult_convergent' :
  forall (x y : R) eps k1 k2,
    (width x.[k1] < mult_delta eps y -> width y.[k2] < mult_delta eps x ->
      width (mult_bounds x y).[Nat.max k1 k2] < eps)%Q.
Proof.
  intros x y eps k1 k2 H1 H2.
  set (k3 := Nat.max k1 k2).
  apply (bounds_width_lt _ _ k3) in H1, H2; try apply Nat.le_max_l; try apply Nat.le_max_r.
  destruct (QImult_spec2 x.[k3] y.[k3]) as [[r1 [s1 [H3 [H4 H5]]]] [r2 [s2 [H6 [H7 H8]]]]]; try apply bounds_nonempty.
  unfold width.
  rewrite mult_nth, H5, H8.
  setoid_replace (r2 * s2 - r1 * s1)%Q with (s2 * (r2 - r1) + r1 * (s2 - s1))%Q by ring.
  setoid_replace eps with (eps / 2 + eps / 2)%Q by field.
  apply Qplus_lt_compat.
  - apply (mult_convergent'1 x y _ k3); trivial.
  - apply (mult_convergent'1 y x _ k3); trivial.
Qed.

Lemma mult_convergent : forall x y, convergent (mult_bounds x y).
Proof.
  intros x y eps Heps.
  destruct (bounds_convergent x (mult_delta eps y)) as [k1 H1]; [apply mult_delta_pos, Heps|].
  destruct (bounds_convergent y (mult_delta eps x)) as [k2 H2]; [apply mult_delta_pos, Heps|].
  exists (Nat.max k1 k2).
  apply mult_convergent'; trivial.
Defined.

Definition mult (x y : R) := make_R (mult_bounds x y) (mult_nested x y) (mult_convergent x y).
Infix "*" := mult : R_scope.

Lemma mult_in_nth : forall r s (x y : R) k, r ∈ x.[k] -> s ∈ y.[k] -> (r * s)%Q ∈ (x * y).[k].
Proof.
  intros.
  setoid_rewrite mult_nth.
  apply QImult_spec1; trivial.
Qed.
Global Hint Resolve mult_in_nth | 1 : fromQ.

Add Morphism mult with signature (eqv ==> eqv ==> eqv) as mult_mor.
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  rewrite eqv_common_point in *.
  intro k.
  destruct (Hx k) as [r Hr], (Hy k) as [s Hs].
  exists (r * s)%Q.
  split; apply mult_in_nth; tauto.
Qed.

Theorem Q2R_mult : forall r s, Q2R (r * s) == Q2R r * Q2R s.
Proof. fromQ. Qed.

Theorem mult_comm: forall x y, x * y == y * x.
Proof. fromQ. Qed.

Theorem mult_assoc: forall x y z, (x * y) * z == x * (y * z).
Proof. fromQ. Qed.

Theorem mult_plus_dist_l : forall x y z, x * (y + z) == x * y + x * z.
Proof. fromQ. Qed.

Theorem mult_plus_dist_r : forall x y z, (x + y) * z == x * z + y * z.
Proof. fromQ. Qed.

Theorem mult_minus_dist_l : forall x y z, x * (y - z) == x * y - x * z.
Proof. fromQ. Qed.

Theorem mult_minus_dist_r : forall x y z, (x - y) * z == x * z - y * z.
Proof. fromQ. Qed.

Theorem mult_1_r : forall x, x * 1 == x.
Proof. fromQ. Qed.

Theorem mult_1_l : forall x, 1 * x == x.
Proof. fromQ. Qed.

Theorem mult_0_r : forall x, x * 0 == 0.
Proof. fromQ. Qed.

Theorem mult_0_l : forall x, 0 * x == 0.
Proof. fromQ. Qed.

Theorem mult_n1_r : forall x, x * -1 == - x.
Proof. fromQ. Qed.

Theorem mult_n1_l : forall x, -1 * x == - x.
Proof. fromQ. Qed.

Theorem mult_opp_r : forall x y, x * (- y) == - (x * y).
Proof. fromQ. Qed.

Theorem mult_opp_l : forall x y, (- x) * y == - (x * y).
Proof. fromQ. Qed.

Theorem mult_opp_opp : forall x y, (- x) * (- y) == x * y.
Proof. fromQ. Qed.

Lemma Qmult_pos_pos : (forall x y, x > 0 -> y > 0 -> x * y > 0)%Q.
Proof.
  intros x y Hx Hy.
  rewrite <- (Qmult_0_l y).
  apply Qmult_lt_compat_r; trivial.
Qed.

Theorem mult_pos_pos : forall x y, x > 0 -> y > 0 -> x * y > 0.
Proof.
  intros x y Hx Hy.
  destruct (lt_common_witness _ _ _ _ Hx Hy) as [k [H1 H2]].
  exists k.
  cbn in *.
  rewrite Q2R_nth, mult_nth in *.
  unfold QIlt, max in *.
  destruct (QImult_spec2 x.[k] y.[k]) as [[r [s [[Hr _] [[Hs _] E]]]] _]; try apply bounds_nonempty.
  rewrite E.
  apply Qmult_pos_pos.
  - apply (Qlt_le_trans _ (min x.[k])); trivial.
  - apply (Qlt_le_trans _ (min y.[k])); trivial.
Defined.

Theorem mult_pos_neg : forall x y, x > 0 -> y < 0 -> x * y < 0.
Proof.
  intros x y Hx Hy.
  apply opp_pos_neg.
  apply (lt_eqv_trans _ (x * (- y))).
  - apply mult_pos_pos; trivial.
    apply opp_pos_neg; trivial.
  - apply mult_opp_r.
Defined.

Theorem mult_neg_neg : forall x y, x < 0 -> y < 0 -> x * y > 0.
Proof.
  intros x y Hx Hy.
  apply (lt_eqv_trans _ ((- x) * (- y))).
  - apply mult_pos_pos; apply opp_pos_neg; trivial.
  - apply mult_opp_opp.
Defined.

Lemma Qmult_pos_conv_r : (forall x y, y > 0 -> x * y > 0 -> x > 0)%Q.
Proof.
  intros x y Hy Hxy.
  apply (Qmult_lt_r 0 x y); trivial.
  rewrite Qmult_0_l; trivial.
Qed.

Theorem mult_pos_conv_r : forall x y, y > 0 -> x * y > 0 -> x > 0.
Proof.
  intros x y Hy Hxy.
  destruct (lt_common_witness _ _ _ _ Hy Hxy) as [k [H1 H2]].
  exists k.
  cbn -[mult] in *.
  rewrite Q2R_nth in *.
  unfold QIlt, max in *.
  apply (Qmult_pos_conv_r _ (min y.[k])); trivial.
  apply (Qlt_le_trans _ _ _ H2).
  assert ((min x.[k] * min y.[k])%Q ∈ (x * y).[k]) as H; [|destruct H; trivial].
  auto with fromQ.
Defined.

Theorem mult_lt_r : forall x y z, z > 0 -> (x < y <-> x * z < y * z).
Proof.
  intros x y z Hz.
  split; intro H; apply gt_diff_pos; apply gt_diff_pos in H.
  - apply (mult_pos_pos _ z) in H; trivial.
    apply (lt_eqv_trans _ _ _ H).
    apply mult_minus_dist_r.
  - apply (mult_pos_conv_r _ z); trivial.
    apply (lt_eqv_trans _ _ _ H).
    apply eqv_sym, mult_minus_dist_r.
Defined.

Lemma mult_minus_opp_r : forall x y z, (x - y) * (- z) == y * z - x * z.
Proof. fromQ. Qed.

Theorem mult_lt_neg_r : forall x y z, z < 0 -> (x < y <-> x * z > y * z).
Proof.
  intros x y z Hz.
  apply opp_pos_neg in Hz.
  split; intro H; apply gt_diff_pos; apply gt_diff_pos in H.
  - apply (mult_pos_pos _ (- z)) in H; trivial.
    apply (lt_eqv_trans _ _ _ H).
    apply mult_minus_opp_r.
  - apply (mult_pos_conv_r _ (- z)); trivial.
    apply (lt_eqv_trans _ _ _ H).
    apply eqv_sym, mult_minus_opp_r.
Defined.

Theorem mult_atm_r : forall x y z, z > 0 -> (x <= y <-> x * z <= y * z).
Proof.
  intros x y z Hz.
  pose (mult_lt_r y x z Hz).
  unfold atm.
  tauto.
Qed.

Theorem mult_atm_neg_r : forall x y z, z < 0 -> (x <= y <-> x * z >= y * z).
Proof.
  intros x y z Hz.
  pose (mult_lt_neg_r y x z Hz).
  unfold atm.
  tauto.
Qed.

Lemma or_comm: forall A B : Prop, A \/ B <-> B \/ A.
Proof. tauto. Defined.

Theorem mult_apart_r : forall x y z, z =/= 0 -> (x =/= y <-> x * z =/= y * z).
Proof.
  intros x y z [Hz|Hz].
  - eapply iff_trans.
    + apply Morphisms_Prop.or_iff_morphism; apply mult_lt_neg_r, Hz.
    + apply or_comm.
  - apply Morphisms_Prop.or_iff_morphism; apply mult_lt_r, Hz.
Defined.

Theorem mult_eqv_r : forall x y z, z =/= 0 -> (x == y <-> x * z == y * z).
Proof.
  intros x y z Hz.
  pose (mult_apart_r x y z Hz).
  unfold eqv.
  tauto.
Qed.

Theorem mult_neg_pos : forall x y, x < 0 -> y > 0 -> x * y < 0.
Proof.
  intros x y Hx Hy.
  eapply eqv_lt_trans.
  - apply mult_comm.
  - apply mult_pos_neg; trivial.
Defined.

Theorem mult_pos_conv_l : forall x y, x > 0 -> x * y > 0 -> y > 0.
Proof.
  intros x y Hx Hxy.
  apply (mult_pos_conv_r _ x); trivial.
  eapply lt_eqv_trans.
  - eassumption.
  - apply mult_comm.
Defined.

Theorem mult_lt_l : forall x y z, z > 0 -> (x < y <-> z * x < z * y).
Proof.
  intros x y z Hz.
  eapply iff_trans.
  - apply mult_lt_r, Hz.
  - apply lt_mor_Proper; apply mult_comm.
Defined.

Theorem mult_lt_neg_l : forall x y z, z < 0 -> (x < y <-> z * x > z * y).
Proof.
  intros x y z Hz.
  eapply iff_trans.
  - apply mult_lt_neg_r, Hz.
  - apply lt_mor_Proper; apply mult_comm.
Defined.

Theorem mult_atm_l : forall x y z, z > 0 -> (x <= y <-> z * x <= z * y).
Proof.
  setoid_rewrite mult_comm.
  exact mult_atm_r.
Qed.

Theorem mult_atm_neg_l : forall x y z, z < 0 -> (x <= y <-> z * x >= z * y).
Proof.
  setoid_rewrite mult_comm.
  exact mult_atm_neg_r.
Qed.

Theorem mult_apart_l : forall x y z, z =/= 0 -> (x =/= y <-> z * x =/= z * y).
Proof.
  intros x y z Hz.
  eapply iff_trans.
  - apply mult_apart_r, Hz.
  - apply apart_mor_Proper; apply mult_comm.
Defined.

Theorem mult_eqv_l : forall x y z, z =/= 0 -> (x == y <-> z * x == z * y).
Proof.
  setoid_rewrite mult_comm.
  exact mult_eqv_r.
Qed.

Lemma not_elem_iff : forall r (rs : Qinterval), ~ r ∈ rs <-> (r < min rs \/ r > max rs)%Q.
Proof.
  intros r rs.
  split.
  - intro H.
    destruct (Qlt_le_dec r (min rs)) as [C|C].
    + left; trivial.
    + right.
      apply Qnot_le_lt.
      contradict H.
      split; trivial.
  - intros [H|H];
    contradict H;
    apply Qle_not_lt;
    destruct H; trivial.
Qed.

Lemma apart_not_elem : forall x r, x =/= Q2R r <-> exists k, ~ r ∈ x.[k].
Proof.
  intros x r.
  split.
  - intros [[k H]|[k H]];
      exists k;
      setoid_rewrite Q2R_nth in H;
      apply not_elem_iff;
      [right|left]; assumption.
  - intros [k H].
    apply not_elem_iff in H.
    destruct H as [H|H];
      [right|left]; exists k;
      setoid_rewrite Q2R_nth; assumption.
Defined.

Theorem mult_apart_0_iff : forall x y, x * y =/= 0 <-> x =/= 0 /\ y =/= 0.
Proof.
  intros x y.
  split; intro H.
  - apply apart_not_elem in H.
    destruct H as [k H].
    split;
      apply apart_not_elem;
      exists k;
      contradict H;
      [erewrite <- Qmult_0_l|erewrite <- Qmult_0_r];
      auto with fromQ.
  - destruct H as [[Hx|Hx] [Hy|Hy]].
    + right. apply mult_neg_neg; trivial.
    + left. apply mult_neg_pos; trivial.
    + left. apply mult_pos_neg; trivial.
    + right. apply mult_pos_pos; trivial.
Defined.

Theorem mult_eqv_0_iff : forall x y, x * y == 0 <-> ~ (x =/= 0 /\ y =/= 0).
  intros x y.
  apply not_iff_compat, mult_apart_0_iff.
Qed.

Lemma demorgan_not_or : forall P Q : Prop, ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof. tauto. Qed.

Theorem mult_eqv_0_iff_markov : Markov -> forall x y, x * y == 0 <-> ~ ~ (x == 0 \/ y == 0).
Proof.
  intros Markov x y.
  rewrite demorgan_not_or.
  repeat rewrite markov_not_eqv_apart; trivial.
  apply mult_eqv_0_iff.
Qed.

Theorem mult_eqv_0_iff_lem : ExcludedMiddle -> forall x y, x * y == 0 <-> x == 0 \/ y == 0.
Proof.
  intros ExcludedMiddle x y.
  setoid_rewrite <- lem_dn at 3; trivial.
  apply mult_eqv_0_iff_markov, lem_markov, ExcludedMiddle.
Qed.

Theorem mult_pos_iff : forall x y, x * y > 0 <-> (x > 0 /\ y > 0) \/ (x < 0 /\ y < 0).
Proof.
  intros x y.
  split; intro H.
  - apply lt_apart in H as H2.
    apply apart_sym, mult_apart_0_iff in H2.
    destruct H2 as [[Hx|Hx] [Hy|Hy]].
    + right. split; trivial.
    + contradict H.
      apply lt_not_gt, mult_neg_pos; trivial.
    + contradict H.
      apply lt_not_gt, mult_pos_neg; trivial.
    + left. split; trivial.
  - destruct H as [[Hx Hy]|[Hx Hy]].
    + apply mult_pos_pos; trivial.
    + apply mult_neg_neg; trivial.
Defined.

Theorem mult_neg_iff : forall x y, x * y < 0 <-> (x > 0 /\ y < 0) \/ (x < 0 /\ y > 0).
Proof.
  intros x y.
  split; intro H.
  - apply lt_apart in H as H2.
    apply mult_apart_0_iff in H2.
    destruct H2 as [[Hx|Hx] [Hy|Hy]].
    + contradict H.
      apply lt_not_gt, mult_neg_neg; trivial.
    + right. split; trivial.
    + left. split; trivial.
    + contradict H.
      apply lt_not_gt, mult_pos_pos; trivial.
  - destruct H as [[Hx Hy]|[Hx Hy]].
    + apply mult_pos_neg; trivial.
    + apply mult_neg_pos; trivial.
Defined.

Theorem mult_atl_0 : forall x y, x >= 0 -> y >= 0 -> x * y >= 0.
Proof.
  intros x y Hx Hy HN.
  apply mult_neg_iff in HN.
  destruct HN as [[_ HN]|[HN _]].
  - apply Hy, HN.
  - apply Hx, HN.
Qed.

Theorem mult_pos_atl_0_r : forall x y, y >= 0 -> x * y > 0 -> x > 0.
Proof.
  intros x y Hy H.
  apply mult_pos_iff in H.
  destruct H as [H|H].
  - destruct H; assumption.
  - destruct H as [_ H].
    contradict H.
    exact Hy.
Defined.

Theorem mult_lt_atl_0_r : forall x y z, z >= 0 -> x * z < y * z -> x < y.
Proof.
  intros x y z Hz H.
  apply gt_diff_pos, (mult_pos_atl_0_r _ z); trivial.
  eapply lt_eqv_trans; [|apply eqv_sym, mult_minus_dist_r].
  apply gt_diff_pos in H; trivial.
Defined.

Theorem mult_pos_atl_0_l : forall x y, x >= 0 -> x * y > 0 -> y > 0.
Proof.
  intros x y Hx H.
  apply (mult_pos_atl_0_r _ x); trivial.
  eapply lt_eqv_trans; [|apply mult_comm].
  exact H.
Defined.

Theorem mult_lt_atl_0_l : forall x y z, z >= 0 -> z * x < z * y -> x < y.
Proof.
  intros x y z Hz H.
  apply (mult_lt_atl_0_r _ _ z); trivial.
  revert H.
  apply lt_mor_Proper; apply mult_comm.
Defined.

Definition find_zeroless (x : R) (p : x =/= 0) := find_lt_witness x 0 0 x p.

Lemma find_zeroless_spec : forall x p, ~ 0%Q ∈ x.[find_zeroless x p].
Proof.
  intros x p.
  apply not_elem_iff.
  pose (find_lt_witness_spec x 0 0 x p) as H.
  cbn in H.
  rewrite Q2R_nth in H.
  tauto.
Qed.

Definition QIinv rs := [/ max rs, / min rs]Q.
Notation "/ x" := (QIinv x) : QI_scope.

Lemma Qnot_lt_le_iff : forall a b, (~ a < b <-> b <= a)%Q.
Proof.
  intros.
  split.
  - apply Qnot_lt_le.
  - apply Qle_not_lt.
Qed.

Lemma Qinv_le_contravar : forall a b, (a > 0 -> b > 0 -> a <= b <-> / b <= / a)%Q.
Proof.
  intros.
  rewrite <- Qnot_lt_le_iff, <- Qnot_lt_le_iff, Qinv_lt_contravar; trivial.
  tauto.
Qed.

Lemma Qle_opp : forall a b, (a <= b <-> - b <= - a)%Q.
Proof.
  intros.
  rewrite <- Qnot_lt_le_iff, <- Qnot_lt_le_iff, Qlt_opp.
  tauto.
Qed.

Lemma Qinv_opp : forall a, (~ a == 0 -> / - a == - / a)%Q.
Proof. intros. field. assumption. Qed.

Lemma Qinv_le_contravar_neg : forall a b, (a < 0 -> b < 0 -> a <= b <-> / b <= / a)%Q.
Proof.
  intros a b Ha Hb.
  setoid_rewrite Qle_opp.
  setoid_rewrite <- Qinv_opp; try (apply Qlt_not_eq; assumption).
  apply Qinv_le_contravar;
    apply (Qlt_opp _ 0); assumption.
Qed.

Lemma QIinv_spec : forall r (rs : Qinterval), ~ 0%Q ∈ rs -> r ∈ rs -> (/ r)%Q ∈ / rs.
Proof.
  intros r rs H0 [Hr1 Hr2].
  apply not_elem_iff in H0.
  destruct H0 as [H0|H0].
  - assert (r > 0)%Q as H1 by (eapply Qlt_le_trans; eassumption).
    assert (max rs > 0)%Q as H2 by (eapply Qlt_le_trans; eassumption).
    split; apply -> Qinv_le_contravar; trivial.
  - assert (r < 0)%Q as H1 by (eapply Qle_lt_trans; eassumption).
    assert (min rs < 0)%Q as H2 by (eapply Qle_lt_trans; eassumption).
    split; apply -> Qinv_le_contravar_neg; trivial.
Qed.

Lemma find_zeroless_ge : forall x p k, (k >= find_zeroless x p)%nat -> ~ 0%Q ∈ x.[k].
Proof.
  intros x p k H HN.
  eapply bounds_nested_elem in HN; try eassumption.
  apply find_zeroless_spec in HN.
  exact HN.
Qed.

Lemma find_zeroless_max : forall x p k, ~ 0%Q ∈ x.[Nat.max k (find_zeroless x p)].
Proof.
  intros x p k.
  apply (find_zeroless_ge x p), Nat.le_max_r.
Qed.

Definition inv_bounds (x : R) (p : x =/= 0) := make_Stream (fun k => / x.[Nat.max k (find_zeroless x p)]).

Lemma inv_nth : forall x p k, (inv_bounds x p).[k] = / x.[Nat.max k (find_zeroless x p)].
Proof.
  setoid_rewrite make_Stream_spec; trivial.
Qed.

Lemma inv_nested : forall x p, nested (inv_bounds x p).
Proof.
  intros x p k1 k2 Hk.
  setoid_rewrite inv_nth.
  set (k1' := Nat.max k1 (find_zeroless x p)).
  set (k2' := Nat.max k2 (find_zeroless x p)).
  assert (k2' >= k1')%nat as Hk' by (apply Nat.max_le_compat_r; assumption).
  assert (~ 0%Q ∈ x.[k1']) as HZ by apply find_zeroless_max.
  split;
    (apply QIinv_spec; [apply find_zeroless_max|]);
    apply bounds_nested, Hk'.
Qed.

Lemma Qmult_neg_neg : (forall a b, a < 0 -> b < 0 -> a * b > 0)%Q.
Proof.
  intros a b Ha Hb.
  setoid_replace (a * b)%Q with ((- a) * (- b))%Q by ring.
  apply Qmult_pos_pos; apply (Qlt_opp _ 0); trivial.
Qed.

Lemma zeroless_min_sq_pos : forall a b, (a <= b -> ~ 0%Q ∈ [a, b]Q -> Qmin (a * a) (b * b) > 0)%Q.
Proof.
  intros a b Hab H0.
  apply not_elem_iff in H0.
  destruct H0 as [H0|H0].
  - assert (b > 0)%Q as Hb by (eapply Qlt_le_trans; eassumption).
    apply Q.min_glb_lt; apply Qmult_pos_pos; assumption.
  - assert (a < 0)%Q as Ha by (eapply Qle_lt_trans; eassumption).
    apply Q.min_glb_lt; apply Qmult_neg_neg; assumption.
Qed.

Lemma zeroless_sq_lb :
  forall a b r s, r ∈ [a, b]Q -> s ∈ [a, b]Q -> ~ 0%Q ∈ [a, b]Q -> (r * s >= Qmin (a * a) (b * b))%Q.
Proof.
  intros a b r s [Hr1 Hr2] [Hs1 Hs2] H0.
  apply not_elem_iff in H0.
  destruct H0 as [H0|H0];
    [|apply Qlt_le_weak in H0];
    eapply Qle_trans, Qle_trans.
  - apply Q.le_min_l.
  - apply (Qmult_le_l _ s); eassumption.
  - apply Qmult_le_r; trivial.
    eapply Qlt_le_trans; eassumption.
  - apply Q.le_min_r.
  - apply (Qmult_le_neg_r s); eassumption.
  - rewrite Qmult_comm.
    apply Qmult_le_neg_r; trivial.
    eapply Qle_trans; eassumption.
Qed.

Lemma inv_convergent' :
  forall x p eps k,
    let n := find_zeroless x p in
    let c := Qmin (min x.[n] * min x.[n]) (max x.[n] * max x.[n]) in
      (width x.[k] < eps * c -> width (inv_bounds x p).[Nat.max k n] < eps)%Q.
Proof.
  intros x p eps k n c Hk.
  set (k' := Nat.max k n).
  set (a := min x.[k']).
  set (b := max x.[k']).
  assert (~ 0%Q ∈ x.[n]) as Hn by apply find_zeroless_spec.
  assert (c > 0)%Q as Hc by (apply zeroless_min_sq_pos; [apply bounds_consistent|apply Hn]).
  assert (k' >= n)%nat as Hk' by apply Nat.le_max_r.
  assert (a * b >= c)%Q as Hab by (apply zeroless_sq_lb; trivial; apply bounds_nested, Hk').
  assert (a * b > 0)%Q as Hab2 by (apply (Qlt_le_trans _ c); trivial).
  assert (~ a == 0 /\ ~ b == 0)%Q as Hab0
    by (split; contradict Hn; rewrite <- Hn; apply bounds_nested, Hk').
  rewrite inv_nth.
  rewrite Nat.max_l by trivial.
  apply
    (@QOrder.eq_lt _ (width x.[k'] / (a * b))%Q),
    (Qle_lt_trans _ (width x.[k'] / c)),
    (Qle_lt_trans _ (width x.[k] / c)).
  - unfold QIinv, width.
    cbn.
    subst a b.
    field; tauto.
  - setoid_rewrite Qmult_comm.
    apply Qmult_le_compat_r; [|apply bounds_width_nonneg].
    apply -> Qinv_le_contravar; trivial.
  - apply Qmult_le_compat_r.
    + apply bounds_width_decr, Nat.le_max_l.
    + apply Qlt_le_weak, Qinv_lt_0_compat, Hc.
  - apply Qlt_shift_div_r; trivial.
Qed.

Lemma inv_convergent : forall x p, convergent (inv_bounds x p).
Proof.
  intros x p eps Heps.
  set (n := find_zeroless x p).
  set (c := Qmin (min x.[n] * min x.[n]) (max x.[n] * max x.[n])).
  assert (~ 0%Q ∈ x.[n]) as Hn by apply find_zeroless_spec.
  assert (c > 0)%Q as Hc by (apply zeroless_min_sq_pos; [apply bounds_consistent|apply Hn]).
  assert (eps * c > 0)%Q as Hdelta by (apply Qmult_pos_pos; trivial).
  destruct (bounds_convergent x (eps * c)%Q Hdelta) as [k Hk].
  set (k' := Nat.max k n).
  exists k'.
  apply inv_convergent', Hk.
Defined.

Definition inv (x : {y : R | y =/= 0}) :=
  let (y, p) := x in make_R (inv_bounds y p) (inv_nested y p) (inv_convergent y p).

Notation "/ x" := (inv x) : R_scope.
Notation "x † p" := (exist _ x p) (at level 2, format "x  † p") : R_scope.

Lemma eqv_fromQ_r :
  forall (x y : R) n, (forall k, (k >= n)%nat -> exists r s, ((r ∈ x.[k] /\ s ∈ y.[k]) /\ r == s)%Q) -> x == y.
Proof.
  intros x y n H [[k Hk]|[k Hk]];
    set (k' := Nat.max k n);
    assert (k' >= n)%nat as Hk' by apply Nat.le_max_r;
    destruct (H k' Hk') as [r [s [[Hr Hs] HE]]];
    apply (bounds_nested_elem _ k) in Hr, Hs; try apply Nat.le_max_l;
    destruct Hr, Hs;
    contradict HE;
    [|apply Qnot_eq_sym];
    apply Qlt_not_eq;
    eapply Qle_lt_trans, Qlt_le_trans; eassumption.
Qed.

Lemma inv_in_nth :
  forall r (x : R) (p : x =/= 0) k, r ∈ x.[Nat.max k (find_zeroless x p)] -> (/ r)%Q ∈ (/ x †p).[k].
Proof.
  intros r x p k Hr.
  setoid_rewrite inv_nth.
  apply QIinv_spec; trivial.
  apply find_zeroless_max.
Qed.

Global Hint Resolve inv_in_nth | 1 : fromQ.

Definition eqv_subset {P : R -> Prop} (x y : {z : R | P z}) :=
  (let (x', _) := x in x') == (let (y', _) := y in y').

Lemma eqv_subset_refl : forall P (x : {y : R | P y}), eqv_subset x x.
Proof.
  intros P [x p].
  apply eqv_refl.
Qed.

Lemma eqv_subset_sym : forall P (x y : {z : R | P z}), eqv_subset x y -> eqv_subset y x.
Proof.
  intros P [x p] [y q].
  apply eqv_sym.
Qed.

Lemma eqv_subset_trans : forall P (x y z : {a : R | P a}), eqv_subset x y -> eqv_subset y z -> eqv_subset x z.
Proof.
  intros P [x p] [y q] [z r].
  apply eqv_trans.
Qed.

Add Parametric Relation P : ({x : R | P x}) (@eqv_subset P)
  reflexivity proved by (eqv_subset_refl P)
  symmetry proved by (eqv_subset_sym P)
  transitivity proved by (eqv_subset_trans P)
  as eqv_subset_rel.

Add Morphism inv with signature ((@eqv_subset (fun x => x =/= 0)) ==> eqv) as inv_mor.
Proof.
  intros [x p] [y q] H.
  unfold eqv_subset in H.
  set (n := Nat.max (find_zeroless x p) (find_zeroless y q)).
  apply (eqv_fromQ_r _ _ n).
  intros k Hk.
  rewrite eqv_common_point in H.
  destruct (H k) as [r [Hr Hs]].
  exists (/ r)%Q, (/ r)%Q.
  split; [|reflexivity].
  split;
    apply inv_in_nth;
    rewrite Nat.max_l; trivial;
    revert Hk; [apply Nat.max_lub_l|apply Nat.max_lub_r].
Qed.

Lemma find_zeroless_min : forall x p k, (k >= find_zeroless x p)%nat -> ~ (min x.[k] == 0)%Q.
Proof.
  intros x p k H.
  apply find_zeroless_ge in H.
  contradict H.
  rewrite <- H.
  apply bounds_min_elem.
Qed.

Lemma add_constraint : (forall k m n P, (k >= m -> P) -> (k >= Nat.max m n -> P))%nat.
Proof.
  intros k m n P H Hk.
  apply H.
  revert Hk.
  apply Nat.max_lub_l.
Qed.

Ltac fromQ_r :=
  repeat (let a := fresh "a" in let b := fresh "b" in intros a b; try (pose (find_zeroless_min _ a)); revert b);
  eapply eqv_fromQ_r;
  let k := fresh "k" in let Hk := fresh "Hk" in (
    intros k Hk;
    eexists; eexists;
    split; [split; auto with fromQ|
      repeat (rewrite (Nat.max_l k) by (eapply Nat.max_lub_r; apply Hk); revert Hk; apply add_constraint; intro Hk);
      try field;
      repeat (split; [eapply Nat.max_lub_r in Hk; eauto|]; revert Hk; apply add_constraint; intro Hk);
      eauto
    ]
  ).

Theorem inv_involutive : forall x p q, / (/ x †p) †q == x.
Proof. fromQ_r. Qed.

Theorem Q2R_inv : forall r p, (~ r == 0)%Q -> Q2R(/ r) == / (Q2R r) †p.
Proof. fromQ; trivial. Qed.

Theorem inv_1 : forall p, / 1 †p == 1.
Proof. fromQ. Qed.

Theorem inv_opp : forall x p q, / (- x) †q == - / x †p.
Proof. fromQ_r. Qed.

Theorem mult_inv_r : forall x p, x * / x †p == 1.
Proof. fromQ_r. Qed.

Theorem mult_inv_l : forall x p, / x †p * x == 1.
Proof. fromQ_r. Qed.

Theorem inv_mult : forall x y p q r, / (x * y) †r == (/x †p) * (/y †q).
Proof. fromQ_r. Qed.

Theorem inv_pos : forall x p, x > 0 <-> / x †p > 0.
Proof.
  intros x p.
  assert (x * / x †p > 0) as H2.
  - eapply lt_eqv_trans.
    + exact lt_0_1.
    + apply eqv_sym, mult_inv_r.
  - split; intro H.
    + eapply mult_pos_conv_l; eassumption.
    + eapply mult_pos_conv_r; eassumption.
Defined.

Lemma iff_sym : forall A B : Prop, (A <-> B) -> (B <-> A).
Proof. tauto. Defined.

Theorem inv_neg : forall x p, x < 0 <-> / x †p < 0.
Proof.
  intros x p.
  assert (-x =/= 0) as q by apply (opp_apart_0 x), p.
  eapply iff_trans, iff_trans, iff_trans.
  - apply opp_pos_neg.
  - apply (inv_pos (- x) q).
  - apply lt_mor_Proper; [reflexivity|].
    apply (inv_opp x p q).
  - apply iff_sym, opp_pos_neg.
Defined.

Theorem inv_apart_0 : forall x (p : x =/= 0), / x †p =/= 0.
Proof.
  intros x [p|p]; [left; apply inv_neg|right; apply inv_pos]; assumption.
Defined.

Lemma inv_lt_mult_pos : forall x y p q, x * y > 0 -> x < y <-> / y †q < / x †p.
Proof.
  intros x y p q H.
  apply (iff_trans _ ((x * y) * (/ y †q) < (x * y) * (/ x †p))).
  - apply lt_mor_Proper;
      [|rewrite (mult_comm x y)];
      rewrite mult_assoc, mult_inv_r, mult_1_r; reflexivity.
  - apply iff_sym, mult_lt_l, H.
Defined.

Theorem inv_lt_pos : forall x y p q, x > 0 -> y > 0 -> x < y <-> / y †q < / x †p.
Proof. intros. apply inv_lt_mult_pos, mult_pos_pos; assumption. Defined.

Theorem inv_lt_neg : forall x y p q, x < 0 -> y < 0 -> x < y <-> / y †q < / x †p.
Proof. intros. apply inv_lt_mult_pos, mult_neg_neg; assumption. Defined.

Theorem inv_atm_pos : forall x y p q, x > 0 -> y > 0 -> x <= y <-> / y †q <= / x †p.
Proof. intros. apply not_iff_compat, inv_lt_pos; assumption. Qed.

Theorem inv_atm_neg : forall x y p q, x < 0 -> y < 0 -> x <= y <-> / y †q <= / x †p.
Proof. intros. apply not_iff_compat, inv_lt_neg; assumption. Qed.

Theorem inv_apart : forall x y p q, x =/= y <-> / x †p =/= / y †q.
Proof.
  intros x y p q.
  apply (iff_trans _ ((x * y) * (/ y †q) =/= (x * y) * (/ x †p))), (iff_trans _ (/ y †q =/= / x †p)).
  - apply apart_mor_Proper;
      [|rewrite (mult_comm x y)];
      rewrite mult_assoc, mult_inv_r, mult_1_r; reflexivity.
  - apply iff_sym, mult_apart_l, mult_apart_0_iff.
    split; assumption.
  - apply apart_sym_iff.
Defined.

Theorem inv_eqv : forall x y p q, x == y <-> / x †p == / y †q.
Proof. intros. apply not_iff_compat, inv_apart. Qed.

Theorem inv_lt_iff :
  forall x y p q, / x †p < / y †q <-> (0 < y /\ y < x) \/ (y < x /\ x < 0) \/ (x < 0 /\ 0 < y).
Proof.
  intros x y p q.
  split; intro H.
  - destruct p as [p|p], q as [q|q].
    + right. left.
      split; trivial.
      eapply inv_lt_neg; eassumption.
    + right. right.
      split; assumption.
    + contradict H.
      apply lt_not_gt, (lt_trans _ 0);
        [apply inv_neg|apply inv_pos]; assumption.
    + left.
      split; trivial.
      eapply inv_lt_pos; eassumption.
  - destruct H as [H|[H|H]]; destruct H as [H1 H2].
    + apply inv_lt_pos; trivial.
      eapply lt_trans; eassumption.
    + apply inv_lt_neg; trivial.
      eapply lt_trans; eassumption.
    + apply (lt_trans _ 0);
        [apply inv_neg|apply inv_pos]; assumption.
Defined.

Definition div (x : R) (y : {z : R | z =/= 0}) := x * (/ y).
Infix "/" := div : R_scope.

Add Morphism div with signature (eqv ==> (@eqv_subset (fun x => x =/= 0)) ==> eqv) as div_mor.
Proof.
  intros x1 x2 Hx [y1 p1] [y2 p2] Hy.
  apply mult_mor_Proper; trivial.
  apply inv_mor_Proper; trivial.
Qed.

Lemma div_in_nth :
  forall r s (x y : R) (p : y =/= 0) k,
    r ∈ x.[k] -> s ∈ y.[Nat.max k (find_zeroless y p)] -> (r / s)%Q ∈ (x / y †p).[k].
Proof.
  intros r s x y p k Hr Hs.
  apply mult_in_nth; trivial.
  apply inv_in_nth; trivial.
Qed.
Global Hint Resolve div_in_nth | 1 : fromQ.

Theorem Q2R_div : forall r s p, ~ (s == 0)%Q -> Q2R (r / s) == (Q2R r) / (Q2R s) † p.
Proof. fromQ; trivial. Qed.

Theorem mult_div : forall x y p, (x * y) / y †p == x.
Proof. fromQ_r. Qed.

Theorem div_mult : forall x y p, (x / y †p) * y == x.
Proof. fromQ_r. Qed.

Theorem div_shift : forall x y z p, x / y †p == z <-> x == z * y.
Proof.
  intros x y z p.
  split; intro H.
  - rewrite <- H.
    apply eqv_sym, div_mult.
  - rewrite H.
    apply mult_div.
Qed.

Theorem div_lt : forall x y z p, z > 0 -> (x < y <-> x / z †p < y / z †p).
Proof. intros. apply mult_lt_r, inv_pos; trivial. Qed.

Theorem div_atm : forall x y z p, z > 0 -> (x <= y <-> x / z †p <= y / z †p).
Proof. intros. apply mult_atm_r, inv_pos; trivial. Qed.

Theorem div_lt_neg : forall x y z p, z < 0 -> (x < y <-> x / z †p > y / z †p).
Proof. intros. apply mult_lt_neg_r, inv_neg; trivial. Qed.

Theorem div_atm_neg : forall x y z p, z < 0 -> (x <= y <-> x / z †p >= y / z †p).
Proof. intros. apply mult_atm_neg_r, inv_neg; trivial. Qed.

Notation N2Z := Z.of_N.
Notation Z2Q := inject_Z.
Notation Z2N := Z.to_N.
Definition N2Q x := Z2Q (N2Z x).
Definition N2R x := Q2R (Z2Q (N2Z x)).
Definition Z2R x := Q2R (Z2Q x).

Theorem archimedes : forall x, exists n, N2R n > x.
Proof.
  intro x.
  exists (Z2N (Z.max (Qfloor (max x.[0]) + 1) 0)).
  unfold N2R.
  apply (atm_lt_trans _ (Q2R (max x.[0]))), (lt_atm_trans _ (Z2R (Qfloor (max x.[0]) + 1))); [| |rewrite Z2N.id].
  - apply bounds_correct.
  - apply Q2R_lt, Qlt_floor.
  - apply Q2R_atm.
    rewrite <- Zle_Qle.
    apply Z.le_max_l.
  - apply Z.le_max_r.
Defined.

Theorem archimedes_inv : forall x, x > 0 -> exists n p, / (N2R n) †p < x.
Proof.
  intros x H.
  assert (x =/= 0) as p by (right; trivial).
  assert (/ x †p > 0) as H2 by apply inv_pos, H.
  assert (/ x †p =/= 0) as q by (right; trivial).
  destruct (archimedes (/ x †p)) as [n Hn].
  exists n.
  assert (N2R n > 0) as Hn2 by (eapply lt_trans; eassumption).
  assert (N2R n =/= 0) as r by (right; trivial).
  exists r.
  apply (lt_eqv_trans _ (/ (/ x †p) †q)).
  - apply inv_lt_pos; trivial.
  - apply inv_involutive.
Defined.
