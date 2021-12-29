Require Import Coq.QArith.QArith.
Require Import Coq.QArith.QOrderedType.
Require Import Coq.Lists.Streams.
Require Import Coq.Logic.ChoiceFacts.
Require Import Coq.Logic.ConstructiveEpsilon.
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
Notation "[ a , b ]Q" := (make_Qinterval a b) (at level 0) : QI_scope.
Notation "s .[ k ]" := (Str_nth k s) (at level 2, left associativity, format "s .[ k ]") : QI_scope.

Coercion QIcontents : Qinterval >-> set.

Definition width (xs : Qinterval) : Q :=
  max xs - min xs.

Record R : Set := make {
  bounds : Stream Qinterval;
  bounds_min_le_max : forall k, (min bounds.[k] <= max bounds.[k])%Q;
  bounds_stricter_min : forall k1 k2, (k2 >= k1)%nat -> (min bounds.[k2] >= min bounds.[k1])%Q;
  bounds_stricter_max : forall k1 k2, (k2 >= k1)%nat -> (max bounds.[k2] <= max bounds.[k1])%Q;
  bounds_convergent : (forall eps, eps > 0 -> exists k, width bounds.[k] < eps)%Q;
}.

Declare Scope R_scope.
Delimit Scope R_scope with R.
Bind Scope R_scope with R.
Local Open Scope R_scope.

Coercion bounds : R >-> Stream.

Lemma bounds_consistent : forall (x : R) k1 k2, (min x.[k1] <= max x.[k2])%Q.
Proof.
  intros x k1 k2.
  set (k3 := Nat.max k1 k2).
  apply (Qle_trans _ (min x.[k3])), (Qle_trans _ (max x.[k3])).
  - apply bounds_stricter_min, Nat.le_max_l.
  - apply bounds_min_le_max.
  - apply bounds_stricter_max, Nat.le_max_r.
Qed.

Lemma bounds_min_elem : forall (x : R) k, min x.[k] ∈ x.[k].
Proof.
  intros x k.
  split; try q_order.
  apply bounds_min_le_max.
Qed.

Lemma bounds_max_elem : forall (x : R) k, max x.[k] ∈ x.[k].
Proof.
  intros x k.
  split; try q_order.
  apply bounds_min_le_max.
Qed.

Lemma bounds_nested_elem : forall (x : R) k1 k2 r, (k2 >= k1)%nat -> r ∈ x.[k2] -> r ∈ x.[k1].
Proof.
  intros x k1 k2 r Hk [H1 H2].
  pose (bounds_stricter_min x k1 k2 Hk).
  pose (bounds_stricter_max x k1 k2 Hk).
  split; q_order.
Qed.

Lemma bounds_width_decr : forall (x : R) k1 k2, (k2 >= k1)%nat -> (width x.[k2] <= width x.[k1])%Q.
Proof.
  intros x k1 k2 Hk.
  apply Qplus_le_compat.
  - apply bounds_stricter_max, Hk.
  - apply Qopp_le_compat, bounds_stricter_min, Hk.
Qed.

Definition QIlt (rs ss : Qinterval) := (max rs < min ss)%Q.

Infix "<" := QIlt : QI_scope.
Notation "x > y" := (QIlt y x) (only parsing) : QI_scope.

Definition lt (x y : R) :=
  exists k, (x.[k] < y.[k])%QI.

Infix "<" := lt : R_scope.
Notation "x > y" := (lt y x) (only parsing) : R_scope.

Theorem lt_trans : forall x y z, x < y -> y < z -> x < z.
Proof.
  intros x y z [k1 H1] [k2 H2].
  set (k3 := Nat.max k1 k2).
  exists k3.
  apply (Qle_lt_trans _ (max x.[k1])), (Qlt_trans _ (min y.[k1])), (Qle_lt_trans _ (max y.[k2])), (Qlt_le_trans _ (min z.[k2]));
    trivial.
  - apply bounds_stricter_max, Nat.le_max_l.
  - apply bounds_consistent.
  - apply bounds_stricter_min, Nat.le_max_r.
Defined.

Theorem lt_irrefl : forall x, ~ x < x.
Proof.
  intros x [k H].
  apply Qlt_not_le in H.
  apply H, bounds_min_le_max.
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
  apply (Qle_lt_trans (width z.[k3])) in Hk2; [|apply bounds_width_decr, Nat.le_max_r].
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
  ExcludedMiddle -> forall P : Prop, ~ ~ P -> P.
Proof.
  intros EM P H.
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

Definition sig2bool {A B : Prop} (u : {A} + {B}) : bool := if u then true else false.

Theorem compare_compatible :
  forall x1 x2, x1 == x2 -> forall y1 y2, y1 == y2 -> forall p1 p2,
    sig2bool (compare x1 y1 p1) = sig2bool (compare x2 y2 p2).
Proof.
  intros x1 x2 Hx y1 y2 Hy p1 p2.
  destruct (compare x1 y1 p1) as [H1|H1];
    destruct (compare x2 y2 p2) as [H2|H2]; trivial;
    cbn; rewrite Hx, Hy in H1;
    contradict H2;
    apply lt_not_gt, H1.
Qed.
