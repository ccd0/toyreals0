Require Import Coq.QArith.QArith.
Require Import Coq.QArith.QOrderedType.
Require Import Coq.QArith.Qminmax.
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
Notation "[ a , b ]Q" := (make_Qinterval a b) (at level 0, format "[ a ,  b ]Q") : QI_scope.
Notation "s .[ k ]" := (Str_nth k s) (at level 2, left associativity, format "s .[ k ]") : QI_scope.

Coercion QIcontents : Qinterval >-> set.

Definition width (xs : Qinterval) : Q :=
  max xs - min xs.

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

Definition nonempty (x : Stream Qinterval) :=
  forall k, (min x.[k] <= max x.[k])%Q.

Definition nested (x : Stream Qinterval) :=
  forall k1 k2, (k2 >= k1)%nat -> (min x.[k2] >= min x.[k1] /\ max x.[k2] <= max x.[k1])%Q.

Definition convergent (x : Stream Qinterval) :=
  (forall eps, eps > 0 -> exists k, width x.[k] < eps)%Q.

Record R : Set := make_R {
  bounds : Stream Qinterval;
  bounds_nonempty : nonempty bounds;
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
  set (k3 := Nat.max k1 k2).
  apply (Qle_trans _ (min x.[k3])), (Qle_trans _ (max x.[k3])).
  - apply bounds_nested, Nat.le_max_l.
  - apply bounds_nonempty.
  - apply bounds_nested, Nat.le_max_r.
Qed.

Lemma bounds_min_elem : forall (x : R) k, min x.[k] ∈ x.[k].
Proof.
  intros x k.
  split; try q_order.
  apply bounds_nonempty.
Qed.

Lemma bounds_max_elem : forall (x : R) k, max x.[k] ∈ x.[k].
Proof.
  intros x k.
  split; try q_order.
  apply bounds_nonempty.
Qed.

Lemma bounds_nested_elem : forall (x : R) k1 k2 r, (k2 >= k1)%nat -> r ∈ x.[k2] -> r ∈ x.[k1].
Proof.
  intros x k1 k2 r Hk [H1 H2].
  destruct (bounds_nested x k1 k2 Hk).
  split; q_order.
Qed.

Lemma bounds_width_decr : forall (x : R) k1 k2, (k2 >= k1)%nat -> (width x.[k2] <= width x.[k1])%Q.
Proof.
  intros x k1 k2 Hk.
  apply Qplus_le_compat.
  - apply bounds_nested, Hk.
  - apply Qopp_le_compat, bounds_nested, Hk.
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
  - apply bounds_nested, Nat.le_max_l.
  - apply bounds_consistent.
  - apply bounds_nested, Nat.le_max_r.
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

Definition Markov :=
  forall P : nat -> Prop, (forall n, P n \/ ~ P n) -> ~ (forall n, ~ P n) -> exists n, P n.

Lemma markov_sig_dn :
  Markov -> forall P : nat -> Prop, (forall n, {P n} + {~ P n}) -> ~ ~ (exists n, P n) -> exists n, P n.
Proof.
  firstorder.
Qed.

Theorem markov_not_atm_gt : Markov -> forall x y, ~ x <= y -> x > y.
Proof.
  intros HM x y H.
  apply markov_sig_dn; trivial.
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
  Markov -> forall w x y z, ~ ~ (w < x \/ y < z) -> w < x \/ y < z.
Proof.
  intros HM w x y z H.
  apply ex_or_or_ex, markov_sig_dn; trivial.
  - intro n.
    apply or_dec; apply QIlt_dec.
  - apply (dn_imp_dn (w < x \/ y < z)); trivial.
    apply or_ex_ex_or.
Qed.

Definition Q2R_bounds (r : Q) := make_Stream (fun k => [r, r]Q).

Lemma Q2R_bounds_spec : forall r k, (Q2R_bounds r).[k] = [r, r]Q.
Proof.
  intros r k.
  unfold Q2R_bounds.
  rewrite make_Stream_spec.
  trivial.
Qed.

Lemma Q2R_nonempty : forall r, nonempty (Q2R_bounds r).
Proof.
  intros r k.
  rewrite Q2R_bounds_spec.
  cbn.
  q_order.
Qed.

Lemma Q2R_nested : forall r, nested (Q2R_bounds r).
Proof.
  intros r k1 k2 Hk.
  repeat rewrite Q2R_bounds_spec.
  split; q_order.
Qed.

Lemma Q2R_convergent : forall r, convergent (Q2R_bounds r).
Proof.
  intros r eps Heps.
  exists 0%nat.
  rewrite Q2R_bounds_spec.
  setoid_rewrite Qplus_opp_r.
  exact Heps.
Defined.

Definition Q2R (r : Q) := make_R (Q2R_bounds r) (Q2R_nonempty r) (Q2R_nested r) (Q2R_convergent r).

Theorem Q2R_lt : forall r s, (r < s)%Q <-> Q2R r < Q2R s.
Proof.
  intros r s.
  split; intro H.
  - exists 0%nat.
    setoid_rewrite Q2R_bounds_spec.
    exact H.
  - destruct H as [k H].
    setoid_rewrite Q2R_bounds_spec in H.
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

Theorem bounds_correct : forall (x : R) k, Q2R (min x.[k]) <= x /\ x <= Q2R (max x.[k]).
Proof.
  intros x k.
  split; intros [k2 HN];
    setoid_rewrite Q2R_bounds_spec in HN;
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
