import Hilbert.Geometry

section BaseLemmas

variable {geo : Geometry}

@[simp]
theorem mem_line {p : geo.point} {l : Line geo} : p ∈ l.val ↔ p ∈ l := ⟨id, id⟩

namespace Colinear

@[simp]
theorem left_symmetric {x y z : geo.point} : Colinear x y z ↔ Colinear y x z := by
  constructor ; repeat {
    rintro ⟨l, xl, yl, zl⟩
    exact ⟨l, yl, xl, zl⟩
  }

@[simp]
theorem right_symmetric {x y z : geo.point} : Colinear x y z ↔ Colinear x z y := by
  constructor ; repeat {
    rintro ⟨l, xl, yl, zl⟩
    exact ⟨l, xl, zl, yl⟩
  }

@[simp]
theorem cross_symmetric {x y z : geo.point} : Colinear x y z ↔ Colinear z y x := by
  constructor ; repeat {
    rintro ⟨l, xl, yl, zl⟩
    exact ⟨l, zl, yl, xl⟩
  }

end Colinear

end BaseLemmas

open IncidenceGeometry

section IncidenceLemmas

variable {geo} [igeo : IncidenceGeometry geo] {x y z : geo.point}

@[simp]
theorem line_unique {l : Line geo} (xny : x ≠ y) : x ∈ l → y ∈ l → line x y = l := by
  rw [<- and_imp]
  apply (line_uniqueness xny).mp

@[simp]
theorem line_of_left (xny : x ≠ y) : x ∈ line x y := ((line_uniqueness xny).mpr rfl).left
@[simp]
theorem line_of_right (xny : x ≠ y) : y ∈ line x y := ((line_uniqueness xny).mpr rfl).right
-- TODO figures out what causes infinite simp loop
-- @[simp]
theorem line_symmetric (xny : x ≠ y) : line x y = line y x :=
  line_unique xny (line_of_right xny.symm) (line_of_left xny.symm)

/--
If two lines are different, then there must be some point that they do not share.
-/
theorem unshared_point: ∀ l l' : Line geo, l ≠ l' → ∃ p, p ∈ l ∧ p ∉ l' := by
  intro l l' distinct_l
  have ⟨p, q, pnq, lpq⟩:= line_nonempty l
  subst lpq
  rcases Classical.em (p ∈ l') with pl' | pnl'
  · rcases Classical.em (q ∈ l') with ql' | qnl'
    · exfalso
      apply distinct_l
      exact line_unique pnq pl' ql'
    · exact ⟨q, line_of_right pnq, qnl'⟩
  · exact ⟨p, line_of_left pnq, pnl'⟩

/--
  Consequence of non-triviality of the geometry -- For any line, a point must lie outside that line.
-/
theorem not_colinear_to (l : Line geo) : ∃ p, p ∉ l := by
  apply Classical.byContradiction
  rw [not_exists]
  intro assume_trivial
  have ⟨a, b, c, noncolinear⟩ := igeo.nontrivial
  have := assume_trivial a
  have := assume_trivial b
  have := assume_trivial c
  rw [Classical.not_not] at *
  apply noncolinear
  exists l

namespace Colinear

-- TODO use macro to automate these proofs
-- TODO split the iff

theorem contains_left (ynz : y ≠ z) : Colinear x y z ↔ x ∈ line y z := by
  constructor
  · intro ⟨l, xl, yl, zl⟩
    rw [line_unique ynz yl zl]
    exact xl
  · intro xl
    exact ⟨line y z, xl, line_of_left ynz, line_of_right ynz⟩
theorem contains_middle (xnz : x ≠ z) : Colinear x y z ↔ y ∈ line x z := by
  rw [left_symmetric]; exact contains_left xnz
theorem contains_right (xny : x ≠ y) : Colinear x y z ↔ z ∈ line x y := by
  rw [right_symmetric]; exact contains_middle xny

theorem left_transfers_line (xny : x ≠ y) (xnz : x ≠ z) (colinear : Colinear x y z):
  line x y = line x z := by
  exact line_unique xny (line_of_left xnz) ((contains_middle xnz).mp colinear)
theorem middle_transfers_line (ynx : y ≠ x) (ynz : y ≠ z) (colinear : Colinear x y z) :
  line y x = line y z := by
  rw [left_symmetric] at colinear; exact left_transfers_line ynx ynz colinear
theorem right_transfers_line (znx : z ≠ x) (zny : z ≠ y) (colinear : Colinear x y z) :
  line z x = line z y := by
  rw [right_symmetric] at colinear; exact middle_transfers_line znx zny colinear

end Colinear

theorem line_exchange_left (ynz : y ≠ z) (xnz : x ≠ z) : x ∈ line y z → y ∈ line x z := by
  rw [<- Colinear.contains_left xnz, Colinear.contains_middle ynz]; exact id
theorem line_exchange_right (ynz : y ≠ z) (xny : x ≠ y) : x ∈ line y z → z ∈ line x y := by
  rw [line_symmetric]; apply line_exchange_left ynz.symm xny; exact ynz

theorem extralinear_left (ynz : y ≠ z) : x ∉ line y z ↔ ¬ Colinear x y z := by
  constructor
  · apply mt; intro x; exact (Colinear.contains_left ynz).mp x
  · apply mt; intro x; exact (Colinear.contains_left ynz).mpr x
theorem extralinear_middle (xnz: x ≠ z) : y ∉ line x z ↔ ¬ Colinear x y z := by
  rw [Colinear.left_symmetric]; exact extralinear_left xnz
theorem extralinear_right (xny : x ≠ y) : z ∉ line x y ↔ ¬ Colinear x y z := by
  rw [Colinear.right_symmetric]; exact extralinear_middle xny

end IncidenceLemmas

open OrderGeometry

section OrderLemmas

variable {geo} [OrderGeometry geo] {a b c : geo.point}

@[simp]
theorem on_segment : p ∈ segment a b ↔ p = a ∨ p = b ∨ ⟪a ∗ p ∗ b⟫ := by
  constructor
  · intro pab
    cases pab
    case inl ab =>
      cases ab
      · left; assumption
      · right; left; assumption
    right; right; assumption
  · rintro (pa | pb | pab) <;> try subst p
    · left; simp [Set.insert]; left; rfl
    · left; simp [Set.insert]; right; rfl
    · right; exact pab

@[simp]
theorem on_locus : p ∈ Segment.locus.as_locus (segment a b) ↔ p ∈ segment a b := by
  rw [on_segment, segment]
  simp only [Segment.locus, Set.mem_union, Set.insert, Set.member]
  rw [or_assoc]
  exact Eq.to_iff rfl

namespace PointOrder.between

theorem colinear (abc : ⟪a ∗ b ∗ c⟫) : Colinear a b c := OrderGeometry.order_colinear abc

@[simp]
theorem left_irrefl (abc : ⟪a ∗ b ∗ c⟫) : a ≠ b := (order_irreflexive abc).right.right
@[simp]
theorem right_irrefl (abc : ⟪a ∗ b ∗ c⟫) : b ≠ c := (order_irreflexive abc).right.left
@[simp]
theorem cross_irrefl (abc : ⟪a ∗ b ∗ c⟫) : a ≠ c := (order_irreflexive abc).left
theorem symm : ⟪a ∗ b ∗ c⟫ → ⟪c ∗ b ∗ a⟫ := order_symmetric

theorem exclusive_left : ⟪a ∗ b ∗ c⟫ → ¬ ⟪b ∗ a ∗ c⟫ := by
  intro abc
  have := order_colinear abc
  have := (order_unique abc.left_irrefl abc.right_irrefl abc.cross_irrefl this).reduce_left abc
  exact this.left

theorem exclusive_right : ⟪a ∗ b ∗ c⟫ → ¬ ⟪a ∗ c ∗ b⟫ := by
  intro abc
  have := order_colinear abc
  have := (order_unique abc.left_irrefl abc.right_irrefl abc.cross_irrefl this).reduce_left abc
  exact this.right

theorem outside_segment : ⟪a ∗ b ∗ c⟫ → a ∉ segment b c := by
  intro abc anbc
  rcases on_segment.mp anbc with ab | ac | anbc
  · exact abc.left_irrefl ab
  · exact abc.cross_irrefl ac
  exfalso
  exact abc.exclusive_left anbc

end PointOrder.between

@[simp]
theorem trivial_nonorder : ∀ p p': geo.point, ¬ ⟪p ∗ p' ∗ p⟫ := by
  intro p p' neg
  have ⟨contra, _⟩ := order_irreflexive neg
  exact contra rfl

@[simp]
theorem trivial_segment : ∀ p : geo.point, segment p p = ({p} : Locus _) := by
  intro p
  simp only [segment, Segment.locus, trivial_nonorder, Set.empty_def, Set.union_empty]
  apply Set.ext -- TODO might need proof automation for bigger cases
  intro p'
  simp [Set.insert, Set.member]
  exact id

@[simp]
theorem order_symmetric': ∀ p q r : geo.point, ⟪p ∗ q ∗ r⟫ ↔ ⟪r ∗ q ∗ p⟫ := by
  intros
  constructor <;> { intro x; exact order_symmetric x }

theorem segment_has_left : a ∈ segment a b := by rw [on_segment]; left; rfl
theorem segment_has_right : b ∈ segment a b := by rw [on_segment]; right; left; rfl

@[simp]
theorem segment_symm : ∀ p q : geo.point, (segment p q : Locus geo) = segment q p := by
  intro p q
  apply Set.ext
  intro x
  simp only [segment, Segment.locus, Set.mem_union, order_symmetric', Set.insert, Set.member]
  rw [@or_comm (x = p), <- eq_iff_iff]
  rfl

variable [IncidenceGeometry geo]

namespace PointOrder.between

theorem contains_left (betw : ⟪a ∗ b ∗ c⟫) : a ∈ line b c := by
  apply (Colinear.contains_left betw.right_irrefl).mp
  exact order_colinear betw
theorem contains_right (betw : ⟪a ∗ b ∗ c⟫) : c ∈ line a b := by
  apply (Colinear.contains_right betw.left_irrefl).mp
  exact order_colinear betw
theorem contains_middle (betw : ⟪a ∗ b ∗ c⟫) : b ∈ line a c := by
  apply (Colinear.contains_middle betw.cross_irrefl).mp
  exact order_colinear betw

end PointOrder.between

theorem segment_in_line (anb : a ≠ b) : segment a b ⊆ (line a b : Locus geo) := by
  unfold Set.subset
  intro a apq
  rcases on_segment.mp apq with ap | aq | apq <;> try subst a
  · exact line_of_left anb
  · exact line_of_right anb
  have ⟨l, pl, al, ql⟩ := order_colinear apq
  rw [line_unique anb pl ql]
  exact al

end OrderLemmas
