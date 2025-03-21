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
theorem line_unique {l : Line geo} (xny : x ≠ y) : x ∈ l → y ∈ l → line x y xny = l := by
  rw [<- and_imp]
  apply (line_uniqueness xny).mp

@[simp]
theorem line_of_left {xny : x ≠ y} : x ∈ line x y xny := ((line_uniqueness xny).mpr rfl).left
@[simp]
theorem line_of_right {xny : x ≠ y} : y ∈ line x y xny := ((line_uniqueness xny).mpr rfl).right
-- TODO figures out what causes infinite simp loop
-- @[simp]
theorem line_symmetric {xny : x ≠ y} : line x y xny = line y x xny.symm :=
  line_unique xny line_of_right line_of_left

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
    · exact ⟨q, line_of_right, qnl'⟩
  · exact ⟨p, line_of_left, pnl'⟩

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

theorem contains_left (ynz : y ≠ z) : Colinear x y z ↔ x ∈ line y z ynz := by
  constructor
  · intro ⟨l, xl, yl, zl⟩
    rw [line_unique ynz yl zl]
    exact xl
  · intro xl
    exact ⟨line y z ynz, xl, line_of_left, line_of_right⟩
theorem contains_middle (xnz : x ≠ z) : Colinear x y z ↔ y ∈ line x z xnz := by
  rw [left_symmetric]; exact contains_left xnz
theorem contains_right (xny : x ≠ y) : Colinear x y z ↔ z ∈ line x y xny := by
  rw [right_symmetric]; exact contains_middle xny

theorem left_transfers_line (xny : x ≠ y) (xnz : x ≠ z) (colinear : Colinear x y z):
  line x y xny = line x z xnz := by
  exact line_unique (xny) line_of_left ((contains_middle xnz).mp colinear)
theorem middle_transfers_line (ynx : y ≠ x) (ynz : y ≠ z) (colinear : Colinear x y z) :
  line y x ynx = line y z ynz := by
  rw [left_symmetric] at colinear; exact left_transfers_line ynx ynz colinear
theorem right_transfers_line (znx : z ≠ x) (zny : z ≠ y) (colinear : Colinear x y z) :
  line z x znx = line z y zny := by
  rw [right_symmetric] at colinear; exact middle_transfers_line znx zny colinear

end Colinear

theorem extralinear_left (ynz : y ≠ z) : x ∉ line y z ynz ↔ ¬ Colinear x y z := by
  constructor
  · apply mt; intro x; exact (Colinear.contains_left ynz).mp x
  · apply mt; intro x; exact (Colinear.contains_left ynz).mpr x
theorem extralinear_middle (xnz: x ≠ z) : y ∉ line x z xnz ↔ ¬ Colinear x y z := by
  rw [Colinear.left_symmetric]; exact extralinear_left xnz
theorem extralinear_right (xny : x ≠ y) : z ∉ line x y xny ↔ ¬ Colinear x y z := by
  rw [Colinear.right_symmetric]; exact extralinear_middle xny

end IncidenceLemmas

open OrderGeometry

section OrderLemmas

variable {geo} [OrderGeometry geo] {a b c : geo.point}

@[simp]
theorem on_segment : p ∈ segment a b ↔ p = a ∨ p = b ∨ ⟪a ∗ p ∗ b⟫ := by
  constructor
  · unfold segment
    simp [Set.insert, Set.member]
    intro pab
    cases pab
    case inl ab =>
      cases ab
      · left; assumption
      · right; left; assumption
    right; right; simp only [*]
  · unfold segment
    rintro (pa | pb | pab) <;> try subst p
    · left; simp [Set.insert]; left; rfl
    · left; simp [Set.insert]; right; rfl
    · right; exact pab

namespace PointOrder.between

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
theorem trivial_segment : ∀ p : geo.point, segment p p = {p} := by
  intro p
  unfold segment
  simp only [trivial_nonorder, and_false, Set.empty_def, Set.union_empty]
  apply Set.ext -- TODO might need proof automation for bigger cases
  intro p'
  simp [Set.insert, Set.member]
  exact id

@[simp]
theorem order_symmetric': ∀ p q r : geo.point, ⟪p ∗ q ∗ r⟫ ↔ ⟪r ∗ q ∗ p⟫ := by
  intros
  constructor <;> { intro x; exact order_symmetric x }

theorem segment_has_left : a ∈ segment a b := by
  unfold segment
  rw [Set.mem_union]
  left
  simp only [Set.insert]
  left
  rfl

theorem segment_has_right : b ∈ segment a b := by
  unfold segment
  rw [Set.mem_union]
  left
  simp only [Set.insert, Set.member]
  right
  rfl

@[simp]
theorem segment_symm : ∀ p q : geo.point, segment p q = segment q p := by
  intro p q
  unfold segment
  congr 1
  · apply Set.ext
    intro x
    simp [Set.insert, Set.member]
    exact Or.comm
  · apply Set.ext
    simp [Set.member]

variable [IncidenceGeometry geo]

namespace PointOrder.between

theorem contains_left (betw : ⟪a ∗ b ∗ c⟫) : a ∈ line b c betw.right_irrefl := by
  apply (Colinear.contains_left betw.right_irrefl).mp
  exact order_colinear betw
theorem contains_right (betw : ⟪a ∗ b ∗ c⟫) : c ∈ line a b betw.left_irrefl := by
  apply (Colinear.contains_right betw.left_irrefl).mp
  exact order_colinear betw
theorem contains_middle (betw : ⟪a ∗ b ∗ c⟫) : b ∈ line a c betw.cross_irrefl := by
  apply (Colinear.contains_middle betw.cross_irrefl).mp
  exact order_colinear betw

end PointOrder.between

theorem segment_in_line {anb : a ≠ b} : segment a b ⊆ line a b anb := by
  unfold Set.subset
  intro a apq
  rcases on_segment.mp apq with ap | aq | apq <;> try subst a
  · exact line_of_left
  · exact line_of_right
  have ⟨l, pl, al, ql⟩ := order_colinear apq
  rw [line_unique anb pl ql]
  exact al

end OrderLemmas
