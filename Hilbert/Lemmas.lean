import Hilbert.Geometry

section BaseLemmas

variable {point} [geo : Geometry point]

@[simp]
theorem mem_line {p : point} {l : Line point} : p ∈ l.val ↔ p ∈ l := ⟨id, id⟩

end BaseLemmas

open IncidenceGeometry

section IncidenceLemmas

variable {point} [geo : IncidenceGeometry point]

@[simp]
theorem line_unique {l : Line point} (xny : x ≠ y) : x ∈ l → y ∈ l → line x y xny = l := by
  rw [<- and_imp]
  apply (line_uniqueness xny).mp

@[simp]
theorem line_of_left {xny : x ≠ y} : x ∈ geo.line x y xny := ((line_uniqueness xny).mpr rfl).left
@[simp]
theorem line_of_right {xny : x ≠ y} : y ∈ geo.line x y xny := ((line_uniqueness xny).mpr rfl).right
-- TODO figures out what causes infinite simp loop
-- @[simp]
theorem line_symmetric {xny : x ≠ y} : geo.line x y xny = line y x xny.symm :=
  line_unique xny line_of_right line_of_left

/--
If two lines are different, then there must be some point that they do not share.
-/
theorem unshared_point: ∀ l l' : Line point, l ≠ l' → ∃ p, p ∈ l ∧ p ∉ l' := by
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
theorem not_colinear_to (l : Line point) : ∃ p, p ∉ l := by
  apply Classical.byContradiction
  rw [not_exists]
  intro assume_trivial
  have ⟨a, b, c, noncolinear⟩ := @nontrivial point geo
  have := assume_trivial a
  have := assume_trivial b
  have := assume_trivial c
  rw [Classical.not_not] at *
  apply noncolinear
  exists l

namespace Colinear

@[simp]
theorem left_symmetric {x y z : point} : Colinear x y z ↔ Colinear y x z := by
  constructor ; repeat {
    rintro ⟨l, xl, yl, zl⟩
    exact ⟨l, yl, xl, zl⟩
  }

@[simp]
theorem right_symmetric {x y z : point} : Colinear x y z ↔ Colinear x z y := by
  constructor ; repeat {
    rintro ⟨l, xl, yl, zl⟩
    exact ⟨l, xl, zl, yl⟩
  }

@[simp]
theorem cross_symmetric {x y z : point} : Colinear x y z ↔ Colinear z y x := by
  constructor ; repeat {
    rintro ⟨l, xl, yl, zl⟩
    exact ⟨l, zl, yl, xl⟩
  }

-- TODO use macro to automate these proofs
-- TODO split the iff

theorem contains_left (ynz : y ≠ z) : Colinear x y z ↔ x ∈ geo.line y z ynz := by
  constructor
  · intro ⟨l, xl, yl, zl⟩
    rw [line_unique ynz yl zl]
    exact xl
  · intro xl
    exact ⟨line y z ynz, xl, line_of_left, line_of_right⟩
theorem contains_middle (xnz : x ≠ z) : Colinear x y z ↔ y ∈ geo.line x z xnz := by
  rw [left_symmetric]; exact contains_left xnz
theorem contains_right (xny : x ≠ y) : Colinear x y z ↔ z ∈ geo.line x y xny := by
  rw [right_symmetric]; exact contains_middle xny

theorem left_transfers_line (xny : x ≠ y) (xnz : x ≠ z) (colinear : Colinear x y z):
  geo.line x y xny = geo.line x z xnz := by
  exact line_unique (xny) line_of_left ((contains_middle xnz).mp colinear)
theorem middle_transfers_line (ynx : y ≠ x) (ynz : y ≠ z) (colinear : Colinear x y z) :
  geo.line y x ynx = geo.line y z ynz := by
  rw [left_symmetric] at colinear; exact left_transfers_line ynx ynz colinear
theorem right_transfers_line (znx : z ≠ x) (zny : z ≠ y) (colinear : Colinear x y z) :
  geo.line z x znx = geo.line z y zny := by
  rw [right_symmetric] at colinear; exact middle_transfers_line znx zny colinear

end Colinear

theorem extralinear_left (bnc : b ≠ c) : a ∉ geo.line b c bnc ↔ ¬ Colinear a b c := by
  constructor
  · apply mt; intro x; exact (Colinear.contains_left bnc).mp x
  · apply mt; intro x; exact (Colinear.contains_left bnc).mpr x
theorem extralinear_middle (anc: a ≠ c) : b ∉ geo.line a c anc ↔ ¬ Colinear a b c := by
  rw [Colinear.left_symmetric]; exact extralinear_left anc
theorem extralinear_right (anb : a ≠ b) : c ∉ geo.line a b anb ↔ ¬ Colinear a b c := by
  rw [Colinear.right_symmetric]; exact extralinear_middle anb

end IncidenceLemmas

open OrderGeometry

section OrderLemmas

variable {point} [geo : OrderGeometry point]

@[simp]
theorem on_segment {p a b: point} : p ∈ segment a b ↔ p = a ∨ p = b ∨ ⟪a ∗ p ∗ b⟫ := by
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
theorem left_irrefl {a b c : point} (abc : ⟪a ∗ b ∗ c⟫) : a ≠ b :=
  (order_irreflexive abc).right.right
@[simp]
theorem right_irrefl {a b c : point} (abc : ⟪a ∗ b ∗ c⟫) : b ≠ c :=
  (order_irreflexive abc).right.left
@[simp]
theorem cross_irrefl {a b c : point} (abc : ⟪a ∗ b ∗ c⟫) : a ≠ c :=
  (order_irreflexive abc).left

theorem symm {a b c : point} : ⟪a ∗ b ∗ c⟫ → ⟪c ∗ b ∗ a⟫ := order_symmetric

theorem contains_left (betw : ⟪a ∗ b ∗ c⟫) : a ∈ geo.line b c betw.right_irrefl := by
  apply (Colinear.contains_left betw.right_irrefl).mp
  exact order_colinear betw
theorem contains_right (betw : ⟪a ∗ b ∗ c⟫) : c ∈ geo.line a b betw.left_irrefl := by
  apply (Colinear.contains_right betw.left_irrefl).mp
  exact order_colinear betw
theorem contains_middle (betw : ⟪a ∗ b ∗ c⟫) : b ∈ geo.line a c betw.cross_irrefl := by
  apply (Colinear.contains_middle betw.cross_irrefl).mp
  exact order_colinear betw

theorem exclusive_left {a b c : point}: ⟪a ∗ b ∗ c⟫ → ¬ ⟪b ∗ a ∗ c⟫ := by
  intro abc
  have := order_colinear abc
  have := (order_unique abc.left_irrefl abc.right_irrefl abc.cross_irrefl this).reduce_left abc
  exact this.left

theorem exclusive_right {a b c : point} : ⟪a ∗ b ∗ c⟫ → ¬ ⟪a ∗ c ∗ b⟫ := by
  intro abc
  have := order_colinear abc
  have := (order_unique abc.left_irrefl abc.right_irrefl abc.cross_irrefl this).reduce_left abc
  exact this.right

theorem outside_segment {a b c : point} : ⟪a ∗ b ∗ c⟫ → a ∉ segment b c := by
  intro abc anbc
  rcases on_segment.mp anbc with ab | ac | anbc
  · exact abc.left_irrefl ab
  · exact abc.cross_irrefl ac
  exfalso
  exact abc.exclusive_left anbc

end PointOrder.between

@[simp]
theorem trivial_nonorder : ∀ p p': point, ¬ ⟪p ∗ p' ∗ p⟫ := by
  intro p p' neg
  have ⟨contra, _⟩ := order_irreflexive neg
  exact contra rfl

@[simp]
theorem trivial_segment : ∀ p : point, segment p p = {p} := by
  intro p
  unfold segment
  simp only [trivial_nonorder, and_false, Set.empty_def, Set.union_empty]
  apply Set.ext -- TODO might need proof automation for bigger cases
  intro p'
  simp [Set.insert, Set.member]
  exact id

@[simp]
theorem order_symmetric': ∀ p q r : point, ⟪p ∗ q ∗ r⟫ ↔ ⟪r ∗ q ∗ p⟫ := by
  intros
  constructor <;> { intro x; exact order_symmetric x }

theorem segment_has_left {a b : point} : a ∈ segment a b := by
  unfold segment
  rw [Set.mem_union]
  left
  simp only [Set.insert]
  left
  rfl

theorem segment_has_right {a b : point} : b ∈ segment a b := by
  unfold segment
  rw [Set.mem_union]
  left
  simp only [Set.insert, Set.member]
  right
  rfl

@[simp]
theorem segment_symm : ∀ p q : point, segment p q = segment q p := by
  intro p q
  unfold segment
  congr 1
  · apply Set.ext
    intro x
    simp [Set.insert, Set.member]
    exact Or.comm
  · apply Set.ext
    simp [Set.member]

theorem segment_in_line {p q : point} {pnq : p ≠ q} : segment p q ⊆ line p q pnq := by
  unfold Set.subset
  intro a apq
  rcases on_segment.mp apq with ap | aq | apq <;> try subst a
  · exact line_of_left
  · exact line_of_right
  have ⟨l, pl, al, ql⟩ := order_colinear apq
  rw [line_unique pnq pl ql]
  exact al

end OrderLemmas
