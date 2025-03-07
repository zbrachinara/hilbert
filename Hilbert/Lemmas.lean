import Hilbert.Geometry

open IncidenceGeometry

section IncidenceLemmas

variable {point} [geo : IncidenceGeometry point]

@[simp]
theorem line_of_left : x ∈ geo.line_of x y := by
  have := unique_line x y (geo.line_of x y) (by apply line_is_line)
  have := this.mpr rfl
  exact this.left

@[simp]
theorem line_of_right : y ∈ geo.line_of x y := by
  have := unique_line x y (geo.line_of x y) (by apply line_is_line)
  have := this.mpr rfl
  exact this.right

/--
If two lines are different, then there must be some point that they do not share.
-/
theorem unshared_point: ∀ l l' ∈ geo.line, l ≠ l' → ∃ p, p ∈ l ∧ p ∉ l' := by
  intro l l' l_line l'_line distinct_l
  have ⟨p, q, _, pl, ql⟩:= line_nonempty l l_line
  rcases Classical.em (p ∈ l') with pl' | pnl'
  · rcases Classical.em (q ∈ l') with ql' | qnl'
    · have := unique_line p q
      exfalso
      apply distinct_l
      calc
        _ = _ := (this l l_line).mp ⟨pl, ql⟩
        _ = _ := by symm; exact (this l' l'_line).mp ⟨pl', ql'⟩
    · exact ⟨q, ql, qnl'⟩
  · exact ⟨p, pl, pnl'⟩

namespace Colinear

theorem contains_left : Colinear x y z → x ∈ geo.line_of y z := by
  intro ⟨l, l_line, xl, yl, zl⟩
  have := unique_line y z l l_line
  have := this.mp ⟨yl, zl⟩
  subst l
  exact xl

theorem contains_right : Colinear x y z → z ∈ geo.line_of x y := by
  intro ⟨l, l_line, xl, yl, zl⟩
  have := unique_line x y l l_line
  have := this.mp ⟨xl, yl⟩
  subst l
  exact zl

theorem contains_middle : Colinear x y z → y ∈ geo.line_of x z := by
  intro ⟨l, l_line, xl, yl, zl⟩
  have := unique_line x z l l_line
  have := this.mp ⟨xl, zl⟩
  subst l
  exact yl

end Colinear

end IncidenceLemmas

open OrderGeometry

section OrderLemmas

variable {point} [geo : OrderGeometry point]

@[simp]
theorem trivial_nonorder : ∀ p p': point, ¬ ⟪p ∗ p' ∗ p⟫ := by
  intro p p' neg
  have ⟨contra, _⟩:= order_irreflexive neg
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

@[simp]
theorem on_segment {p a b: point} : p ∈ segment a b → p = a ∨ p = b ∨ ⟪a ∗ p ∗ b⟫ := by
  unfold segment
  simp [Set.insert, Set.member]
  intro pab
  cases pab
  case inl ab =>
    cases ab
    · left; assumption
    · right; left; assumption
  right; right; simp only [*]

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

theorem segment_in_line : ∀ p q : point, segment p q ⊆ line_of p q := by
  unfold Set.subset
  intro a b p pab
  rcases on_segment pab with pa | pb | pab
    <;> try {subst p; simp only [line_of_left, line_of_right]}
  have ⟨l, l_line, al, pl, bl⟩ := order_colinear pab
  have := unique_line a b l l_line
  have := this.mp ⟨al, bl⟩
  subst l
  exact pl

end OrderLemmas
