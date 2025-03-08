import Hilbert.Geometry

section BaseLemmas

variable {point} [geo : Geometry point]

@[simp]
theorem mem_line_locus {p : point} {l : Line point} : p ∈ l ↔ p ∈ l.val := ⟨id, id⟩

end BaseLemmas

open IncidenceGeometry

section IncidenceLemmas

variable {point} [geo : IncidenceGeometry point]

@[simp]
theorem line_of_left : x ∈ geo.line_of x y := by
  have := unique_line x y (geo.line_of x y)
  have := this.mpr rfl
  exact this.left

@[simp]
theorem line_of_right : y ∈ geo.line_of x y := by
  have := unique_line x y (geo.line_of x y)
  have := this.mpr rfl
  exact this.right

/--
If two lines are different, then there must be some point that they do not share.
-/
theorem unshared_point: ∀ l l' : Line point, l ≠ l' → ∃ p, p ∈ l ∧ p ∉ l' := by
  intro l l' distinct_l
  have ⟨p, q, _, pl, ql⟩:= line_nonempty l
  rcases Classical.em (p ∈ l') with pl' | pnl'
  · rcases Classical.em (q ∈ l') with ql' | qnl'
    · have := unique_line p q
      exfalso
      apply distinct_l
      calc
        _ = _ := (this l).mp ⟨pl, ql⟩
        _ = _ := by symm; exact (this l').mp ⟨pl', ql'⟩
    · exact ⟨q, ql, qnl'⟩
  · exact ⟨p, pl, pnl'⟩

namespace Colinear

theorem contains_left : Colinear x y z → x ∈ geo.line_of y z := by
  intro ⟨l, xl, yl, zl⟩
  have := unique_line y z l
  have := this.mp ⟨yl, zl⟩
  subst l
  exact xl

theorem contains_right : Colinear x y z → z ∈ geo.line_of x y := by
  intro ⟨l, xl, yl, zl⟩
  have := unique_line x y l
  have := this.mp ⟨xl, yl⟩
  subst l
  exact zl

theorem contains_middle : Colinear x y z → y ∈ geo.line_of x z := by
  intro ⟨l, xl, yl, zl⟩
  have := unique_line x z l
  have := this.mp ⟨xl, zl⟩
  subst l
  exact yl

end Colinear

end IncidenceLemmas

open OrderGeometry

section OrderLemmas

variable {point} [geo : OrderGeometry point]

namespace between

theorem contains_left : ⟪a ∗ b ∗ c⟫ → a ∈ geo.line_of b c := by
  intro betw
  apply Colinear.contains_left
  exact order_colinear betw

theorem contains_right : ⟪a ∗ b ∗ c⟫ → c ∈ geo.line_of a b := by
  intro betw
  apply Colinear.contains_right
  exact order_colinear betw

theorem contains_middle : ⟪a ∗ b ∗ c⟫ → b ∈ geo.line_of a c := by
  intro betw
  apply Colinear.contains_middle
  exact order_colinear betw

end between

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

theorem segment_has_left (a b : point) : a ∈ segment a b := by
  unfold segment
  rw [Set.mem_union]
  left
  simp only [Set.insert]
  left
  rfl

theorem segment_has_right (a b : point) : b ∈ segment a b := by
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

theorem segment_in_line : ∀ p q : point, segment p q ⊆ line_of p q := by
  unfold Set.subset
  intro a b p pab
  rcases on_segment pab with pa | pb | pab
    <;> try {subst p; apply mem_line_locus.mp; simp only [line_of_left, line_of_right]}
  have ⟨l, al, pl, bl⟩ := order_colinear pab
  have := unique_line a b l
  have := this.mp ⟨al, bl⟩
  subst l
  exact pl

end OrderLemmas
