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
theorem line_unique {x y : point} {l : Line point} : x ∈ l → y ∈ l → line x y = l := by
  rw [<- and_imp]
  apply (line_uniqueness x y l).mp

@[simp]
theorem line_of_left : x ∈ geo.line x y := by
  have := line_uniqueness x y (geo.line x y)
  have := this.mpr rfl
  exact this.left

@[simp]
theorem line_of_right : y ∈ geo.line x y := by
  have := line_uniqueness x y (geo.line x y)
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
    · exfalso
      apply distinct_l
      calc
        l = line p q := by symm; exact line_unique pl ql
        line p q = l' := line_unique pl' ql'
    · exact ⟨q, ql, qnl'⟩
  · exact ⟨p, pl, pnl'⟩

namespace Colinear

theorem contains_left : Colinear x y z → x ∈ geo.line y z := by
  intro ⟨l, xl, yl, zl⟩
  rw [line_unique yl zl]
  exact xl

theorem contains_right : Colinear x y z → z ∈ geo.line x y := by
  intro ⟨l, xl, yl, zl⟩
  rw [line_unique xl yl]
  exact zl

theorem contains_middle : Colinear x y z → y ∈ geo.line x z := by
  intro ⟨l, xl, yl, zl⟩
  rw [line_unique xl zl]
  exact yl

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

theorem left_transfers_line : Colinear x y z → geo.line x y = geo.line x z := by
  intro col
  apply line_unique line_of_left (contains_middle col)
theorem middle_transfers_line : Colinear x y z → geo.line x y = geo.line y z := by
  intro col
  apply line_unique (contains_left col) line_of_left
theorem right_transfers_line : Colinear x y z → geo.line x z = geo.line y z := by
  intro col
  apply line_unique (contains_left col) line_of_right

end Colinear

theorem extralinear_left : a ∉ geo.line b c → ¬ Colinear a b c := by
  apply mt
  intro x
  exact x.contains_left

theorem extralinear_right : c ∉ geo.line a b → ¬ Colinear a b c := by
  apply mt
  intro x
  exact x.contains_right

theorem extralinear_middle : b ∉ geo.line a c → ¬ Colinear a b c := by
  apply mt
  intro x
  exact x.contains_middle

end IncidenceLemmas

open OrderGeometry

section OrderLemmas

variable {point} [geo : OrderGeometry point]

namespace between

theorem contains_left : ⟪a ∗ b ∗ c⟫ → a ∈ geo.line b c := by
  intro betw
  apply Colinear.contains_left
  exact order_colinear betw

theorem contains_right : ⟪a ∗ b ∗ c⟫ → c ∈ geo.line a b := by
  intro betw
  apply Colinear.contains_right
  exact order_colinear betw

theorem contains_middle : ⟪a ∗ b ∗ c⟫ → b ∈ geo.line a c := by
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

theorem segment_in_line {p q : point} : segment p q ⊆ line p q := by
  unfold Set.subset
  intro p pab
  rcases on_segment pab with pa | pb | pab
    <;> try {subst p; simp only [line_of_left, line_of_right, mem_line]}
  have ⟨l, al, pl, bl⟩ := order_colinear pab
  rw [line_unique al bl]
  exact pl

end OrderLemmas
