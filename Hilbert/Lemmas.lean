import Hilbert.Geometry

variable {point} [OrderGeometry point]

open OrderGeometry

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
  constructor <;> exact fun x ↦ order_symmetric x

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
