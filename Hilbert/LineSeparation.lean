import Hilbert.Geometry
import Hilbert.Lemmas

def line_sidedness {point} [OrderGeometry point] (l : Line' point) (p q : point) :=
  (segment p q) ∩ l = {} ∨ p = q

-- TODO workshop notation, doesn't look good without parentheses
notation l " ⇇ " x:40 ", " y:40 => line_sidedness l x y
notation x " ⇇ " l " ⇉ " y:40 => ¬ line_sidedness l x y

theorem line_sidedness_is_equivalence {point} [geo : OrderGeometry point] :
  ∀ l ∈ geo.line, Equivalence (line_sidedness l) := by
  intro l l_line
  constructor
  · intro x; right; rfl
  · intro x y xy
    cases xy
    · left; rw [segment_symm]; assumption
    · right; symm; assumption
  · intro x y z xy yz

    -- discharging trivial cases
    cases xy; case inr t => rw [t]; assumption
    case inl xy =>
    cases yz; case inr t => rw [<- t]; left; assumption
    case inl yz =>

    cases Classical.em (Colinear x y z)
    case inl colinear => sorry
    case inr noncolinear =>

    apply Classical.byContradiction
    intro neg
    sorry

theorem plane_separation {point} [geo : OrderGeometry point] :
  ∀ l ∈ geo.line, ∀ a b p ∈ Set.every point - l, (a ⇇ l ⇉ b) → (l ⇇ p, a) ∨ (l ⇇ p, b)
  := by sorry

theorem line_separation {point} [geo : OrderGeometry point] : ∀ l ∈ geo.line, ∀ a b c p ∈ l,
  ⟪a ∗ c ∗ b⟫ → p ≠ c → ⟪a ∗ p ∗ c⟫ ∨ ⟪c ∗ p ∗ b⟫
  := by sorry
