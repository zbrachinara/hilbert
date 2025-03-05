import Hilbert.Geometry

open Geometry

def line_sidedness {point} [OrderGeometry point] (l : Line' point) (p q : point) :=
  (segment p q) ∩ l = {}

theorem line_sidedness_is_equivalence {point} [geo : OrderGeometry point] :
  ∀ l ∈ geo.line, Equivalence (line_sidedness l) := by sorry

theorem plane_separation {point} [geo : OrderGeometry point] :
  ∀ l ∈ geo.line, ∀ a b p ∈ Set.every point - l,
  ¬ line_sidedness l a b → line_sidedness l p a ∨ line_sidedness l p b
  := by sorry

theorem line_separation {point} [geo : OrderGeometry point] : ∀ l ∈ geo.line, ∀ a b c p ∈ l,
  ⟪a ∗ c ∗ b⟫ → ⟪a ∗ p ∗ c⟫ ∨ ⟪c ∗ p ∗ b⟫
  := by sorry
