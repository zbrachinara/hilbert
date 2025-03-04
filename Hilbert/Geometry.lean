import Hilbert.Set

class Geometry (point : Type) where
  line : Set (Set point)

class IncidenceGeometry (point : Type) extends Geometry point where
  unique_line : ∀ x y : point, ∃ l ∈ line, ∀ l' ∈ line, x ∈ l' → y ∈ l' → l = l'
  line_nonempty : ∀ l ∈ line, ∃ x y ∈ point, x ≠ y ∧ x ∈ l ∧ y ∈ l
  non_colinearity : ∃ a b c : point, ∀ l ∈ line, a ∉ l ∨ b ∉ l ∨ c ∉ l

class PointOrder (point : Type) where
  between (a b c : point) : Prop

syntax (name := order_relation) "⟪" term " ∗ " term " ∗ " term "⟫": term
macro_rules
| `(⟪$p ∗ $q ∗ $r⟫) => `(PointOrder.between $p $q $r)

class OrderGeometry (point : Type) [PointOrder point] extends IncidenceGeometry point where
  order_symmetric : ∀ a b c : point, ⟪a ∗ b ∗ c⟫ → ⟪c ∗ b ∗ a⟫
