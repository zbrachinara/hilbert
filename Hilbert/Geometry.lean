import Hilbert.Set

class Geometry (α : Type) where
  point : Set α
  line : Set (Set α)
  closed: line ⊆ point.power_set

class IncidenceGeometry (α : Type) extends Geometry α where
  unique_line : ∀ x y ∈ point, ∃ l ∈ line, ∀ l' ∈ line, a ∈ l' → b ∈ l' → l = l'
  line_nonempty : ∀ l ∈ line, ∃ x y ∈ point, x ≠ y ∧ x ∈ l ∧ y ∈ l
  non_colinearity : ∃ a b c ∈ point,
    ∀ l ∈ line, a ∉ l ∨ b ∉ l ∨ c ∉ l

class PointOrder (α : Type) where
  rel (a b c : α) : Prop

syntax (name := order_relation) "⟪" term " ∗ " term " ∗ " term "⟫": term
macro_rules
| `(⟪$p ∗ $q ∗ $r⟫) => `(PointOrder.rel $p $q $r)

class OrderGeometry (α : Type) [PointOrder α] extends IncidenceGeometry α where
  order_symmetric : ∀ a b c ∈ point, ⟪a ∗ b ∗ c⟫ → ⟪c ∗ b ∗ a⟫
