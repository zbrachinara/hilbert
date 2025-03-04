import Hilbert.Set

class Geometry (point : Type) where
  line : Set (Set point)

inductive Colinear : point → point → point → Prop where
| colinear {point} [geo : Geometry point] (a b c : point)
    (evidence : ∃ l ∈ geo.line, a ∈ l ∧ b ∈ l ∧ c ∈ l) :
    Colinear a b c

class IncidenceGeometry (point : Type) extends Geometry point where
  unique_line : ∀ x y : point, ∃ l ∈ line, ∀ l' ∈ line, x ∈ l' → y ∈ l' → l = l'
  line_nonempty : ∀ l ∈ line, ∃ x y ∈ point, x ≠ y ∧ x ∈ l ∧ y ∈ l
  non_colinearity : ∃ a b c : point, ¬ Colinear a b c

class PointOrder (point : Type) where
  between (a b c : point) : Prop

syntax (name := order_relation) "⟪" term " ∗ " term " ∗ " term "⟫": term
macro_rules
| `(⟪$p ∗ $q ∗ $r⟫) => `(PointOrder.between $p $q $r)

def Dichotomy (a b : Prop) : Prop := (a ∧ ¬ b) ∨ (¬ a ∧ b)
def Trichotomy (a b c : Prop) : Prop := (a ∧ b ∧ ¬ c) ∨ (a ∧ ¬ b ∧ c) ∨ (¬ a ∧ b ∧ c)

class OrderGeometry (point : Type) [PointOrder point] extends IncidenceGeometry point where
  order_symmetric : ∀ a b c : point, ⟪a ∗ b ∗ c⟫ → ⟪c ∗ b ∗ a⟫
  order_irreflexive : ∀ a b c : point, ⟪a ∗ b ∗ c⟫ → a ≠ c ∧ b ≠ c ∧ a ≠ b
  order_colinear : ∀ a b c : point, ⟪a ∗ b ∗ c⟫ → Colinear a b c
  extension : ∀ a b : point, ∃ c : point, ⟪a ∗ b ∗ c⟫
  order_unique : ∀ a b c : point, Trichotomy ⟪a ∗ b ∗ c⟫ ⟪b ∗ a ∗ c⟫ ⟪a ∗ c ∗ b⟫
  pasch :
    ∀ a b c : point, ¬ Colinear a b c →
    ∀ d : point, ⟪a ∗ d ∗ b⟫ →
    ∀ l ∈ line, d ∈ l →
    ∃ p : point, p ∈ l ∧ Dichotomy ⟪a ∗ p ∗ c⟫ ⟪b ∗ p ∗ c⟫
