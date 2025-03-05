import Hilbert.Set

class Geometry (point : Type) where
  line : Set (Set point)

open Geometry

inductive Colinear : point → point → point → Prop where
| colinear {point} [Geometry point] (a b c : point)
    (evidence : ∃ l ∈ line, a ∈ l ∧ b ∈ l ∧ c ∈ l) :
    Colinear a b c

class IncidenceGeometry (point : Type) extends Geometry point where
  unique_line : ∀ x y : point, ∃ l ∈ line, ∀ l' ∈ line, x ∈ l' → y ∈ l' → l = l'
  line_nonempty : ∀ l ∈ line, ∃ x y ∈ point, x ≠ y ∧ x ∈ l ∧ y ∈ l
  non_colinearity : ∃ a b c : point, ¬ Colinear a b c

inductive between : point → point → point → Prop where
| mk (a b c) : between a b c

syntax (name := order_relation) "⟪" term " ∗ " term " ∗ " term "⟫": term
macro_rules
| `(⟪$p ∗ $q ∗ $r⟫) => `(between $p $q $r)

def Dichotomy (a b : Prop) : Prop := (a ∧ ¬ b) ∨ (¬ a ∧ b)
def Trichotomy (a b c : Prop) : Prop := (a ∧ b ∧ ¬ c) ∨ (a ∧ ¬ b ∧ c) ∨ (¬ a ∧ b ∧ c)

class OrderGeometry (point : Type) extends IncidenceGeometry point where
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

def Segment {point} [OrderGeometry point] (a b : point) : Set point :=
  {a, b} ∪ {p ∈ Set.every point | ⟪a ∗ p ∗ b⟫}
def Ray {point} [OrderGeometry point] (a b : point): Set point :=
  Segment a b ∪ {p ∈ Set.every point | ⟪a ∗ b ∗ p⟫}
def Angle {point} [OrderGeometry point] (a b c : point) : Set point :=
  Ray a b ∪ Ray a c

def segment {point} [OrderGeometry point] := λ x ↦ ∃ a b : point, x = Segment a b
def ray {point} [OrderGeometry point] := λ x ↦ ∃ a b : point, x = Ray a b
def angle {point} [OrderGeometry point] := λ x ↦ ∃ a b c : point, x = Angle a b c
