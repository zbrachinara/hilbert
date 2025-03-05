import Hilbert.Set

class Geometry (point : Type) where
  line : Set (Set point)

def Line' point [Geometry point] := Set point
def Line {point} [Geometry point] := Line' point

open Geometry

inductive Colinear : point → point → point → Prop where
| colinear {point} [Geometry point] (a b c : point)
    (evidence : ∃ l ∈ line, a ∈ l ∧ b ∈ l ∧ c ∈ l) :
    Colinear a b c

class IncidenceGeometry (point : Type) extends Geometry point where
  line_of (x y : point) : Set point
  unique_line : ∀ x y : point, ∀ l' ∈ line, x ∈ l' ∧ y ∈ l' ↔ l' = line_of x y
  line_nonempty : ∀ l ∈ line, ∃ x y ∈ point, x ≠ y ∧ x ∈ l ∧ y ∈ l
  non_colinearity : ∃ a b c : point, ¬ Colinear a b c

structure between (a b c : point) : Prop
notation (name := order_relation) "⟪" a " ∗ " b " ∗ " c "⟫" => between a b c

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

def segment {point} [OrderGeometry point] (a b : point) : Set point :=
  {a, b} ∪ {p ∈ Set.every point | ⟪a ∗ p ∗ b⟫}
def ray {point} [OrderGeometry point] (a b : point): Set point :=
  segment a b ∪ {p ∈ Set.every point | ⟪a ∗ b ∗ p⟫}
def angle {point} [OrderGeometry point] (a b c : point) : Set point :=
  ray b a ∪ ray b c

def Segment (point) [OrderGeometry point] : Set (Set point) := λ x ↦ ∃ a b : point, x = segment a b
def Ray (point) [OrderGeometry point] : Set (Set point) := λ x ↦ ∃ a b : point, x = ray a b
def Angle (point) [OrderGeometry point] : Set (Set point) := λ x ↦ ∃ a b c : point, x = angle a b c

structure congruent (x y : locus) : Prop
infix:30 (name := locus_congruence) " ≅ " => congruent

class HilbertPlane (point : Type) extends OrderGeometry point where
  segment_congruence : ∀ a b c d : point,
    ∃ p ∈ ray c d, ∀ p' ∈ ray c d, segment a b ≅ segment c p ↔ p' = p
  segment_congruence_equivalence : Equivalence (@congruent {s : Set point // s ∈ Segment point})
  addition_congruent : ∀ a b c a' b' c' : point,
    Colinear a b c → Colinear a' b' c' →
    segment a b ∩ segment b c = {b} → segment a' b' ∩ segment b' c' = {b'} →
    segment a b ≅ segment a' b' → segment b c ≅ segment b' c' →
    segment a c ≅ segment a' c'
  angle_congruence : ∀ a b c d g : point, ∃ e f : point, ∀ p : point,
    angle a b c ≅ angle p d g → p = e ∨ p = f
  angle_congruence_equivalence : Equivalence (@congruent {s : Set point // s ∈ Angle point})
  sas_congruence : ∀ a b c a' b' c' : point,
    segment a b ≅ segment a' b' → segment a c ≅ segment a' c' → angle b a c ≅ angle b' a' c' →
    angle a b c ≅ angle a' b' c'
