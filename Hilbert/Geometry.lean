import Hilbert.Foundations.Logic
import Hilbert.Foundations.Set

class Geometry (point : Type) where
  line_set : Set (Set point)

def Line point [geo : Geometry point] := {x : Set point // x ∈ geo.line_set}
instance {point} [Geometry point] : Membership point (Line point) where
  mem l x := x ∈ l.val
instance {point} [Geometry point] : Coe (Line point) (Set point) where
  coe x := x.val

open Geometry

structure Colinear {point} [geo : Geometry point] (a b c : point) : Prop where
  evidence : ∃ l : Line point, a ∈ l ∧ b ∈ l ∧ c ∈ l

class IncidenceGeometry (point : Type) extends Geometry point where
  line (x y : point) : Line point
  line_uniqueness {x y : point} {l' : Line point} (xny : x ≠ y) : (x ∈ l' ∧ y ∈ l' ↔ line x y = l')
  line_nonempty : ∀ l : Line point, ∃ x y : point, x ≠ y ∧ line x y = l
  nontrivial : ∃ a b c : point, ¬ Colinear a b c

export IncidenceGeometry (line)

class Betweenness {α : Type} where
  between : α → α → α → Prop
notation (name := order_relation) "⟪" a " ∗ " b " ∗ " c "⟫" => Betweenness.between a b c

class OrderGeometry (point : Type) extends IncidenceGeometry point, @Betweenness point where
  order_symmetric : ∀ {a b c : point}, ⟪a ∗ b ∗ c⟫ → ⟪c ∗ b ∗ a⟫
  order_irreflexive : ∀ {a b c : point}, ⟪a ∗ b ∗ c⟫ → a ≠ c ∧ b ≠ c ∧ a ≠ b
  order_colinear {a b c : point} : ⟪a ∗ b ∗ c⟫ → Colinear a b c
  extension : ∀ a b : point, ∃ c : point, ⟪a ∗ b ∗ c⟫ -- TODO make this constructive
  order_unique : ∀ {a b c : point}, a ≠ b → b ≠ c → a ≠ c → Colinear a b c →
    Trichotomy ⟪a ∗ b ∗ c⟫ ⟪b ∗ a ∗ c⟫ ⟪a ∗ c ∗ b⟫
  pasch {a b c : point} : ¬ Colinear a b c →
    ∀ d : point, ⟪a ∗ d ∗ b⟫ →
    ∀ l : Line point, d ∈ l → c ∉ l →
    Dichotomy (∃ p ∈ l, ⟪a ∗ p ∗ c⟫) (∃ p ∈ l, ⟪b ∗ p ∗ c⟫)

def segment {point} [OrderGeometry point] (a b : point) : Set point :=
  {a, b} ∪ {p : point | ⟪a ∗ p ∗ b⟫}
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
