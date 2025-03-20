import Hilbert.Foundations.Logic
import Hilbert.Foundations.Set

structure Geometry where
  point : Type
  line_set : Set (Set point)

def Line (geo : Geometry) := {x : Set geo.point // x ∈ geo.line_set}
def Locus (geo : Geometry) := (Set geo.point)
instance {geo : Geometry} : Membership geo.point (Line geo) where
  mem l x := x ∈ l.val
instance {geo : Geometry} : Coe (Line geo) (Set geo.point) where
  coe x := x.val

open Geometry

structure Colinear {geo : Geometry} (a b c : geo.point) : Prop where
  evidence : ∃ l : Line geo, a ∈ l ∧ b ∈ l ∧ c ∈ l

class IncidenceGeometry (geo : Geometry) where
  line (x y : geo.point) (xny : x ≠ y) : Line geo
  line_uniqueness {x y : geo.point} {l' : Line geo} (xny : x ≠ y) : (x ∈ l' ∧ y ∈ l' ↔ line x y xny = l')
  line_nonempty : ∀ l, ∃ x y, ∃ xny, line x y xny = l
  nontrivial : ∃ a b c : geo.point, ¬ Colinear a b c

export IncidenceGeometry (line)

class PointOrder (α : Type) where
  between : α → α → α → Prop
notation (name := order_relation) "⟪" a " ∗ " b " ∗ " c "⟫" => PointOrder.between a b c

class OrderGeometry (geo : Geometry) extends PointOrder geo.point where
  order_symmetric : ∀ {a b c : geo.point}, ⟪a ∗ b ∗ c⟫ → ⟪c ∗ b ∗ a⟫
  order_irreflexive : ∀ {a b c : geo.point}, ⟪a ∗ b ∗ c⟫ → a ≠ c ∧ b ≠ c ∧ a ≠ b
  order_colinear {a b c : geo.point} : ⟪a ∗ b ∗ c⟫ → Colinear a b c
  extension : ∀ a b : geo.point, ∃ c : geo.point, ⟪a ∗ b ∗ c⟫ -- TODO make this constructive
  order_unique : ∀ {a b c : geo.point}, a ≠ b → b ≠ c → a ≠ c → Colinear a b c →
    Trichotomy ⟪a ∗ b ∗ c⟫ ⟪b ∗ a ∗ c⟫ ⟪a ∗ c ∗ b⟫
  pasch {a b c : geo.point} : ¬ Colinear a b c →
    ∀ d : geo.point, ⟪a ∗ d ∗ b⟫ →
    ∀ l : Line geo, d ∈ l → c ∉ l →
    Dichotomy (∃ p ∈ l, ⟪a ∗ p ∗ c⟫) (∃ p ∈ l, ⟪b ∗ p ∗ c⟫)

def segment {geo} [OrderGeometry geo] (a b : geo.point) : Set geo.point :=
  {a, b} ∪ {p : geo.point | ⟪a ∗ p ∗ b⟫}
def ray {geo} [OrderGeometry geo] (a b : geo.point): Set geo.point :=
  segment a b ∪ {p : geo.point | ⟪a ∗ b ∗ p⟫}
def angle {geo} [OrderGeometry geo] (a b c : geo.point) : Set geo.point :=
  ray b a ∪ ray b c

def Segment (geo) [OrderGeometry geo] := {x : Locus geo // ∃ a b, x = segment a b}
def Ray (geo) [OrderGeometry geo] := {x : Locus geo // ∃ a b, x = ray a b}
def Angle (geo) [OrderGeometry geo] := {x : Locus geo // ∃ a b c, x = angle a b c}

structure congruent (x y : locus) : Prop
infix:30 (name := locus_congruence) " ≅ " => congruent

class CongruenceGeometry (geo : Geometry) extends OrderGeometry geo where
  segment_congruence : ∀ a b c d : geo.point,
    ∃ p ∈ ray c d, ∀ p' ∈ ray c d, segment a b ≅ segment c p ↔ p' = p
  segment_congruence_equivalence : Equivalence (@congruent (Segment geo))
  addition_congruent : ∀ a b c a' b' c' : geo.point,
    Colinear a b c → Colinear a' b' c' →
    segment a b ∩ segment b c = {b} → segment a' b' ∩ segment b' c' = {b'} →
    segment a b ≅ segment a' b' → segment b c ≅ segment b' c' →
    segment a c ≅ segment a' c'
  angle_congruence : ∀ a b c d g : geo.point, ∃ e f : geo.point, ∀ p : geo.point,
    angle a b c ≅ angle p d g → p = e ∨ p = f
  angle_congruence_equivalence : Equivalence (@congruent (Angle geo))
  sas_congruence : ∀ a b c a' b' c' : geo.point,
    segment a b ≅ segment a' b' → segment a c ≅ segment a' c' → angle b a c ≅ angle b' a' c' →
    angle a b c ≅ angle a' b' c'

class HilbertPlane (geo : Geometry) extends IncidenceGeometry geo, CongruenceGeometry geo

inductive Parallel (l₁ l₂ : Line geo) where
| unequal : l₁.val ∩ l₂ = ∅ → Parallel l₁ l₂
| equal : l₁ = l₂ → Parallel l₁ l₂

class ParallelGeometry (geo : Geometry) where
  parallel (l : Line geo) (p : geo.point) : Line geo
  parallel_contains : p ∈ parallel l p
  parallel_is_parallel : Parallel l (parallel l p)
