import Hilbert.Foundations.Logic
import Hilbert.Foundations.Set

structure Geometry where
  point : Type
  line_set : Set (Set point)

abbrev Locus (geo : Geometry) := (Set geo.point)

def Line (geo : Geometry) := {x : Set geo.point // x ∈ geo.line_set}
instance {geo : Geometry} : Membership geo.point (Line geo) where
  mem l x := x ∈ l.val
instance {geo : Geometry} : Coe (Line geo) (Locus geo) where
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
  extend (a b : geo.point) : geo.point
  extension : ⟪a ∗ b ∗ extend a b⟫
  order_unique : ∀ {a b c : geo.point}, a ≠ b → b ≠ c → a ≠ c → Colinear a b c →
    Trichotomy ⟪a ∗ b ∗ c⟫ ⟪b ∗ a ∗ c⟫ ⟪a ∗ c ∗ b⟫
  pasch {a b c : geo.point} : ¬ Colinear a b c →
    ∀ d : geo.point, ⟪a ∗ d ∗ b⟫ →
    ∀ l : Line geo, d ∈ l → c ∉ l →
    Dichotomy (∃ p ∈ l, ⟪a ∗ p ∗ c⟫) (∃ p ∈ l, ⟪b ∗ p ∗ c⟫)

structure Segment (geo : Geometry) where
  a : geo.point
  b : geo.point
structure Ray (geo : Geometry) where
  o : geo.point
  a : geo.point
structure Angle (geo : Geometry) where
  o : geo.point
  a : geo.point
  b : geo.point

instance Segment.as_locus {geo} [OrderGeometry geo] : Coe (Segment geo) (Locus geo) where
  coe segment := {segment.a, segment.b} ∪ {p : geo.point | ⟪segment.a ∗ p ∗ segment.b⟫}
instance Segment.membership {geo} [OrderGeometry geo] : Membership geo.point (Segment geo) where
  mem loc x := x ∈ Segment.as_locus.coe loc
instance Ray.as_locus {geo} [OrderGeometry geo] : Coe (Ray geo) (Locus geo) where
  coe ray := Segment.mk ray.o ray.a ∪ {p : geo.point | ⟪ray.o ∗ ray.a ∗ p⟫}
instance Ray.membership {geo} [OrderGeometry geo] : Membership geo.point (Ray geo) where
  mem loc x := x ∈ Ray.as_locus.coe loc
instance Angle.as_locus {geo} [OrderGeometry geo] : Coe (Angle geo) (Locus geo) where
  coe angle := Ray.mk angle.o angle.a ∪ Ray.mk angle.o angle.b
instance Angle.membership {geo} [OrderGeometry geo] : Membership geo.point (Angle geo) where
  mem loc x := x ∈ Angle.as_locus.coe loc

def segment {geo} [OrderGeometry geo] (a b : geo.point) : Locus geo := Segment.mk a b
def ray {geo} [OrderGeometry geo] (o a : geo.point) : Locus geo := Ray.mk o a
def angle {geo} [OrderGeometry geo] (a b c : geo.point) : Locus geo := Angle.mk a b c

structure congruent (x y : locus) : Prop
infix:30 (name := locus_congruence) " ≅ " => congruent

class CongruenceGeometry (geo : Geometry) extends OrderGeometry geo where
  segment_copy (s₁ s₂ r₁ r₂ : geo.point) : geo.point
  segment_congruence : ∀ a b c d : geo.point,
    ∀ p' ∈ (ray c d), segment a b ≅ segment c p' ↔ p' = segment_copy a b c d
  segment_congruence_equivalence : Equivalence (@congruent (Segment geo))
  addition_congruent : ∀ a b c a' b' c' : geo.point,
    Colinear a b c → Colinear a' b' c' →
    segment a b ∩ segment b c = {b} → (segment a' b' : Set _) ∩ segment b' c' = {b'} →
    segment a b ≅ segment a' b' → segment b c ≅ segment b' c' →
    segment a c ≅ segment a' c'
  angle_congruence : ∀ a b c d g : geo.point, ∃ e f : geo.point, ∀ p : geo.point, -- TODO make same as segment_copy
    angle a b c ≅ angle p d g → p = e ∨ p = f
  angle_congruence_equivalence : Equivalence (@congruent (Angle geo))
  sas_congruence : ∀ a b c a' b' c' : geo.point,
    segment a b ≅ segment a' b' → segment a c ≅ segment a' c' → angle b a c ≅ angle b' a' c' →
    angle a b c ≅ angle a' b' c'

instance {geo} [CongruenceGeometry geo]: LT (Segment geo) where
  lt a b := by
    sorry


class HilbertPlane (geo : Geometry) extends IncidenceGeometry geo, CongruenceGeometry geo

inductive Parallel (l₁ l₂ : Line geo) where
| unequal : l₁.val ∩ l₂ = ∅ → Parallel l₁ l₂
| equal : l₁ = l₂ → Parallel l₁ l₂

class ParallelGeometry (geo : Geometry) where
  parallel (l : Line geo) (p : geo.point) : Line geo
  parallel_contains : p ∈ parallel l p
  parallel_is_parallel : Parallel l (parallel l p)

private def extend_segment_by_segment {geo} [CongruenceGeometry geo]
  (a₁ a₂ b₁ b₂ : geo.point) : geo.point × geo.point := by
  have a' := OrderGeometry.extend a₁ a₂
  have a₃ := CongruenceGeometry.segment_copy b₁ b₂ a₂ a'
  exact ⟨a₁, a₃⟩
private def extend_segment_by_segment_n {geo} [CongruenceGeometry geo]
  (a₁ a₂ b₁ b₂ : geo.point) (n : Nat) : geo.point × geo.point := match n with
  | .zero => ⟨a₁, a₁⟩
  | .succ n' => by
    have ⟨x₁, x₂⟩ := extend_segment_by_segment a₁ a₂ b₁ b₂
    exact extend_segment_by_segment_n x₁ x₂ b₁ b₂ n'
private def extend_segment_n {geo} [CongruenceGeometry geo] (s₁ s₂ : geo.point) (n : Nat) :
  geo.point × geo.point := extend_segment_by_segment_n s₁ s₁ s₁ s₂ n

class ContinuousGeometry (geo : Geometry) extends CongruenceGeometry geo where
  archimedean : sorry
