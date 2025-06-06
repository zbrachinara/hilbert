import Hilbert.Foundations.Logic
import Hilbert.Foundations.Set

structure Geometry where
  point : Type
  line_set : Set (Set point)

abbrev Locus (geo : Geometry) := Set (geo.point)

class AsLocus (α : outParam (Geometry → Type)) (geo : Geometry) where
  as_locus : α geo → Locus geo
instance AsLocus.coe_to_locus [AsLocus α geo] : Coe (α geo) (Locus geo) where
  coe x := AsLocus.as_locus x
instance [AsLocus α geo] : Membership geo.point (α geo) where
  mem locus x := x ∈ (locus : Locus geo)

def Line (geo : Geometry) := {x : Set geo.point // x ∈ geo.line_set}
instance {geo : Geometry} : Membership geo.point (Line geo) where
  mem l x := x ∈ l.val
instance {geo : Geometry} : Coe (Line geo) (Set geo.point) where
  coe x := x.val

open Geometry

structure Colinear {geo : Geometry} (a b c : geo.point) : Prop where
  evidence : ∃ l : Line geo, a ∈ l ∧ b ∈ l ∧ c ∈ l

class IncidenceGeometry (geo : Geometry) where
  line (x y : geo.point) : Line geo
  line_uniqueness {x y : geo.point} {l' : Line geo} (xny : x ≠ y) : (x ∈ l' ∧ y ∈ l' ↔ line x y = l')
  line_nonempty : ∀ l, ∃ x y, x ≠ y ∧ line x y = l
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
  extension : ⟪a ∗ b ∗ extend a b⟫ -- TODO a ≠ b
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

def segment {geo} := @Segment.mk geo
def ray {geo} := @Ray.mk geo
def angle {geo} := @Angle.mk geo

@[simp]
instance Segment.locus [OrderGeometry geo] : AsLocus Segment geo where
  as_locus segment := {segment.a, segment.b} ∪ {p : geo.point | ⟪segment.a ∗ p ∗ segment.b⟫}
@[simp]
instance Ray.locus [OrderGeometry geo] : AsLocus Ray geo where
  as_locus ray := segment ray.o ray.a ∪ {p : geo.point | ⟪ray.o ∗ ray.a ∗ p⟫}
@[simp]
instance Angle.locus [OrderGeometry geo] : AsLocus Angle geo where
  as_locus angle := ray angle.o angle.a ∪ ray angle.o angle.b

class SegmentCongruence (geo : Geometry) where
  segments_congruent : Segment geo → Segment geo → Prop
infix:30 (name := segment_congruence) " ≅s " => SegmentCongruence.segments_congruent
class AngleCongruence (geo : Geometry) where
  angles_congruent : Angle geo → Angle geo → Prop
infix:30 (name := angle_congruence) " ≅a " => AngleCongruence.angles_congruent

class CongruenceGeometry (geo : Geometry) extends OrderGeometry geo, SegmentCongruence geo, AngleCongruence geo where
  segment_copy : Segment geo → Ray geo → geo.point
  segment_congruence (seg : Segment geo) (ray : Ray geo) : ∀ p' ∈ ray,
    seg ≅s segment ray.o p' ↔ p' = segment_copy seg ray
  segment_congruence_equiv : Equivalence segments_congruent
  addition_congruent : ∀ a b c a' b' c' : geo.point,
    Colinear a b c → Colinear a' b' c' →
    (segment a b : Locus _) ∩ segment b c = {b} → (segment a' b' : Locus _) ∩ segment b' c' = {b'} →
    segment a b ≅s segment a' b' → segment b c ≅s segment b' c' →
    segment a c ≅s segment a' c'
  angle_copy : Angle geo → Ray geo → geo.point
  angle_congruence (a : Angle geo) (ray : Ray geo) : ∀ p' : geo.point,
    a ≅a ⟨ray.o, ray.a, p'⟩ ↔ p' = angle_copy a ray
  angle_congruence_equivalence : Equivalence angles_congruent
  sas_congruence : ∀ a b c a' b' c' : geo.point,
    segment a b ≅s segment a' b' → segment a c ≅s segment a' c' →
    angle b a c ≅a angle b' a' c' → angle a b c ≅a angle a' b' c'

instance {geo} [CongruenceGeometry geo]: LT (Segment geo) where
  lt a b := by
    have b_ray := ray b.a b.b
    have a' := CongruenceGeometry.segment_copy a b_ray
    exact ⟪b.a ∗ a' ∗ b.b⟫

class HilbertPlane (geo : Geometry) extends IncidenceGeometry geo, CongruenceGeometry geo

inductive Parallel (l₁ l₂ : Line geo) where
| unequal : l₁.val ∩ l₂ = ∅ → Parallel l₁ l₂
| equal : l₁ = l₂ → Parallel l₁ l₂

class ParallelGeometry (geo : Geometry) where
  parallel (l : Line geo) (p : geo.point) : Line geo
  parallel_contains : p ∈ parallel l p
  parallel_is_parallel : Parallel l (parallel l p)

private def extend_segment_by_segment {geo} [CongruenceGeometry geo]
  (s₁ s₂ : Segment geo) : Segment geo := by
  have c := OrderGeometry.extend s₁.a s₁.b
  have s₁s₂ := CongruenceGeometry.segment_copy s₂ (ray s₁.b c)
  exact segment s₁.a s₁s₂
private def extend_segment_by_segment_n {geo} [CongruenceGeometry geo]
  (s₁ s₂ : Segment geo) (n : Nat) : Segment geo := match n with
  | .zero => s₁
  | .succ n' => by
    have s' := extend_segment_by_segment s₁ s₂
    exact extend_segment_by_segment_n s' s₂ n'
private def extend_segment_n {geo} [CongruenceGeometry geo]
  (s : Segment geo) (n : Nat) : Segment geo := extend_segment_by_segment_n s s n

class ContinuousGeometry (geo : Geometry) extends CongruenceGeometry geo where
  archimedean (seg target : Segment geo) : ∃ n, target < extend_segment_n seg n
