import Hilbert.Geometry
import Hilbert.Lemmas

def line_sidedness {point} [OrderGeometry point] (l : Line point) (p q : point) :=
  (segment p q) ∩ l = {} ∨ p = q

-- TODO workshop notation, doesn't look good without parentheses
notation l " ⇇ " x:40 ", " y:40 => line_sidedness l x y
notation x " ⇇ " l " ⇉ " y:40 => ¬ line_sidedness l x y

/--
  Transitivity of line-sidedness, with three specifically nontrivial and noncolinear points.
-/
private theorem transitivity_lemma {point} [geo : OrderGeometry point]
  {a b c : point} {l : Line point}:
  segment a b ∩ l = ∅ → segment b c ∩ l = ∅ → ¬Colinear a c b → segment a c ∩ l = ∅ := by
  intro ab bc noncolinear
  apply Classical.byContradiction
  intro neg
  have ⟨d, ds⟩ := Set.nonempty_exists neg
  have ⟨dac, dl⟩ := Set.mem_inter.mp ds
  rcases on_segment dac with da | dc | dac
  · apply Set.member_empty ab
    exact ⟨d, by subst d; exact segment_has_left, dl⟩
  · apply Set.member_empty bc
    exact ⟨d, by subst d; exact segment_has_right, dl⟩
  rcases Classical.em (b ∈ l) with bl | bnl
  · apply Set.member_empty ab
    exact ⟨b, segment_has_right, bl⟩
  rcases geo.pasch noncolinear d dac l dl bnl with ⟨p, pl, pab | pcb⟩
  · apply Set.member_empty ab
    exact ⟨p, by unfold segment; right; exact pab, pl⟩
  · apply Set.member_empty bc
    exact ⟨p, by unfold segment; right; exact OrderGeometry.order_symmetric pcb, pl⟩

/--
  No matter how we cut a line `l`, for any point `x ∈ l` that is not on the cut, there is a point
  `p` on the same side of the cut as `x`.

  This theorem is used to create a point outside of a set of colinear points on the same side of a
  cut as these points. It also has the quirk of accepting cases in which the line is the same as the
  cut. In this case, this theorem is vacuously true.
 -/
private theorem line_cut_lemma {point} [OrderGeometry point] (l cut : Line point) :
  ∀ x ∈ l, x ∉ cut → ∃ p, segment x p ∩ cut = ∅ ∧ p ∉ l := by
  intro x xl xncut
  rcases Classical.em (cut = l) with lcut | lncut
  · subst l
    exact False.elim (xncut xl)

  have ⟨p, pcut, pnl⟩ := unshared_point cut l lncut
  have ⟨p', pxp'⟩ := OrderGeometry.extension p x
  exists p'
  constructor

  -- Part 1 -- the segment x p' does not go through the cut
  apply Set.empty_not_exists
  simp only [Set.mem_inter, mem_line, not_and]
  intro y yxp' ycut
  suffices cut = line x p' by apply xncut; rw [this]; exact line_of_left
  calc
    cut = line p y := by symm; exact line_unique pcut ycut
    _ = line x p' := line_unique (between.contains_left pxp') (segment_in_line y yxp')

  -- Part 2 -- p' doesn't lie with x
  intro neg
  apply pnl
  rw [<- line_unique xl neg]
  exact between.contains_left pxp'

theorem line_sidedness_is_equivalence {point} [OrderGeometry point] :
  ∀ l : Line point, Equivalence (line_sidedness l) := by
  intro l
  constructor
  · intro x; right; rfl
  · intro x y xy; cases xy
    · left; rw [segment_symm]; assumption
    · right; symm; assumption
  · intro x y z xy yz

    -- Discharge trivial cases
    rcases xy; case inr t => rw [t]; assumption
    case inl xy =>
    left
    cases yz; case inr t => rw [<- t]; assumption
    case inl yz =>

    refine Classical.byCases ?false (transitivity_lemma xy yz)
    intro colinear

    have : y ∉ l := by
      intro yl
      apply (Set.member_empty xy)
      exact ⟨y, segment_has_right, yl⟩
    -- TODO maybe I can unpack colinearity instead of using the line specifically between x and y
    have ⟨p, yp, p_extralinear⟩ := line_cut_lemma (line x y) l y line_of_right this

    -- from p' ∉ line_of x y I can derive every noncolinearity necessary
    have pnxy := extralinear_middle p_extralinear
    rw [colinear.right_transfers_line] at p_extralinear
    have pnyz := extralinear_left p_extralinear
    rw [<- colinear.middle_transfers_line] at p_extralinear
    have pnxz := extralinear_right p_extralinear

    have xp' := transitivity_lemma xy yp pnxy
    have p'y := transitivity_lemma (by rw [segment_symm]; exact yp) yz pnyz
    exact transitivity_lemma xp' p'y pnxz

theorem plane_separation {point} [geo : OrderGeometry point] :
  ∀ l : Line point, ∀ a b p : point, p ∉ l → (a ⇇ l ⇉ b) → (l ⇇ p, a) ∨ (l ⇇ p, b)
  := by sorry

theorem line_separation {point} [geo : OrderGeometry point] : ∀ l ∈ geo.line_set, ∀ a b c p ∈ l,
  ⟪a ∗ c ∗ b⟫ → p ≠ c → ⟪a ∗ p ∗ c⟫ ∨ ⟪c ∗ p ∗ b⟫
  := by sorry
