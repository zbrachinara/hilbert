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
  · apply Set.member_empty.mp ab
    exact ⟨d, by subst d; exact segment_has_left, dl⟩
  · apply Set.member_empty.mp bc
    exact ⟨d, by subst d; exact segment_has_right, dl⟩
  rcases Classical.em (b ∈ l) with bl | bnl
  · apply Set.member_empty.mp ab
    exact ⟨b, segment_has_right, bl⟩
  have pasch_out := geo.pasch noncolinear d dac l dl bnl
  rcases pasch_out.either with ⟨p, pl, pab⟩ | ⟨p, pl, pcb⟩
  · apply Set.member_empty.mp ab
    exact ⟨p, by unfold segment; right; exact pab, pl⟩
  · apply Set.member_empty.mp bc
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
  apply Set.member_empty.mpr
  rw [not_exists]
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
      apply Set.member_empty.mp xy
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

/--
  Similar to the transitivity lemma, proves for noncolinear points that a line will separate a plane
  into at most two parts, then this result is extended to colinear points using the line cut lemma.
-/
private theorem separation_lemma {point} [OrderGeometry point] {a b p : point} {l : Line point}:
  ¬Colinear a b p → a ∉ l → b ∉ l → p ∉ l → (a ⇇ l ⇉ b) → (p ⇇ l ⇉ a) → (l ⇇ p, b) := by

  intro noncolinear anl bnl pnl lnab lnpa
  unfold line_sidedness at lnab
  rw [not_or, Set.member_empty, Classical.not_not] at lnab
  have ⟨⟨x, xab, xl⟩, _⟩ := lnab
  unfold line_sidedness at lnpa
  rw [not_or, Set.member_empty, Classical.not_not] at lnpa
  have ⟨⟨y, ypa, yl⟩, _⟩ := lnpa

  rcases on_segment xab with xa | xb | xab <;> try subst x -- TODO extract to lemma
  · exact False.elim (anl xl)
  · exact False.elim (bnl xl)
  rcases on_segment ypa with yp | ya | ypa <;> try subst y
  · exact False.elim (pnl yl)
  · exact False.elim (anl yl)
  left
  apply Set.member_empty.mpr
  have pasch_out := OrderGeometry.pasch noncolinear x xab l xl pnl
  intro ⟨t, tpb, tl⟩
  rcases on_segment tpb with tp | tb | tpb <;> try subst t
  · exact pnl tl
  · exact bnl tl
  apply pasch_out.neg_left
  · exact ⟨t, tl, OrderGeometry.order_symmetric tpb⟩
  · exact ⟨y, yl, OrderGeometry.order_symmetric ypa⟩

theorem plane_separation {point} [OrderGeometry point] (l : Line point) (a b p : point):
  a ∉ l → b ∉ l → p ∉ l → a ⇇ l ⇉ b → Dichotomy (l ⇇ p, a) (l ⇇ p, b)
  := by
  intro anl bnl pnl lnab
  have eq := line_sidedness_is_equivalence l
  rcases Classical.em (l ⇇ p, a) with lpa | lnpa
  · left
    refine ⟨lpa, ?h⟩
    intro lpb
    apply lnab
    exact eq.trans (eq.symm lpa) lpb -- TODO find a way to do inference with calc and symm
  · right
    refine ⟨lnpa, ?h⟩
    rcases Classical.em (Colinear a b p) with colinear | noncolinear
    rotate_left
    · exact separation_lemma noncolinear anl bnl pnl lnab lnpa
    have ⟨r, prl, rnab⟩ := line_cut_lemma (line a b) l p (Colinear.contains_right colinear) pnl
    have pr : l ⇇ p, r := by left; exact prl
    have rnl : r ∉ l := by
      intro rl
      apply Set.member_empty.mp prl
      exact ⟨r, segment_has_right, rl⟩
    have : r ⇇ l ⇉ a := by
      intro neg
      apply lnpa
      exact eq.trans pr neg

    suffices l ⇇ r, b by {
      exact eq.trans pr this
    }
    refine separation_lemma ?col anl bnl rnl lnab this
    exact extralinear_right rnab

theorem line_separation {point} [geo : OrderGeometry point] : ∀ l ∈ geo.line_set, ∀ a b c p ∈ l,
  ⟪a ∗ c ∗ b⟫ → p ≠ c → ⟪a ∗ p ∗ c⟫ ∨ ⟪c ∗ p ∗ b⟫
  := by sorry
