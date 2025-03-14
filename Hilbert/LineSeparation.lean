import Hilbert.Geometry
import Hilbert.Lemmas

variable {point} [OrderGeometry point]

/--
  Two points are on the same side of a cut if the segment through the points does not intersect the
  cut. Two points are also consdiered on the same side of the cut if they are equal (for
  reflexivity), so any point on the cut is together with itself, but not with any other point.
-/
def cut_together (cut : Line point) (p q : point) := (segment p q) ∩ cut = ∅ ∨ p = q
/--
  Two points are on the opposite sides of a cut when the segment through them intsersects the cut.
  This is the exact negation of `cut_together`, and is defined as such.
-/
def cut_apart (cut : Line point) (p q : point) := ¬ cut_together cut p q

-- TODO workshop notation, doesn't look good without parentheses
@[inherit_doc] notation l " ⇇ " x:40 ", " y:40 => cut_together l x y
@[inherit_doc] notation x " ⇇ " l " ⇉ " y:40 => cut_apart l x y

namespace cut_apart

theorem defn {a b : point} : a ⇇ cut ⇉ b → (∃ p, p ∈ segment a b ∧ p ∈ cut) ∧ (a ≠ b) := by
  intro separated
  unfold cut_apart at separated
  unfold cut_together at separated
  rw [not_or, Set.member_empty, Classical.not_not] at separated
  exact separated

@[simp]
theorem intersects_cut {a b : point} : a ⇇ cut ⇉ b → ∃ p, p ∈ segment a b ∧ p ∈ cut := by
  intro separated; exact separated.defn.left
@[simp]
theorem irreflexive {a b : point} : a ⇇ cut ⇉ b → a ≠ b := by
  intro separated; exact separated.defn.right

end cut_apart

/--
  Transitivity of line-sidedness, but specifically needs noncolinear points.
-/
private theorem transitivity_lemma {a b c : point} {l : Line point}:
  segment a b ∩ l = ∅ → segment b c ∩ l = ∅ → ¬Colinear a c b → segment a c ∩ l = ∅ := by
  intro ab bc noncolinear
  apply Classical.byContradiction
  intro neg
  have ⟨d, ds⟩ := Set.nonempty_exists neg
  have ⟨dac, dl⟩ := Set.mem_inter.mp ds
  rcases on_segment.mp dac with da | dc | dac
  · apply Set.member_empty.mp ab
    exact ⟨d, by subst d; exact segment_has_left, dl⟩
  · apply Set.member_empty.mp bc
    exact ⟨d, by subst d; exact segment_has_right, dl⟩
  rcases Classical.em (b ∈ l) with bl | bnl
  · apply Set.member_empty.mp ab
    exact ⟨b, segment_has_right, bl⟩
  have pasch_out := OrderGeometry.pasch noncolinear d dac l dl bnl
  rcases pasch_out.either with ⟨p, pl, pab⟩ | ⟨p, pl, pcb⟩
  · apply Set.member_empty.mp ab
    exact ⟨p, by unfold segment; right; exact pab, pl⟩
  · apply Set.member_empty.mp bc
    exact ⟨p, by unfold segment; right; exact pcb.symm, pl⟩

/--
  No matter how we cut a line `l`, for any point `x ∈ l` that is not on the cut, there is a point `p
  ∉ l` on the same side of the cut as `x`.

  This theorem is used to create a point outside of a set of colinear points, but also on the same
  side of a cut as these points. It also has the quirk of accepting cases in which the line is the
  same as the cut. In this case, this theorem is vacuously true.
 -/
theorem line_cut_lemma (l cut : Line point) :
  ∀ x ∈ l, x ∉ cut → ∃ p, segment x p ∩ cut = ∅ ∧ p ∉ l := by
  intro x xl xncut
  rcases Classical.em (cut = l) with lcut | lncut
  · subst l
    exact False.elim (xncut xl)

  have ⟨p, pcut, pnl⟩ := unshared_point cut l lncut
  have ⟨p', pxp'⟩ := OrderGeometry.extension p x
  have xnp' : x ≠ p' := by intro p'x; exact pxp'.right_irrefl p'x

  exists p'
  constructor

  -- Part 1 -- the segment x p' does not go through the cut
  apply Set.member_empty.mpr
  rw [not_exists]
  simp only [Set.mem_inter, mem_line, not_and]
  intro y yxp' ycut
  suffices cut = line x p' by apply xncut; rw [this]; exact line_of_left pxp'.right_irrefl
  have pny : p ≠ y := by intro py; subst p; exact pxp'.outside_segment yxp'
  calc
    cut = line p y := by symm; exact line_unique pny pcut ycut
    line p y = line x p' := line_unique pny (pxp'.contains_left) (segment_in_line xnp' y yxp')

  -- Part 2 -- p' doesn't lie with x
  intro neg
  apply pnl
  rw [<- line_unique xnp' xl neg]
  exact pxp'.contains_left

theorem line_sidedness_symmetric {a b : point} : ∀ l : Line point, l ⇇ a, b → l ⇇ b, a := by
  intro l xy; cases xy
  · left; rw [segment_symm]; assumption
  · right; symm; assumption

theorem line_sidedness_transitive {x y z : point} : ∀ l : Line point,
  l ⇇ x, y → l ⇇ y, z → l ⇇ x, z := by
  intro cut xy yz
  -- Remove trivial equalities
  rcases Classical.em (x = y) with xy | xny
  · subst x; exact yz
  rcases Classical.em (y = z) with yz | ynz
  · subst y; exact xy
  rcases Classical.em (x = z) with xz | xnz
  · right; exact xz
  rw [<- Ne] at *
  -- Discharge trivial cases
  rcases xy; case inr t => rw [t]; assumption
  case inl xy =>
  left
  cases yz
  case inr t => rw [<- t]; assumption
  case inl yz =>

  refine Classical.byCases ?false (transitivity_lemma xy yz)
  intro colinear

  have : y ∉ cut := by
    intro yl
    apply Set.member_empty.mp xy
    exact ⟨y, segment_has_right, yl⟩
  -- TODO maybe I can unpack colinearity instead of using the line specifically between x and y
  have ⟨p, yp, p_extralinear⟩ := line_cut_lemma (line x y) cut y (line_of_right xny) this

  -- from p' ∉ line_of x y I can derive every noncolinearity necessary
  have pnxy := (extralinear_middle xny).mp p_extralinear
  rw [line_symmetric xny, colinear.right_transfers_line xny.symm ynz, line_symmetric ynz]
    at p_extralinear
  have pnyz := (extralinear_left ynz.symm).mp p_extralinear
  rw [<- colinear.middle_transfers_line xnz.symm ynz.symm, line_symmetric xnz.symm] at p_extralinear
  have pnxz := (extralinear_right xnz).mp p_extralinear

  have xp' := transitivity_lemma xy yp pnxy
  have p'y := transitivity_lemma (by rw [segment_symm]; exact yp) yz pnyz
  exact transitivity_lemma xp' p'y pnxz

theorem line_sidedness_is_equivalence : ∀ l : Line point, Equivalence (cut_together l) := by
  intro cut
  constructor
  · intro x; right; rfl
  · exact line_sidedness_symmetric cut
  · exact line_sidedness_transitive cut
/--
  Similar to the transitivity lemma, proves for noncolinear points that a line will separate a plane
  into at most two parts, then this result is extended to colinear points using the line cut lemma.
-/
private theorem separation_lemma {a b p : point} {l : Line point}:
  ¬Colinear a b p → a ∉ l → b ∉ l → p ∉ l → (a ⇇ l ⇉ b) → (p ⇇ l ⇉ a) → (l ⇇ p, b) := by

  intro noncolinear anl bnl pnl lnab lnpa
  have ⟨x, xab, xl⟩ := lnab.intersects_cut
  have ⟨y, ypa, yl⟩ := lnpa.intersects_cut

  rcases on_segment.mp xab with xa | xb | xab <;> try subst x
  · exact False.elim (anl xl)
  · exact False.elim (bnl xl)
  rcases on_segment.mp ypa with yp | ya | ypa <;> try subst y
  · exact False.elim (pnl yl)
  · exact False.elim (anl yl)
  left
  apply Set.member_empty.mpr
  have pasch_out := OrderGeometry.pasch noncolinear x xab l xl pnl
  intro ⟨t, tpb, tl⟩
  rcases on_segment.mp tpb with tp | tb | tpb <;> try subst t
  · exact pnl tl
  · exact bnl tl
  apply pasch_out.neg_left
  · exact ⟨t, tl, tpb.symm⟩
  · exact ⟨y, yl, ypa.symm⟩

theorem plane_separation {l : Line point} {a b p : point}:
  a ∉ l → b ∉ l → p ∉ l → a ⇇ l ⇉ b → Dichotomy (l ⇇ p, a) (l ⇇ p, b)
  := by
  intro anl bnl pnl lnab

  have anb := lnab.irreflexive

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
    have ⟨r, prl, rnab⟩ := line_cut_lemma (line a b) l p ((Colinear.contains_right anb).mp colinear) pnl
    have pr : l ⇇ p, r := by left; exact prl
    have rnl : r ∉ l := by
      intro rl
      apply Set.member_empty.mp prl
      exact ⟨r, segment_has_right, rl⟩
    have : r ⇇ l ⇉ a := by
      intro neg
      apply lnpa
      exact eq.trans pr neg

    suffices l ⇇ r, b from eq.trans pr this
    exact separation_lemma ((extralinear_right anb).mp rnab) anl bnl rnl lnab this

namespace Betweenness.between

@[simp]
theorem quasitransitive_left {a b c d : point} : ⟪a ∗ b ∗ c⟫ → ⟪b ∗ c ∗ d⟫ → ⟪a ∗ b ∗ d⟫ := by
  intro abc bcd

  have ⟨l, al, bl, cl⟩ := OrderGeometry.order_colinear abc
  have ⟨l', _, _, dl⟩ := OrderGeometry.order_colinear bcd
  have ⟨s, snl⟩ := not_colinear_to l
  have : l = l' := by calc
    l = line b c := by symm; apply line_unique abc.right_irrefl bl cl
    line b c = l' := by apply line_unique abc.right_irrefl <;> assumption
  subst this

  have bns : b ≠ s := by intro bs; subst b; exact snl bl

  have unique_intersection : ∀ p ∈ l, p ≠ b → p ∉ line b s := by
    intro p pl pnb pbs
    apply snl
    rw [<- line_unique pnb pl bl, line_unique pnb pbs (line_of_left bns)]
    exact line_of_right bns

  have anl := (unique_intersection a al abc.left_irrefl)
  have cnl := (unique_intersection c cl abc.right_irrefl.symm)
  have dnl := (unique_intersection d dl bcd.cross_irrefl.symm)

  have separated := plane_separation anl cnl dnl (by
    intro bsad
    apply bsad.elim
    · rw [Set.member_empty]
      simp
      intro _ _
      exact ⟨b, abc, line_of_left bns⟩
    · exact (OrderGeometry.order_irreflexive abc).left
  )

  have : line b s ⇇ d, c := by
    left
    apply Classical.byContradiction
    intro neg
    rw [Set.member_empty, Classical.not_not] at neg
    have ⟨x, xdc, xbs⟩ := neg
    rw [on_segment] at xdc
    rcases xdc with xd | xc | dxc
    · subst x; exact dnl xbs
    · subst x; exact cnl xbs
    apply snl
    suffices (l = line b s ) by rw [this]; exact line_of_right bns
    symm
    have bnx : b ≠ x := by
      intro bx
      subst x
      apply bcd.exclusive_left
      exact dxc.symm
    calc
      line b s = line b x := by symm; exact line_unique bnx (line_of_left bns) xbs
      line b x = line d c := by
        apply line_unique
        · exact bnx
        · rw [line_symmetric bcd.right_irrefl.symm]
          exact bcd.contains_left
        · apply contains_middle
          exact dxc
      line d c = l := line_unique bcd.right_irrefl.symm dl cl

  have := separated.neg_left this
  rw [<- cut_apart] at this

  have ⟨⟨x, xda, xbs⟩, dna⟩ := this.defn
  rcases on_segment.mp xda with xd | xa | xda <;> try subst x; exfalso
  · exact dnl xbs
  · exact anl xbs
  suffices x = b by { subst x ; exact xda.symm }
  apply Classical.byContradiction
  intro xnb
  have := unique_intersection x ?h xnb
  exact this xbs
  rw [<- line_unique dna dl al]
  exact contains_middle xda

end Betweenness.between
