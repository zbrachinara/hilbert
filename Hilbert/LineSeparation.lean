import Hilbert.Geometry
import Hilbert.Lemmas

def line_sidedness {point} [OrderGeometry point] (l : Line point) (p q : point) :=
  (segment p q) ∩ l = {} ∨ p = q

-- TODO workshop notation, doesn't look good without parentheses
notation l " ⇇ " x:40 ", " y:40 => line_sidedness l x y
notation x " ⇇ " l " ⇉ " y:40 => ¬ line_sidedness l x y

theorem line_sidedness_symmetric {point} [geo : OrderGeometry point]
  {a b : point} {l : Line point} : l ⇇ a, b → l ⇇ b, a := by
  intro ab
  cases ab
  · left; rw [segment_symm]; assumption
  · right; symm; assumption

/--
  Transitivity of line-sidedness, with three specifically nontrivial and noncolinear points.
-/
theorem transitivity_lemma {point} [geo : OrderGeometry point]
  {a b c : point} {l : Line point}:
  segment a b ∩ l = ∅ → segment b c ∩ l = ∅ → ¬Colinear a c b → segment a c ∩ l = ∅ := by
  intro ab bc noncolinear

  apply Classical.byContradiction
  intro neg
  have ⟨d, ds⟩ := Set.nonempty_exists neg
  have ⟨dac, dl⟩ := Set.mem_inter.mp ds
  rcases on_segment dac with da | dc | dac
  · sorry  -- dl, dx, xy create a contradiction
  · sorry -- similarly dl, dz yz
  rcases Classical.em (b ∈ l) with bl | bnl
  · sorry
  rcases geo.pasch noncolinear d dac l dl bnl with ⟨p, pl, pxy | pzy⟩
  sorry
  sorry

/--
  No matter how we cut a line `l`, for any point `x` on `l` that is not on the cut, there is a
  point `p` which is on the same side of the cut as `x`.

  This theorem is used to create a point outside of a set of colinear points on the same side of a
  cut as these points.
 -/
private theorem line_cut_lemma {point} [OrderGeometry point] (l cut : Line point) :
  l ≠ cut → ∀ x ∈ l, x ∉ cut → ∃ p, segment x p ∩ cut = ∅ ∧ p ∉ l := by
  intro lncut x xl xncut -- TODO we do not need l ≠ cut (needs classical reasoning)
  have ⟨p, psep, pnl⟩ := unshared_point l cut lncut
  have ⟨p', pxp'⟩ := OrderGeometry.extension p x
  exists p'
  constructor

  -- Part 1 -- the segment x p' does not go through the cut
  apply Set.empty_not_exists
  intro y yl
  rw [Set.mem_inter, mem_line] at yl
  suffices x ∈ cut by
    sorry

  sorry

  -- Part 2 -- p' doesn't lie on this line
  sorry

theorem line_sidedness_is_equivalence {point} [OrderGeometry point] :
  ∀ l : Line point, Equivalence (line_sidedness l) := by
  intro l
  constructor
  · intro x; right; rfl
  · exact line_sidedness_symmetric
  · intro x y z xy yz

    -- Discharge trivial cases
    rcases xy; case inr t => rw [t]; assumption
    case inl xy =>
    left
    cases yz; case inr t => rw [<- t]; assumption
    case inl yz =>

    refine Classical.byCases ?false (transitivity_lemma xy yz)
    intro colinear

    have : l ≠ line x y := by
      intro neg
      have := colinear.contains_middle
      rw [<- neg] at this
      apply Set.member_empty yz
      exact ⟨z, segment_has_right y z, this⟩

    have ⟨p, pl, pnxy⟩ := unshared_point l (line x y) this
    have ⟨p', pyp'⟩:= OrderGeometry.extension p y -- TODO extract this construction and relevant proofs
    have yp': segment y p' ∩ l = ∅ := by
      apply Set.empty_not_exists
      intro t tl
      rw [Set.mem_inter, mem_line] at tl
      suffices y ∈ l by
        apply Set.member_empty yz
        refine ⟨y, segment_has_left y z, this⟩
      rcases on_segment tl.left with ty | tp' | ytp' <;> try subst t
      · exact tl.right
      · rw [<- line_unique pl tl.right]
        exact pyp'.contains_middle
      suffices l = line y p' by subst l; exact line_of_left
      calc
        _ = line p t := by symm; exact line_unique pl tl.right
        _ = _ := line_unique (between.contains_left pyp') (between.contains_middle ytp')

    -- from p' ∉ line_of x y I can derive every noncolinearity necessary
    have p'_extralinear : p' ∉ line x y := by
      intro neg
      apply pnxy
      rw [<- line_unique line_of_right neg]
      exact between.contains_left pyp'
    have p'nxy := extralinear_middle p'_extralinear
    rw [colinear.right_transfers_line] at p'_extralinear
    have p'nyz := extralinear_left  p'_extralinear
    rw [<- colinear.middle_transfers_line] at p'_extralinear
    have p'nxz := extralinear_right p'_extralinear

    have xp' := transitivity_lemma xy yp' p'nxy
    have p'y := transitivity_lemma (by rw [segment_symm] at yp'; exact yp') yz p'nyz
    exact transitivity_lemma xp' p'y p'nxz

theorem plane_separation {point} [geo : OrderGeometry point] :
  ∀ l : Line point, ∀ a b p ∈ Set.every point - l, (a ⇇ l ⇉ b) → (l ⇇ p, a) ∨ (l ⇇ p, b)
  := by sorry

theorem line_separation {point} [geo : OrderGeometry point] : ∀ l ∈ geo.line_set, ∀ a b c p ∈ l,
  ⟪a ∗ c ∗ b⟫ → p ≠ c → ⟪a ∗ p ∗ c⟫ ∨ ⟪c ∗ p ∗ b⟫
  := by sorry
