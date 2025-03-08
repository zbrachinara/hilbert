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

theorem line_sidedness_is_equivalence {point} [OrderGeometry point] :
  ∀ l : Line point, Equivalence (line_sidedness l) := by
  intro l
  constructor
  · intro x; right; rfl
  · exact line_sidedness_symmetric
  · intro x y z xy yz

    rcases xy; case inr t => rw [t]; assumption
    case inl xy =>
    left
    cases yz; case inr t => rw [<- t]; assumption
    case inl yz =>

    refine Classical.byCases ?false (transitivity_lemma xy yz)
    intro colinear

    have : l ≠ line_of x y := by
      intro neg
      have := colinear.contains_middle
      rw [<- neg] at this
      apply Set.member_empty yz
      exact ⟨z, segment_has_right y z, this⟩

    have ⟨p, pl, pnxy⟩ := unshared_point l (line_of x y) this
    have ⟨p', pyp'⟩:= OrderGeometry.extension p y -- TODO extract this construction and relevant proofs
    have yp': segment y p' ∩ l = ∅ := by
      apply Set.empty_not_exists
      intro t tl
      rw [Set.mem_inter, <- mem_line_locus] at tl
      suffices y ∈ l by
        apply Set.member_empty yz
        refine ⟨y, segment_has_left y z, this⟩
      rcases on_segment tl.left with ty | tp' | ytp' <;> try subst t
      · exact tl.right
      · have : l = line_of p p' := by
          have := IncidenceGeometry.unique_line p p' l
          apply this.mp
          exact ⟨pl, tl.right⟩
        subst this
        exact pyp'.contains_middle
      suffices l = line_of y p' by subst l; exact line_of_left
      calc
        _ = line_of p t := by
          have := IncidenceGeometry.unique_line p t l
          exact this.mp ⟨pl, tl.right⟩
        _ = _ := by
          symm
          apply (IncidenceGeometry.unique_line p t (line_of y p')).mp
          constructor
          exact between.contains_left pyp'
          exact between.contains_middle ytp'

    -- from p' ∉ line_of x y I can derive every noncolinearity necessary
    have p'_extralinear : p' ∉ line_of x y := by
      intro neg
      apply pnxy
      have := IncidenceGeometry.unique_line y p' (line_of x y)
      have := this.mp ⟨line_of_right, neg⟩
      rw [this]
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

theorem line_separation {point} [geo : OrderGeometry point] : ∀ l ∈ geo.line, ∀ a b c p ∈ l,
  ⟪a ∗ c ∗ b⟫ → p ≠ c → ⟪a ∗ p ∗ c⟫ ∨ ⟪c ∗ p ∗ b⟫
  := by sorry
