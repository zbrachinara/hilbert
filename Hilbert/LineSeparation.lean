import Hilbert.Geometry
import Hilbert.Lemmas

def line_sidedness {point} [OrderGeometry point] (l : Line point) (p q : point) :=
  (segment p q) ∩ l = {} ∨ p = q

-- TODO workshop notation, doesn't look good without parentheses
notation l " ⇇ " x:40 ", " y:40 => line_sidedness l x y
notation x " ⇇ " l " ⇉ " y:40 => ¬ line_sidedness l x y

theorem line_sidedness_symmetric {point} [geo : OrderGeometry point]
  {a b : point} {l : Line point} :
  l ⇇ a, b → l ⇇ b, a := by
  intro ab
  cases ab
  · left; rw [segment_symm]; assumption
  · right; symm; assumption

theorem line_sidedness_transitivity_lemma {point} [geo : OrderGeometry point]
  {a b c : point} {l : Line point}:
  l ⇇ a, b → l ⇇ b, c → ¬Colinear a c b → l ⇇ a, c := by
  intro ab bc noncolinear

  -- discharging trivial cases
  rcases ab; case inr t => rw [t]; assumption
  case inl ab =>
  cases bc; case inr t => rw [<- t]; left; assumption
  case inl bc =>

  left
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

theorem line_sidedness_is_equivalence {point} [geo : OrderGeometry point] :
  ∀ l : Line point, Equivalence (line_sidedness l) := by
  intro l
  constructor
  · intro x; right; rfl
  · exact line_sidedness_symmetric
  · intro x y z xy yz

    refine Classical.byCases ?false (line_sidedness_transitivity_lemma xy yz)
    intro colinear

    have : l ≠ line_of x y := by
      intro neg
      -- subst l
      have := colinear.contains_middle
      rw [<- neg] at this
      sorry -- obtain contradiction with yz

    have ⟨p, pl, pnxy⟩ := unshared_point l (line_of x y) this
    have ⟨p', pyp⟩:= geo.extension p y
    have yp': l ⇇ y, p' := by
      left
      sorry

    have xp' := line_sidedness_transitivity_lemma xy yp' sorry
    have p'y := line_sidedness_transitivity_lemma (line_sidedness_symmetric yp') yz sorry
    apply line_sidedness_transitivity_lemma xp' p'y
    sorry

theorem plane_separation {point} [geo : OrderGeometry point] :
  ∀ l : Line point, ∀ a b p ∈ Set.every point - l, (a ⇇ l ⇉ b) → (l ⇇ p, a) ∨ (l ⇇ p, b)
  := by sorry

theorem line_separation {point} [geo : OrderGeometry point] : ∀ l ∈ geo.line, ∀ a b c p ∈ l,
  ⟪a ∗ c ∗ b⟫ → p ≠ c → ⟪a ∗ p ∗ c⟫ ∨ ⟪c ∗ p ∗ b⟫
  := by sorry
