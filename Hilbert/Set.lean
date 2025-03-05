def Set α := α -> Prop

namespace Set

instance member {α} : Membership α (Set α) where
  mem s a := s a

axiom ext {α} {s₁ s₂ : Set α} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂

instance empty {α : Type u} : EmptyCollection (Set α) where
  emptyCollection := λ _ ↦ False
instance singleton {α} : Singleton α (Set α) where
  singleton x := λ y ↦ y = x
instance insert {α} : Insert α (Set α) where
  insert x s := λ y ↦ y = x ∨ y ∈ s

/-- Illustration: The order of elements in a set is irrelevant -/
example : ({1, 2, 3} : Set Int) = {1, 3, 2} := by
  apply ext
  intro x
  simp [insert, singleton, member]
  rw [@or_comm (x = 2)]

syntax "{" ident " ∈ " term " | " term "}" : term
macro_rules
| `({ $x ∈ $s | $fx }) => `(λ $x ↦ $x ∈ $s ∧ $fx)
def ℤ : Set Int := λ _ ↦ True
#check {x ∈ ℤ | x = 1}

syntax "{" term "|" Lean.binderIdent "∈" term "}" : term
macro_rules
| `({ $fx | $x ∈ $s }) => `({y ∈ $s | ∃ $x ∈ $s, $fx = y})
#check {2 * n | n ∈ ℤ}

def subset {α} (s₁ s₂ : Set α) := ∀ a, a ∈ s₁ → a ∈ s₂
notation a:40 " ⊆ " b:40 => subset a b
/-- Aluffi adopts ⊂ as the same as ⊆, and ⊊ for strict subsets. -/
notation a:40 " ⊂ " b:40 => a ⊆ b

def strict_subset {α} (s₁ s₂ : Set α) := s₁ ⊆ s₂ ∧ s₁ ≠ s₂
notation a:40 " ⊊ " b:40 => strict_subset a b

def every (α) : Set α := λ _ ↦ True
def power_set {α} (s : Set α) := {s' ∈ every (Set α) | s' ⊆ s}

instance {α : Type} : Union (Set α) where
  union a b := λ x ↦ x ∈ a ∨ x ∈ b

instance {α : Type} : Inter (Set α) where
  inter a b := λ x ↦ x ∈ a ∧ x ∈ b

instance {α : Type} : Sub (Set α) where
  sub a b := λ x ↦ x ∈ a ∧ x ∉ b

end Set

-- Hack to prevent overloading -- only recognize this form if it has more than one binder (lmao)
syntax (name := all_members_imply) "∀ " ident ident+ " ∈ " term ", " term : term
@[macro all_members_imply]
macro_rules
| `(∀ $x' $x'' $xs* ∈ $set, $consequence) => do
  let consequence' ← xs.foldrM (λ x t ↦ `($x ∈ $set → $t)) consequence
  `(∀ $x' $x'' $xs*, $x' ∈ $set → $x'' ∈ $set → $consequence')

syntax (name := exist_members_st) "∃ " ident ident+ " ∈ " term ", " term : term
@[macro exist_members_st]
macro_rules
| `(∃ $x' $x'' $xs* ∈ $set, $consequence) => do
  let consequence' ← xs.foldrM (λ x t ↦ `($x ∈ $set ∧ $t)) consequence
  `(∃ $x':ident $x'':ident $[$xs:ident]*, $consequence')
