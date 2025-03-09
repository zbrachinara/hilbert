def Dichotomy (a b : Prop) : Prop := (a ∧ ¬ b) ∨ (¬ a ∧ b)

namespace Dichotomy

variable (di : Dichotomy a b)

def either : a ∨ b := by
  rcases di with h | h
  · left; exact h.left
  · right; exact h.right

def neg_left : b → ¬ a := by
  intro b
  rcases di with ⟨_, f⟩ | ⟨t, _⟩
  · exact False.elim (f b)
  · exact t

def neg_right : a → ¬ b := by
  intro a
  rcases di with ⟨_, t⟩ | ⟨f, _⟩
  · exact t
  · exact False.elim (f a)

end Dichotomy

def Trichotomy (a b c : Prop) : Prop := (a ∧ b ∧ ¬ c) ∨ (a ∧ ¬ b ∧ c) ∨ (¬ a ∧ b ∧ c)

namespace Trichotomy

variable (tri : Trichotomy a b c)

def any : a ∨ b ∨ c := by
  rcases tri with ⟨t, _, _⟩ | ⟨_, _, t⟩ | ⟨_, _, t⟩
  · left; exact t
  · right; right; exact t
  · right; right; exact t

def reduce_left : a → Dichotomy b c := by
  intro a
  rcases tri with ⟨_, l⟩ | ⟨_, r⟩ | ⟨f, _⟩
  · left; exact l
  · right; exact r
  · exact False.elim (f a)

def reduce_right : c → Dichotomy a b := by
  intro c
  rcases tri with ⟨_, _, f⟩ | ⟨l₁, l₂, _⟩ | ⟨r₁, r₂, _⟩
  · exact False.elim (f c)
  · left; exact ⟨l₁, l₂⟩
  · right; exact ⟨r₁, r₂⟩

def reduce_middle : b → Dichotomy a c := by
  intro b
  rcases tri with ⟨l₁, _, l₂⟩ | ⟨_, f, _⟩ | ⟨r₁, _, r₂⟩
  · left; exact ⟨l₁, l₂⟩
  · exact False.elim (f b)
  · right; exact ⟨r₁, r₂⟩

end Trichotomy
