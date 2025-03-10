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

def Trichotomy (a b c : Prop) : Prop := (a ∧ ¬ b ∧ ¬ c) ∨ (¬ a ∧ b ∧ ¬ c) ∨ (¬ a ∧ ¬ b ∧ c)

namespace Trichotomy

variable (tri : Trichotomy a b c)

def any : a ∨ b ∨ c := by
  rcases tri with ⟨t, _, _⟩ | ⟨_, t, _⟩ | ⟨_, _, t⟩
  · left; exact t
  · right; left; exact t
  · right; right; exact t

-- TODO rewrite using symmetry
def reduce_left : a → ¬ b ∧ ¬ c := by
  intro a
  rcases tri with ⟨_, t⟩ | ⟨f, _⟩ | ⟨f, _⟩ <;> try exact False.elim (f a)
  exact t

def reduce_right : c → ¬ a ∧ ¬ b := by
  intro c
  rcases tri with ⟨_, _, f⟩ | ⟨_, _, f⟩ | ⟨a, b, _⟩ <;> try  exact False.elim (f c)
  exact ⟨a, b⟩

def reduce_middle : b → ¬ a ∧ ¬ c := by
  intro b
  rcases tri with ⟨_, f, _⟩ | ⟨a, _, c⟩ | ⟨_, f, _⟩ <;> try exact False.elim (f b)
  · exact ⟨a, c⟩

end Trichotomy
