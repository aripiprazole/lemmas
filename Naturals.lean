inductive ℕ : Type where
  | zero : ℕ
  | succ : ℕ → ℕ
open ℕ

def ℕ.add : ℕ → ℕ → ℕ
  | zero, n   => n
  | succ n, m => succ (add n m)

-- Defines a notation for ℕ.add, so it's easier to use
-- and proof things about `+`
infixl:65 " + " => ℕ.add

-- Proofs that: 0 + n = n
theorem ℕ.add_zero : ∀ {n : ℕ}, n + zero = n
  | zero   => rfl
  | succ _ => congrArg succ add_zero

-- Proofs that: (m + n) + p = m + (n + p)
--   1. succ (m + n) + p = succ (m + (n + p))
theorem ℕ.add_assoc : ∀ {m n p : ℕ}, (m + n) + p = m + (n + p)
  | zero, _, _   => rfl
  | succ _, _, _ => congrArg succ add_assoc

-- Proofs that: 1 + 1 = 2 by reflection
example : (succ zero) + (succ zero) = (succ (succ zero)) := rfl