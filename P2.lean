import Mathlib
--defining the bionomial function with factorial
def m_bin (n k : ℕ) : ℕ := Nat.div (n.factorial) (k.factorial * (n - k).factorial)
--proof for part (i)_1
theorem q3_1 (n : ℕ) : m_bin n 0 = 1 := by 
  cases n with 
    | zero => simp [m_bin]
    | succ n' => simp [m_bin]; apply Nat.div_self; apply Nat.factorial_pos
--proof for part (i)_2
theorem q3_2 (n : ℕ) : m_bin n n = 1 := by
  simp [m_bin]; apply Nat.div_self; apply Nat.factorial_pos

--proof for part (ii)
theorem q3_3 (n k : ℕ) (h : k ≤ n) : m_bin n k = m_bin n (n - k) := by 
  simp [m_bin]
  have hk : n - (n - k) = k := by omega
  simp [hk]
  simp [Nat.mul_comm]
