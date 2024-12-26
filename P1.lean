import Mathlib 
import Mathlib.Tactic.Linarith

--defining sigma as a function with two inputs (f, n)
def m_sum (f : ℕ → ℝ ) (n : ℕ ): ℝ :=
  match n with
     | 0   => f 0
     | n + 1 => f (n + 1) + m_sum f n 

--defining ar^j as the function f in input of sigma
  def f (a r : ℝ) : ℕ → ℝ :=
    fun (n : ℕ ) => a * r ^ n


--proof of the question by induction
  theorem test (a r : ℝ) (h: r ≠ 1) (n : ℕ) : 
     m_sum (f a r) n = (a * (r ^ (n + 1)) - a) / (r - 1) := by
     induction n with
      | zero =>  
        simp [ m_sum, f]
        have Ha : a * (r - 1) = a * r - a := by ring 
        rw [<-Ha]
        refine Eq.symm (mul_div_cancel_right₀ a ?mm) --?mm is a placeholder for required goal to use the refine
        exact sub_ne_zero_of_ne h
      | succ n' ihn =>
        simp[m_sum, f]
        rw [ihn]
        have Ha : 
        a * r ^ (n' + 1) + (a * r ^ (n' + 1) - a) / (r - 1) = 
        (a * r ^ (n' + 1) * (r - 1) + (a * r ^ (n' + 1) - a)) / (r - 1) := by
          refine add_div' (a * r ^ (n' + 1) - a) (a * r ^ (n' + 1)) (r - 1) ?hc
          exact sub_ne_zero_of_ne h
        rewrite [Ha]
        ring
