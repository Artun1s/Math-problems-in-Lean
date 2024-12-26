import Mathlib 
import Mathlib.Tactic.Linarith

--defining function f in question 3 as function g
def g (n : Nat) : Nat :=
    match n with 
    | 0 => 0  /- absurd case -/
    | 1 => 1
    | 2 => 5 
    | n + 3 => g (n + 2) + 2 * g (n + 1) 
-- since n>2 in function f, hence n + 2 + 1 in g.

--the following is a helper lemma for proving theorem q4ifelse
 theorem q4helperfirst : forall (u : Nat),
  1 + 2 ^ (2 * u) * 4 + (2 ^ (2 * u) * 2 - 1) * 2 = 2 ^ (2 * u) * 8 - 1 := by 
  intro u
  have ha : 1 <= 2 ^ (2 * u) * 2  := by exact NeZero.one_le 
  omega 
  
   
 --the following is a helper lemma for proving theorem q4ifelse   
 theorem q4helpersecond : forall (u : Nat), 
  2 + (2 ^ (u * 2) * 8 - 1) + 2 ^ (u * 2) * 8 = 1 + 2 ^ (u * 2) * 16 := by 
  intro u 
  have ha : 1 <= 2 ^ (u * 2) * 8 := by exact NeZero.one_le
  have hb : 2 + (2 ^ (u * 2) * 8 - 1) + 2 ^ (u * 2) * 8 =
    2 + 2 ^ (u * 2) * 8 - 1 + 2 ^ (u * 2) * 8 := by omega
  omega  
  
    
--proof of question 3
 theorem q4ifelse  : forall (n : Nat), 0 < n -> 
  g n = if n%2 = 0 then 2^n + 1 else 2^n - 1:= by
    intro n 
    induction n using Nat.strong_induction_on 
    rename_i n ih 
    intro ha
    cases n with 
    | zero => 
      contradiction
    | succ n' => 
      cases n' with --Based of g 's definition we have to use cases on n', it means n = 1 case
      | zero => 
        simp [g]
      | succ n'' => 
        cases n'' with --Based of g 's definition we have to use cases on n'', it means n = 2 case
        | zero => 
          simp [g]
        | succ n''' => --Based of g's definition we have to use cases on n''', it means n = 3 case
          simp [g]
          repeat rw[ih] --applying ih on goals as much as it's needed
          ring_nf
          rcases Nat.even_or_odd' n''' with ⟨u, hu | hu⟩ --pattern matching over Nat.even_or_odd
          rw [hu]
          have hb : (2 + 2 * u) % 2 = 0 := by omega
          rw[hb]; simp
          apply q4helperfirst
          rw [hu]
          have hb : (2 + (2 * u + 1)) % 2 = 1 := by omega 
          rw [hb]; simp 
          have hc : (1 + (2 * u + 1)) % 2 = 0 := by omega 
          rw [hc]; simp 
          have hd : (3 + (2 * u + 1)) % 2 = 0 := by omega 
          rw [hd]; simp 
          ring_nf
          apply q4helpersecond
          omega
          omega
          omega
          omega
          