module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryIdleRead

/-! Select a child branch after restoring the comparison tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open Shared50ModularControl (prime)

/-- The cutoff test restores all stacks before entering the selected branch. -/
theorem chartCutoff_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (cmp : Fin 10 ↪ Fin T) (rank w L cutoff : ℕ) (cutFits : cutoff < 2^L)
    (fits : ((w+1)*rank).size ≤ L) (large leaf : Pr P T Q prime U)
    (a : HS T Q prime U) (S : Stacks T prime)
    (clock : (S.R (cmp 0)).length = w) (word : S.R (cmp 1) = binSyms L cutoff)
    (empty : ∀ j : Fin 10, 2 ≤ j.val → S.R (cmp j) = [])
    (result : Stacks T prime → Prop) (budget : ℝ)
    (selected : ∀ z : HS T Q prime U, ∃ y B, ∃ k : ℕ, y.user = z.user ∧ (k : ℝ) ≤ budget ∧
      Exec body (if cutoff < (w+1)*rank then large else leaf) (mk z S) k (mk y B) ∧ result B) :
    ∃ y B, ∃ k : ℕ, y.user = a.user ∧ (k : ℝ) ≤ (4*w+23*((w+1)*rank)+22*L+51 : ℕ)+budget ∧
      Exec body ((ordinaryCutoffTest cmp rank).seq (.cond (fun z => symBit (z.scan (cmp 7))) large leaf))
        (mk a S) k (mk y B) ∧ result B := by
  obtain ⟨z,m,user,flag,time,test⟩ := ordinaryCutoffTest_exec body cmp rank w L cutoff cutFits fits a S clock word empty
  obtain ⟨y,B,k,same,paid,run,out⟩ := selected z
  have branch : Exec body (.cond (fun z => symBit (z.scan (cmp 7))) large leaf) (mk z S) (k+1) (mk y B) := by
    by_cases active : cutoff < (w+1)*rank
    · exact Exec.cond_true (by simp [mk_var,flag,active]) (by simpa only [ite_eq_left active] using run)
    · exact Exec.cond_false (by simp [mk_var,flag,active]) (by simpa only [ite_eq_right active] using run)
  refine ⟨y,B,m+(k+1),same.trans user,?_,Exec.seq test branch,out⟩
  have testPaid : ((m+1 : ℕ) : ℝ) ≤ ((4*w+23*((w+1)*rank)+22*L+51 : ℕ) : ℝ) := by exact_mod_cast (by omega : m+1 ≤ _)
  push_cast at testPaid ⊢
  linarith

end IntegerMultBounds.MathlibTM2.M6.BitNode
