module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRoundHeaders

/-! Restoring the scalar bank leaves only the advertised generated counter ports changed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM

theorem roundHeader_frame {T A n m : ℕ} (rg : TblR n → Fin T) (ports : Fin m → Fin T)
    (S S' : Stacks T A) (ρ : TblR n → List (Fin (A+4)))
    (hS : tblHolds rg S ρ) (hS' : tblHolds rg S' ρ)
    (hframe : ∀ k, (∀ r, rg r ≠ k) → (∀ i, ports i ≠ k) → S'.R k = S.R k)
    (k : Fin T) (hk : ∀ i, ports i ≠ k) : S'.R k = S.R k := by
  by_cases hr : ∃ r, rg r = k
  · obtain ⟨r,rfl⟩ := hr
    exact (hS' r).trans (hS r).symm
  · exact hframe k (by simpa using hr) hk

/-- Separate counter ports from the data and scratch ports once, before numerical instantiation. -/
theorem roundPorts_separate {T : ℕ} {ports : Fin 4 → Fin T} {src dst tmp sp sg cy : Fin T}
    (hreg : [src,dst,tmp,ports 0,ports 1,ports 2,ports 3,sp,sg,cy].Nodup) :
    ∀ i, ∀ r ∈ [src,dst,tmp,sp,sg,cy], ports i ≠ r := by
  regs_ne hreg
  intro i r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> fin_cases i <;> simp_all [ne_comm]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
