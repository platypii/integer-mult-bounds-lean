module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceHost
public import IntegerMultBounds.MathlibTM2.Fast.TableFrameStock
import Mathlib.Tactic.FinCases

/-! Saved binary packets move between tapes; only the emitted advance grows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM

theorem originAdvanceNext_stock_le {Q A W e origin advance : ℕ} {U : Type}
    (v v' : HS 117 Q A U) (S F : Stacks 117 A) (st st' : TblSt 4 A)
    (hS : tblHolds advanceReg S (tblRho W (List.replicate W tick) (List.replicate e tick) st))
    (hF : tblHolds advanceReg F (tblRho W (List.replicate W tick) (List.replicate e tick) st'))
    (ha : st'.acc = st.acc) (tail : List (Fin (A+4)))
    (hsrc : S.R 109 = binSyms W origin++tail)
    (hs : F.R 109 = tail)
    (hsave : F.R 89 = (binSyms W origin).reverse++S.R 89)
    (hout : F.R 90 = blank::(List.replicate advance tick++S.R 90))
    (hi : F.inp = S.inp) (ho : F.out = S.out) (hl : F.L = S.L)
    (hframe : ∀ k, k ≠ 109 → k ≠ 89 → k ≠ 90 →
      (∀ r, advanceReg r ≠ k) → F.R k = S.R k) :
    mnSize (mk v' F) ≤ mnSize (mk v S)+advance+1 := by
  let B : Stacks 117 A := {S with R := Function.update (Function.update (Function.update S.R 109 tail)
    89 ((binSyms W origin).reverse++S.R 89)) 90 (blank::(List.replicate advance tick++S.R 90))}
  have hB : tblHolds advanceReg B (tblRho W (List.replicate W tick) (List.replicate e tick) st) := by
    intro r
    have hr := advanceReg_range r
    have h109 : advanceReg r ≠ 109 := by intro he; rw [he] at hr; omega
    have h89 : advanceReg r ≠ 89 := by intro he; rw [he] at hr; omega
    have h90 : advanceReg r ≠ 90 := by intro he; rw [he] at hr; omega
    simpa [B,h109,h89,h90] using hS r
  have hfr : tblFr advanceReg B F := by
    refine ⟨hi,ho,hl,?_⟩
    intro k hk
    by_cases h109 : k = 109
    · subst k; simpa [B] using hs
    by_cases h89 : k = 89
    · subst k; simpa [B] using hsave
    by_cases h90 : k = 90
    · subst k; simpa [B] using hout
    simpa [B,h109,h89,h90] using hframe k h109 h89 h90 hk
  have hbalance := hB.stock_balance v v' hF hfr
  rw [ha] at hbalance
  let roles : Fin 3 → Fin 117 := ![109,89,90]
  let words : Fin 3 → List (Fin (A+4)) :=
    ![tail,(binSyms W origin).reverse++S.R 89,blank::(List.replicate advance tick++S.R 90)]
  have hb := mn_replace_bank_size roles (by decide) v v S B words
    (by intro i; fin_cases i <;> simp [roles,words,B])
    (by
      intro k hk
      have h109 := (hk 0).symm
      have h89 := (hk 1).symm
      have h90 := (hk 2).symm
      change k ≠ 109 at h109
      change k ≠ 89 at h89
      change k ≠ 90 at h90
      simp [B,h109,h89,h90]) rfl rfl rfl
  simp [roles,words,Fin.sum_univ_succ,hsrc,length_binSyms] at hb
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
