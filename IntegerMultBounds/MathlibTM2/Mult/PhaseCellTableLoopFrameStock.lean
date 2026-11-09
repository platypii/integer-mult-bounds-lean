module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableLoopInvariant
public import IntegerMultBounds.MathlibTM2.Host.BankGrowth
import Mathlib.Tactic.FinCases

/-! Canonical table boundaries charge packed output and the retained index.
Moving the scan counter between its two tapes changes no stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
variable {A s q w W k m : ℕ} [NeZero s] {B : Finset (ZMod s)}
  {Sh : Matrix (ZMod s) (ZMod s) ℝ} {ε : ℝ} {base R : Regs 154 A}

theorem TableLoopInvariant.index_length (h : TableLoopInvariant q w B W Sh ε base k R) :
    (R 151).length = k := by
  obtain ⟨columns,hlen,_,_,hframe⟩ := h
  rw [hframe 151 (by decide) (by decide)]
  simpa [tableLoopRegs] using hlen

theorem TableLoopInvariant.output_storage (h : TableLoopInvariant q w B W Sh ε base k R) :
    (R 132).length ≤ (base 132).length+k*(2*W+1)*w := by
  obtain ⟨columns,hlen,_,_,hframe⟩ := h
  have hs := bandTableWords_storage A w B W columns 0
  rw [hlen] at hs
  rw [hframe 132 (by decide) (by decide)]
  simp only [tableLoopRegs,Function.update_of_ne (by decide : (132 : Fin 154) ≠ 151),
    Function.update_self,List.length_append]
  omega

/-- All other storage is unchanged between two canonical scan boundaries.
The arithmetic reserve therefore need not be multiplied by the column count. -/
theorem TableLoopInvariant.stock_balance {Q : ℕ} {U : Type}
    (v v' : HS 154 Q A U) (S F : Stacks 154 A)
    (hS : TableLoopInvariant q w B W Sh ε base k S.R)
    (hF : TableLoopInvariant q w B W Sh ε base m F.R)
    (hi : F.inp = S.inp) (ho : F.out = S.out) (hl : F.L = S.L)
    (hclock : (F.R 152).length+(F.R 153).length = (S.R 152).length+(S.R 153).length) :
    mnSize (mk v' F)+(S.R 132).length+k = mnSize (mk v S)+(F.R 132).length+m := by
  have hindexS := hS.index_length
  have hindexF := hF.index_length
  obtain ⟨columns,_,_,_,hframeS⟩ := hS
  obtain ⟨columns',_,_,_,hframeF⟩ := hF
  let roles : Fin 4 → Fin 154 := ![132,151,152,153]
  let words : Fin 4 → List (Fin (A+4)) := ![F.R 132,F.R 151,F.R 152,F.R 153]
  have hb := mn_replace_bank_size roles (by decide) v v' S F words
    (by intro i; fin_cases i <;> simp [roles,words])
    (by
      intro r hr
      have h132 := (hr 0).symm
      have h151 := (hr 1).symm
      have h152 := (hr 2).symm
      have h153 := (hr 3).symm
      change r ≠ 132 at h132
      change r ≠ 151 at h151
      change r ≠ 152 at h152
      change r ≠ 153 at h153
      rw [hframeF r h152 h153,hframeS r h152 h153]
      simp [tableLoopRegs,h132,h151]) hi ho hl
  simp [roles,words,Fin.sum_univ_succ,hindexS,hindexF] at hb
  omega

/-- Publishing columns preserves the caller's existing output suffix. -/
theorem TableLoopInvariant.output_length_mono
    (h : TableLoopInvariant q w B W Sh ε base k R) :
    (base 132).length ≤ (R 132).length := by
  obtain ⟨columns,_,_,_,hframe⟩ := h
  rw [hframe 132 (by decide) (by decide)]
  simp [tableLoopRegs]

/-- A canonical boundary needs only retained table words and index ticks beyond
an earlier boundary. The scan counter itself is transported without growth. -/
theorem TableLoopInvariant.stock_le {Q : ℕ} {U : Type}
    (v v' : HS 154 Q A U) (S F : Stacks 154 A)
    (hS : TableLoopInvariant q w B W Sh ε base k S.R)
    (hF : TableLoopInvariant q w B W Sh ε base m F.R)
    (hi : F.inp = S.inp) (ho : F.out = S.out) (hl : F.L = S.L)
    (hclock : (F.R 152).length+(F.R 153).length = (S.R 152).length+(S.R 153).length) :
    mnSize (mk v' F) ≤ mnSize (mk v S)+m*((2*W+1)*w+1) := by
  have hb := hS.stock_balance v v' S F hF hi ho hl hclock
  have hs := hS.output_length_mono
  have hf := hF.output_storage
  have hm : m*((2*W+1)*w+1) = m*(2*W+1)*w+m := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  rw [hm]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
