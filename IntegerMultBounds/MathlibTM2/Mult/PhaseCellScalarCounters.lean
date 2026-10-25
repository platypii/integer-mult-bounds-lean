module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarBank
public import IntegerMultBounds.MathlibTM2.Mult.ChirpMultiplierSetup

/-! # Generate all three scalar multiplier counters from unary q and w -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def counterSetup : Pr P 117 Q A U := .seq loadBank (chirpMultiplierSetup bank cr)

def counterSetupCost (q w : ℕ) : ℕ :=
  (q + w) * (4 * w + 10) + 12 * w + 20 + chirpBankLoadCost bank bankInput w w (inputBits w) +
    chirpMultiplierSetupCost w w q w

/-- The exact installed counters are generated, including topN(w). The loaded
binary bank remains explicit until the subsequent paid cleanup step. -/
theorem counterSetup_exec_of_width (q w : ℕ) (hw5 : 5 ≤ w) (hw : q + 4 ≤ w)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hqR : (S.R 100).length = q) (hwR : (S.R 94).length = w)
    (hclean : ∀ k : Fin 117, k.val < 26 → S.R k = [])
    (hcounters : ∀ r ∈ [CR.wn, .pn, .nn], S.R (cr r) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ counterSetupCost q w ∧
      Exec body counterSetup (mk v S) m
        (mk v' { S with R := counterR q w (loadedR q w S.R) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := loadBank_exec_of_width (body := body) q w hw5 hw v S hqR hwR hclean
  let S₁ : Stacks 117 A := { S with R := loadedR q w S.R }
  have hS₁ := loadBank_holds q w S hclean
  have hroom := unarySetup_room_of_width hw5 hw
  have hout : ∀ r ∈ [CR.wn, .pn, .nn], ∀ i, bank i ≠ cr r := by
    intro r _ i
    have hi := bank_lt i
    have hr := (cr_range r).1
    intro h
    have he := congrArg Fin.val h
    omega
  have hblank (r : CR) (hr : r ∈ [CR.wn, .pn, .nn]) : loadedR q w S.R (cr r) = [] := by
    rw [loadedR_off q w S.R (cr r) (by have hh := (cr_range r).1; omega)]
    exact hcounters r hr
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := chirpMultiplierSetup_exec (body := body)
    bank_injective cr hout (List.replicate w tick) (List.replicate w tick)
    (by simp) (by simp) le_rfl (bankState q w) q w rfl rfl (by omega) hroom.2.2
    (by intro i hi; fin_cases i <;> first | (simp at hi; done) | simp [bankState])
    (by intro i; fin_cases i <;> simp [bankState, hroom.1, hroom.2.1])
    v₁ S₁ hS₁
  have hR : unaryCopiesR (chirpMultiplierDimensionValues q w) (loadedR q w S.R)
      (chirpMultiplierAssignments cr) = counterR q w (loadedR q w S.R) := by
    simp [unaryCopiesR, chirpMultiplierAssignments, chirpMultiplierDimensionValues,
      cr_injective.eq_iff, hblank .wn (by simp), hblank .pn (by simp), hblank .nn (by simp), counterR]
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by unfold counterSetupCost; omega, ?_⟩
  exact Exec.seq he₁ (by simpa only [S₁, hR] using he₂)

theorem counterSetup_exec (q w : ℕ) (hq : 1 ≤ q) (hw : q + 4 ≤ w)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hqR : (S.R 100).length = q) (hwR : (S.R 94).length = w)
    (hclean : ∀ k : Fin 117, k.val < 26 → S.R k = [])
    (hcounters : ∀ r ∈ [CR.wn, .pn, .nn], S.R (cr r) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ counterSetupCost q w ∧
      Exec body counterSetup (mk v S) m
        (mk v' { S with R := counterR q w (loadedR q w S.R) }) := by
  exact counterSetup_exec_of_width (body := body) q w (by omega) hw v S hqR hwR hclean hcounters

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
