module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarCounters

/-! # Release all temporary scalar setup banks after generating readiness -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem bank_covers (k : Fin 117) (hk : k.val < 20) : ∃ r, bank r = k := by
  by_cases hv : k.val < 5
  · exact ⟨.v ⟨k.val, hv⟩, Fin.ext rfl⟩
  · by_cases h5 : k.val = 5
    · exact ⟨.wr, Fin.ext h5.symm⟩
    · by_cases h6 : k.val = 6
      · exact ⟨.wn, Fin.ext h6.symm⟩
      · by_cases h7 : k.val = 7
        · exact ⟨.acc, Fin.ext h7.symm⟩
        · refine ⟨.z ⟨k.val - 8, by omega⟩, ?_⟩
          apply Fin.ext
          simp only [bank, ForwardBankPlacement.code]
          omega

theorem counterR_off {A : ℕ} (q w : ℕ) (R : Regs 117 A) (k : Fin 117) (hk : k.val < 26) :
    counterR q w R k = R k := by
  have hn (r : CR) : k ≠ cr r := by
    have hh := (cr_range r).1
    intro h
    have he := congrArg Fin.val h
    omega
  simp [counterR, hn]

/-- Each temporary setup word has at most the selected binary width. -/
theorem loadedR_length {A : ℕ} (q w : ℕ) (S : Stacks 117 A)
    (hclean : ∀ k : Fin 117, k.val < 26 → S.R k = []) (k : Fin 117) (hk : k.val < 26) :
    (loadedR q w S.R k).length ≤ w := by
  by_cases hb : k.val < 20
  · obtain ⟨r, rfl⟩ := bank_covers k hb
    have hh := loadBank_holds q w S hclean r
    change loadedR q w S.R (bank r) = tblRho w (List.replicate w tick) (List.replicate w tick) (bankState q w) r at hh
    rw [hh]
    cases r <;> simp [tblRho, bankState]
  · unfold loadedR
    rw [chirpBankLoad_off _ _ _ _ _ _ _ (by
      intro r
      have hr := bank_lt r
      intro h
      have he := congrArg Fin.val h
      omega)]
    simp only [unarySetupR, Function.update_apply]
    split_ifs <;> simp [hclean k hk]

def setupPorts : List (Fin 117) := List.ofFn fun i : Fin 26 => ⟨i.val, by omega⟩

@[simp] theorem mem_setupPorts (k : Fin 117) : k ∈ setupPorts ↔ k.val < 26 := by
  simp only [setupPorts, List.mem_ofFn]
  constructor
  · rintro ⟨i, hi⟩
    have he := congrArg (fun j : Fin 117 => j.val) hi
    change i.val = k.val at he
    have hh := i.isLt
    omega
  · intro hk
    exact ⟨⟨k.val, hk⟩, Fin.ext rfl⟩

theorem setupPorts_nodup : setupPorts.Nodup := by
  rw [setupPorts, List.nodup_ofFn]
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 117 => k.val) h)

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def prepare : Pr P 117 Q A U := .seq counterSetup (clearWords setupPorts)

def prepareCost (q w : ℕ) : ℕ := counterSetupCost q w + 52 * w + 53

/-- All scalar readiness counters are executed from unary q/w; every binary
bank and temporary word is released. Exactly the three installed counters change. -/
theorem prepare_exec_of_width (q w : ℕ) (hw5 : 5 ≤ w) (hw : q + 4 ≤ w)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hqR : (S.R 100).length = q) (hwR : (S.R 94).length = w)
    (hclean : ∀ k : Fin 117, k.val < 26 → S.R k = [])
    (hcounters : ∀ r ∈ [CR.wn, .pn, .nn], S.R (cr r) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCost q w ∧
      Exec body prepare (mk v S) m (mk v' { S with R := counterR q w S.R }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := counterSetup_exec_of_width (body := body) q w hw5 hw v S hqR hwR hclean hcounters
  let S₁ : Stacks 117 A := { S with R := counterR q w (loadedR q w S.R) }
  obtain ⟨v₂, hu₂, he₂⟩ := clearWords_exec (body := body) setupPorts setupPorts_nodup v₁ S₁
  have hsum : (setupPorts.map (fun k => (S₁.R k).length)).sum ≤ 26 * w := by
    have hh := List.sum_le_length_nsmul (setupPorts.map (fun k => (S₁.R k).length)) w (by
      intro n hn
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hn
      have hk' := (mem_setupPorts k).mp hk
      simpa only [S₁, counterR_off q w _ k hk'] using loadedR_length q w S hclean k hk')
    simpa [setupPorts] using hh
  refine ⟨v₂, m₁ + (2 * (setupPorts.map (fun k => (S₁.R k).length)).sum + 2 * setupPorts.length + 1),
    hu₂.trans hu₁, ?_, (Exec.seq he₁ he₂).cast rfl ?_⟩
  · have hlen : setupPorts.length = 26 := by simp [setupPorts]
    rw [hlen]
    unfold prepareCost
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k.val < 26
    · simp [hk, counterR_off q w S.R k hk, hclean k hk]
    · simp only [mem_setupPorts, ite_eq_right hk, S₁]
      simp only [counterR, Function.update_apply]
      split_ifs <;> first | rfl | exact loadedR_off q w S.R k (by omega)

theorem prepare_exec (q w : ℕ) (hq : 1 ≤ q) (hw : q + 4 ≤ w)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hqR : (S.R 100).length = q) (hwR : (S.R 94).length = w)
    (hclean : ∀ k : Fin 117, k.val < 26 → S.R k = [])
    (hcounters : ∀ r ∈ [CR.wn, .pn, .nn], S.R (cr r) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCost q w ∧
      Exec body prepare (mk v S) m (mk v' { S with R := counterR q w S.R }) := by
  exact prepare_exec_of_width (body := body) q w (by omega) hw v S hqR hwR hclean hcounters

/-- Closed setup endpoint on the actual phase-cell bank: readiness and clean
multiplier tapes follow from execution, rather than being caller oracles. -/
theorem prepareCanonical_exec (q l w M L : ℕ) (hq : 1 ≤ q) (hw : q + 4 ≤ w)
    (X V : ℕ → List GaussianInt) (v : HS 117 Q A U) (tail : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := Fixed.start q l w M L L X V tail inp out
    let SF := { S with R := counterR q w S.R }
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCost q w ∧
      Exec body prepare (mk v S) m (mk v' SF) ∧
      Ready (fun r => SF.R (cr r)) w q ∧ CClean mul SF := by
  dsimp only
  let S := Fixed.start q l w M L L X V tail inp out
  obtain ⟨v', m, hu, hm, he⟩ := prepare_exec (body := body) q w hq hw v S
    (by simp [S, Fixed.start, Fixed.inputBank]) (by simp [S, Fixed.start, Fixed.inputBank])
    (by
      intro k hk
      simp [S, Fixed.start, Fixed.inputBank,
        show k.val ≠ 94 by omega, show k.val ≠ 100 by omega,
        show k.val ≠ 101 by omega, show k.val ≠ 102 by omega,
        show k.val ≠ 103 by omega, show k.val ≠ 108 by omega,
        show k.val ≠ 110 by omega, show k.val ≠ 111 by omega, show k.val ≠ 93 by omega])
    (fun r _ => cr_fresh q l w M L X V tail inp out r)
  refine ⟨v', m, hu, hm, he, counterR_ready q w S.R
    (fun r => cr_fresh q l w M L X V tail inp out r), ?_⟩
  intro i
  constructor
  · rfl
  · have hh := (mul_clean q l w M L X V tail inp out i).2
    simpa [counterR, (cr_mul .wn i).symm, (cr_mul .pn i).symm, (cr_mul .nn i).symm] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
