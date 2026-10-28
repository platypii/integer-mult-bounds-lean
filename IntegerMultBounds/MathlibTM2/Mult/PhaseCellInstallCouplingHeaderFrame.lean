module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallCouplingHeaders

/-! Install scalar coupling headers while retaining arbitrary coordinate and page spectators. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

theorem installCouplingHeaders_from_lengths_exec (P q s t u band a b : ℕ)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hsrc : ∀ r ∈ couplingHeaderCopies, (S.R r.1).length = couplingHeaderValue P q s t u band a b r.1)
    (h94 : S.R 94 = []) (h135 : S.R 135 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body installCouplingHeaders (mk v S) (installCouplingHeadersCost P q s t u band a b)
        (mk v' {S with R := couplingHeadersR P q s t u band a b S.R}) := by
  let value := couplingHeaderValue P q s t u band a b
  obtain ⟨v₁,hu₁,he₁⟩ := copyUnaryHeaders_exec (body := body) 135 couplingHeaderCopies
    (by intro r hr
        simp only [couplingHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by intro r hr p hp
        have hd : r.2.val < 117 := by
          simp only [couplingHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        have hs : 117 ≤ p.1.val := by
          simp only [couplingHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        intro he
        have hv := congrArg Fin.val he
        omega) value v S hsrc h135
  let S₁ : Stacks 144 A := {S with R := unaryCopiesR value S.R couplingHeaderCopies}
  have hoff (k : Fin 144) (hk : k ∉ couplingHeaderCopies.map Prod.snd) : S₁.R k = S.R k := by
    apply unaryCopiesR_off
    intro r hr he
    exact hk (List.mem_map.mpr ⟨r,hr,he⟩)
  have h119 : (S.R 119).length = q := by
    simpa [value,couplingHeaderValue] using hsrc (119,112) (by simp [couplingHeaderCopies])
  obtain ⟨v₂,hu₂,he₂⟩ := couplingHeaderWidth_exec (body := body) q v₁ S₁
    (by rw [hoff 119 (by decide)]; exact h119)
    (by rw [hoff 94 (by decide)]; exact h94)
    (by rw [hoff 135 (by decide)]; exact h135)
  exact ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast (by
    simp [copyUnaryHeadersCost,couplingHeaderCopies,value,couplingHeaderValue,installCouplingHeadersCost]
    omega) rfl⟩

theorem couplingHeadersR_update_output {A : ℕ} (P q s t u band a b : ℕ) (R : Regs 144 A)
    (output : List (Fin (A+4))) :
    couplingHeadersR P q s t u band a b (Function.update R 143 output) =
      Function.update (couplingHeadersR P q s t u band a b R) 143 output := by
  funext k
  by_cases hk : k = 143
  · subst k
    simp [couplingHeadersR,unaryCopiesR,couplingHeaderCopies,couplingHeaderValue]
  · simp [couplingHeadersR,unaryCopiesR,couplingHeaderCopies,couplingHeaderValue,
      Function.update_apply,hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
