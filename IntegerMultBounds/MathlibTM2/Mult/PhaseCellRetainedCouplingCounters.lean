module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingReady

/-! Generate scalar counters once from the ordinary coupling headers and
release their owned tapes after the retained row loop. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem RetainedCouplingReady.of_generated {A P q w s t u band a b : ℕ}
    {raw : List (Fin (A+4))} {S : Stacks 117 A}
    (h : CouplingReady P q w s t u band a b raw S) :
    RetainedCouplingReady P q w s t u band a b raw {S with R := counterR q w S.R} := by
  constructor
  · simpa [counterR,cr,OutputPlacement.code] using h.precision
  · simpa [counterR,cr,OutputPlacement.code] using h.fraction
  · simpa [counterR,cr,OutputPlacement.code] using h.parameter
  · simpa [counterR,cr,OutputPlacement.code] using h.axis
  · simpa [counterR,cr,OutputPlacement.code] using h.period
  · simpa [counterR,cr,OutputPlacement.code] using h.bandwidth
  · simpa [counterR,cr,OutputPlacement.code] using h.lower
  · simpa [counterR,cr,OutputPlacement.code] using h.upper
  · simpa [counterR,cr,OutputPlacement.code] using h.width
  · simpa [counterR,cr,OutputPlacement.code] using h.source
  · intro k hk
    have hn : k ≠ cr .wn ∧ k ≠ cr .pn ∧ k ≠ cr .nn := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [counterR,Function.update_of_ne hn.1,Function.update_of_ne hn.2.1,
      Function.update_of_ne hn.2.2] using h.fresh k (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
        rcases hk with h | h | h | h | h | h | h | h | h <;> simp_all)
  · intro i
    have hne (r : CR) : mul i ≠ cr r := (cr_mul r i).symm
    exact ⟨(h.clean i).1,by simpa [counterR,hne] using (h.clean i).2⟩
  · intro r hr
    have hn : r ≠ .wn ∧ r ≠ .pn ∧ r ≠ .nn := by simpa using hr
    simpa [counterR,cr_injective.ne hn.1,cr_injective.ne hn.2.1,cr_injective.ne hn.2.2] using h.arithmetic r
  · exact counterR_ready q w S.R h.arithmetic
  · exact h.left

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem retainedCouplingCounters_exec (q w : ℕ) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    {P s t u band a b : ℕ} (raw : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hready : CouplingReady P q w s t u band a b raw S) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareCost q w+6*q+4*band+10 ∧
      Exec body couplingReadiness (mk v S) n (mk v' {S with R := counterR q w S.R}) ∧
      RetainedCouplingReady P q w s t u band a b raw {S with R := counterR q w S.R} := by
  obtain ⟨v',n,hu,hn,he⟩ := couplingReadiness_exec (body := body) q w hw5 hqw v S
    hready.fraction hready.width (hready.left 100 (by simp)) (hready.fresh 109 (by simp)) (by
      intro k hk
      let i : Fin 64 := ⟨k.val,by omega⟩
      have hi : mul i = k := Fin.ext rfl
      simpa only [hi] using (hready.clean i).2) (fun r _ => hready.arithmetic r)
  exact ⟨v',n,hu,by simpa only [hready.bandwidth] using hn,he,RetainedCouplingReady.of_generated hready⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
