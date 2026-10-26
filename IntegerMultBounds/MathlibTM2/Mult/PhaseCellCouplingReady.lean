module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawCouplingRow

/-! Reusable ordinary-header and workspace invariant for coupling row iteration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

structure CouplingReady {A : ℕ} (P q w s t u band a b : ℕ)
    (raw : List (Fin (A+4))) (S : Stacks 117 A) : Prop where
  precision : (S.R 114).length = P
  fraction : (S.R 112).length = q
  parameter : (S.R 99).length = u
  axis : (S.R 97).length = s
  period : (S.R 98).length = t
  bandwidth : (S.R 100).length = band
  lower : (S.R 101).length = a
  upper : (S.R 103).length = b
  width : (S.R 94).length = w
  source : S.R 110 = raw
  fresh : ∀ k ∈ [(92 : Fin 117),96,102,104,105,106,108,109,115,116], S.R k = []
  clean : CClean mul S
  arithmetic : ∀ r : CR, S.R (cr r) = []
  left : ∀ k ∈ [(97 : Fin 117),98,99,100], S.L k = []

variable {A P q w s t u band a b : ℕ} {raw : List (Fin (A+4))} {S : Stacks 117 A}

theorem CouplingReady.of_frame (h : CouplingReady P q w s t u band a b raw S)
    {S' : Stacks 117 A} (hL : S'.L = S.L)
    (hR : ∀ k : Fin 117, k ≠ 93 → k ≠ 107 → k ≠ 113 → S'.R k = S.R k) :
    CouplingReady P q w s t u band a b raw S' := by
  constructor
  · rw [hR 114 (by decide) (by decide) (by decide)]; exact h.precision
  · rw [hR 112 (by decide) (by decide) (by decide)]; exact h.fraction
  · rw [hR 99 (by decide) (by decide) (by decide)]; exact h.parameter
  · rw [hR 97 (by decide) (by decide) (by decide)]; exact h.axis
  · rw [hR 98 (by decide) (by decide) (by decide)]; exact h.period
  · rw [hR 100 (by decide) (by decide) (by decide)]; exact h.bandwidth
  · rw [hR 101 (by decide) (by decide) (by decide)]; exact h.lower
  · rw [hR 103 (by decide) (by decide) (by decide)]; exact h.upper
  · rw [hR 94 (by decide) (by decide) (by decide)]; exact h.width
  · rw [hR 110 (by decide) (by decide) (by decide)]; exact h.source
  · intro k hk
    have hn : k ≠ 93 ∧ k ≠ 107 ∧ k ≠ 113 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hR k hn.1 hn.2.1 hn.2.2]
    exact h.fresh k hk
  · intro i
    have hn : mul i ≠ (93 : Fin 117) ∧ mul i ≠ 107 ∧ mul i ≠ 113 := by
      have hi := i.isLt
      simp only [mul,ne_eq,Fin.ext_iff]
      omega
    rw [hL,hR (mul i) hn.1 hn.2.1 hn.2.2]
    exact h.clean i
  · intro r
    have hr := cr_range r
    have hn : cr r ≠ (107 : Fin 117) ∧ cr r ≠ 113 := by
      constructor <;> intro he <;> have hv := congrArg Fin.val he <;> omega
    rw [hR (cr r) (by intro he; exact hr.2.2.1 (congrArg Fin.val he)) hn.1 hn.2]
    exact h.arithmetic r
  · intro k hk
    rw [hL]
    exact h.left k hk

theorem CouplingReady.low (h : CouplingReady P q w s t u band a b raw S)
    (k : Fin 117) (hk : k.val < 63) : S.R k = [] := by
  let i : Fin 64 := ⟨k.val,by omega⟩
  have hi : mul i = k := Fin.ext rfl
  simpa only [hi] using (h.clean i).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
