module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingHeaderWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLengthKeyReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderCopies

/-! Reconstruct coupling runtime headers after the private interior bank is released. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def couplingHeaderCopies : List (Fin 144 × Fin 144) :=
  [(117,114),(119,112),(121,97),(122,98),(123,99),(124,100),(141,101),(142,103)]

def couplingHeaderValue (P q s t u band a b : ℕ) (k : Fin 144) : ℕ :=
  if k = 117 then P else if k = 119 then q else if k = 121 then s else if k = 122 then t else
  if k = 123 then u else if k = 124 then band else if k = 141 then a else if k = 142 then b else 0

def couplingHeadersR {A : ℕ} (P q s t u band a b : ℕ) (R : Regs 144 A) : Regs 144 A :=
  Function.update (unaryCopiesR (couplingHeaderValue P q s t u band a b) R couplingHeaderCopies)
    94 (List.replicate (2*q+8) tick)

theorem couplingHeadersR_off {A : ℕ} (P q s t u band a b : ℕ) (R : Regs 144 A) (k : Fin 144)
    (hk : k ∉ [(114 : Fin 144),112,97,98,99,100,101,103,94]) :
    couplingHeadersR P q s t u band a b R k = R k := by
  have h94 : k ≠ 94 := by intro he; subst k; simp at hk
  unfold couplingHeadersR
  rw [Function.update_of_ne h94]
  apply unaryCopiesR_off
  intro r hr he
  apply hk
  simp only [couplingHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals subst k; simp

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def installCouplingHeaders : Pr P₀ 144 Q A U :=
  .seq (copyUnaryHeaders 135 couplingHeaderCopies) couplingHeaderWidth

def installCouplingHeadersCost (P q s t u band a b : ℕ) : ℕ :=
  4*P+12*q+4*(s+t+u+band+a+b)+42

/-- Header installation needs only the native scratch and source lengths;
coefficient-page spectators may already be live. -/
theorem installCouplingHeaders_native_exec (P q s t u band a b : ℕ)
    (input : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hsrc : ∀ r ∈ couplingHeaderCopies,
      (S.R r.1).length = couplingHeaderValue P q s t u band a b r.1)
    (hleft : ∀ k : Fin 144, k.val < 117 → S.L k = [])
    (hblank : ∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = [])
    (hsource : S.R 110 = input) (h135 : S.R 135 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body installCouplingHeaders (mk v S) (installCouplingHeadersCost P q s t u band a b)
        (mk v' {S with R := couplingHeadersR P q s t u band a b S.R}) ∧
      CouplingReady P q (2*q+8) s t u band a b input
        (embStk groupReg {S with R := couplingHeadersR P q s t u band a b S.R}) := by
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
    simpa [couplingHeaderValue] using hsrc (119,112) (by simp [couplingHeaderCopies])
  obtain ⟨v₂,hu₂,he₂⟩ := couplingHeaderWidth_exec (body := body) q v₁ S₁
    (by rw [hoff 119 (by decide)]; exact h119)
    (by rw [hoff 94 (by decide)]; exact hblank 94 (by decide) (by decide) (by decide))
    (by rw [hoff 135 (by decide)]; exact h135)
  have hat (r : Fin 144 × Fin 144) (hr : r ∈ couplingHeaderCopies) :
      S₁.R r.2 = List.replicate (value r.1) tick := by
    have hf : r.2.val < 117 ∧ r.2 ≠ 93 ∧ r.2 ≠ 110 := by
      simp only [couplingHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    change unaryCopiesR value S.R couplingHeaderCopies r.2 = _
    rw [unaryCopiesR_at value S.R couplingHeaderCopies (by decide) r hr,
      hblank r.2 hf.1 hf.2.1 hf.2.2,List.append_nil]
  let S₂ : Stacks 144 A := {S with R := couplingHeadersR P q s t u band a b S.R}
  have hoff₂ (k : Fin 144) (hk : k ∉ [(114 : Fin 144),112,97,98,99,100,101,103,94]) : S₂.R k = S.R k := by
    exact couplingHeadersR_off P q s t u band a b S.R k hk
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast ?_ rfl,?_⟩
  · simp [copyUnaryHeadersCost,couplingHeaderCopies,value,couplingHeaderValue,installCouplingHeadersCost]
    omega
  · constructor
    · simpa [embStk,groupReg,S₂,couplingHeadersR,S₁,value,couplingHeaderValue] using congrArg List.length (hat (117,114) (by decide))
    · simpa [embStk,groupReg,S₂,couplingHeadersR,S₁,value,couplingHeaderValue] using congrArg List.length (hat (119,112) (by decide))
    · simpa [embStk,groupReg,S₂,couplingHeadersR,S₁,value,couplingHeaderValue] using congrArg List.length (hat (123,99) (by decide))
    · simpa [embStk,groupReg,S₂,couplingHeadersR,S₁,value,couplingHeaderValue] using congrArg List.length (hat (121,97) (by decide))
    · simpa [embStk,groupReg,S₂,couplingHeadersR,S₁,value,couplingHeaderValue] using congrArg List.length (hat (122,98) (by decide))
    · simpa [embStk,groupReg,S₂,couplingHeadersR,S₁,value,couplingHeaderValue] using congrArg List.length (hat (124,100) (by decide))
    · simpa [embStk,groupReg,S₂,couplingHeadersR,S₁,value,couplingHeaderValue] using congrArg List.length (hat (141,101) (by decide))
    · simpa [embStk,groupReg,S₂,couplingHeadersR,S₁,value,couplingHeaderValue] using congrArg List.length (hat (142,103) (by decide))
    · simp [embStk,groupReg,couplingHeadersR]
    · change S₂.R 110 = input
      rw [hoff₂ 110 (by decide)]
      exact hsource
    · intro k hk
      have hn : groupReg k ∉ [(114 : Fin 144),112,97,98,99,100,101,103,94] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      change S₂.R (groupReg k) = []
      rw [hoff₂ (groupReg k) hn]
      have hh : (groupReg k).val < 117 ∧ groupReg k ≠ 93 ∧ groupReg k ≠ 110 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact hblank _ hh.1 hh.2.1 hh.2.2
    · intro i
      have hi := i.isLt
      have hn : groupReg (mul i) ∉ [(114 : Fin 144),112,97,98,99,100,101,103,94] := by
        simp [groupReg,mul,Fin.ext_iff]
        omega
      constructor
      · exact hleft _ (by change i.val < 117; omega)
      · change S₂.R (groupReg (mul i)) = []
        rw [hoff₂ _ hn]
        exact hblank _ (by change i.val < 117; omega)
          (by simp [groupReg,mul,Fin.ext_iff]; omega) (by simp [groupReg,mul,Fin.ext_iff]; omega)
    · intro r
      have hr := cr_range r
      have hn : groupReg (cr r) ∉ [(114 : Fin 144),112,97,98,99,100,101,103,94] := by
        simp [groupReg,Fin.ext_iff]
        omega
      change S₂.R (groupReg (cr r)) = []
      rw [hoff₂ _ hn]
      exact hblank _ (cr r).isLt (by simpa [groupReg,Fin.ext_iff] using hr.2.2.1)
        (by simp [groupReg,Fin.ext_iff]; omega)
    · intro k _
      exact hleft _ k.isLt


theorem installCouplingHeaders_exec (P N q l s t u band a b : ℕ)
    (input : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (h : LengthKeyReady P N q l s t u band 0 0 input S)
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b) :
    ∃ v', v'.user = v.user ∧
      Exec body installCouplingHeaders (mk v S) (installCouplingHeadersCost P q s t u band a b)
        (mk v' {S with R := couplingHeadersR P q s t u band a b S.R}) ∧
      CouplingReady P q (2*q+8) s t u band a b input
        (embStk groupReg {S with R := couplingHeadersR P q s t u band a b S.R}) := by
  let value := couplingHeaderValue P q s t u band a b
  have hsrc : ∀ r ∈ couplingHeaderCopies, (S.R r.1).length = value r.1 := by
    intro r hr
    simp only [couplingHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [value,couplingHeaderValue,groupHeaderValue] using h.masters (117,114) (by simp [groupHeaderCopies])
    · simpa [value,couplingHeaderValue,groupHeaderValue] using h.masters (119,112) (by simp [groupHeaderCopies])
    · simpa [value,couplingHeaderValue,groupHeaderValue] using h.masters (121,97) (by simp [groupHeaderCopies])
    · simpa [value,couplingHeaderValue,groupHeaderValue] using h.masters (122,98) (by simp [groupHeaderCopies])
    · simpa [value,couplingHeaderValue,groupHeaderValue] using h.masters (123,99) (by simp [groupHeaderCopies])
    · simpa [value,couplingHeaderValue,groupHeaderValue] using h.masters (124,100) (by simp [groupHeaderCopies])
    · simpa [value,couplingHeaderValue] using ha
    · simpa [value,couplingHeaderValue] using hb
  exact installCouplingHeaders_native_exec P q s t u band a b input v S hsrc
    h.left h.blank h.source (h.fresh 135 (by simp))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
