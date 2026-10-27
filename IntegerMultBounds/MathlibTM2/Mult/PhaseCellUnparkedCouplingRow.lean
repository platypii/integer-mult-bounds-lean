module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedReadyRow
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Rename arithmetic scratch away from ordinary geometry, avoiding header parking. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

def couplingArithmeticReg (i : Fin 117) : Fin 117 :=
  if i = 97 then 115 else if i = 115 then 97 else
  if i = 98 then 116 else if i = 116 then 98 else
  if i = 99 then 108 else if i = 108 then 99 else i

theorem couplingArithmeticReg_involutive : Function.Involutive couplingArithmeticReg := by
  intro i
  by_cases h97 : i = 97
  · subst i; decide
  by_cases h115 : i = 115
  · subst i; decide
  by_cases h98 : i = 98
  · subst i; decide
  by_cases h116 : i = 116
  · subst i; decide
  by_cases h99 : i = 99
  · subst i; decide
  by_cases h108 : i = 108
  · subst i; decide
  simp [couplingArithmeticReg,h97,h115,h98,h116,h99,h108]

theorem couplingArithmeticReg_injective : Function.Injective couplingArithmeticReg :=
  couplingArithmeticReg_involutive.injective

theorem couplingArithmeticReg_low (i : Fin 117) (hi : i.val < 96) : couplingArithmeticReg i = i := by
  have hn : i ≠ 97 ∧ i ≠ 115 ∧ i ≠ 98 ∧ i ≠ 116 ∧ i ≠ 99 ∧ i ≠ 108 := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> intro he <;> have hv := congrArg Fin.val he <;> simp at hv <;> omega
  simp [couplingArithmeticReg,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,hn.2.2.2.2.2]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def unparkedCouplingRow (hQ : SS.states ≤ Q) : Pr P 117 Q A U :=
  embProg couplingArithmeticReg Empty.elim (generatedReadyRow (P₀ := Empty) hQ)

theorem unparkedCouplingRow_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {L q w : ℕ} (hw5 : 5 ≤ w) (hqw : q+4 ≤ w) (xs as : List GaussianInt) (rhs : GaussianInt)
    (hxlen : xs.length = L) (halen : as.length = L)
    (hxs : ∀ x ∈ xs, Fits w x) (has : ∀ a ∈ as, Fits w a ∧ a.im = 0)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A+4)))
    (hL : (S.R 102).length = L) (hwR : (S.R 94).length = w) (hq : (S.R 112).length = q)
    (hx : S.R 110 = cstream A w xs++tailX) (ha : S.R 111 = cstream A w as++tailA)
    (hrhs : S.R 93 = csyms A w rhs++tailR) (hc : CClean mul S)
    (hblank : ∀ r : CR, S.R (cr r) = [])
    (hleft : S.L 100 = [])
    (hwork : ∀ k ∈ integerRowWork, k ∉ [(97 : Fin 117),98,99] → S.R k = [])
    (h109 : S.R 109 = []) (h108 : S.R 108 = []) (h115 : S.R 115 = []) (h116 : S.R 116 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generatedReadyRowCost L q w (S.R 100).length ∧
      Exec body (unparkedCouplingRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          113 (csyms A w (rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum)++S.R 113))
          110 tailX) 111 tailA) 102 [])}) := by
  let T := embStk couplingArithmeticReg S
  have hcr (r : CR) : couplingArithmeticReg (cr r) = cr r :=
    couplingArithmeticReg_low _ (by have hr := cr_range r; omega)
  obtain ⟨v₁,m,hu₁,hm,he₁⟩ := generatedReadyRow_exec (body := fun p : Empty => nomatch p)
    hQ hA hw5 hqw xs as rhs hxlen halen hxs has (embDn couplingArithmeticReg v) T tailX tailA tailR
    (by simpa [T,embStk,couplingArithmeticReg] using hL)
    (by simpa [T,embStk,couplingArithmeticReg] using hwR)
    (by simpa [T,embStk,couplingArithmeticReg] using hq)
    (by simpa [T,embStk,couplingArithmeticReg] using hx)
    (by simpa [T,embStk,couplingArithmeticReg] using ha)
    (by simpa [T,embStk,couplingArithmeticReg] using hrhs)
    (by intro i
        have hi : couplingArithmeticReg (mul i) = mul i := couplingArithmeticReg_low _ (by simp [mul]; omega)
        simpa [T,embStk,hi] using hc i)
    (by intro r; simpa [T,embStk,hcr r] using hblank r)
    (by simpa [T,embStk,couplingArithmeticReg] using hleft)
    (by intro k hk
        simp only [integerRowWork,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · simpa [T,embStk,hcr] using hblank .xs
        · simpa [T,embStk,hcr] using hblank .ys
        · simpa [T,embStk,hcr] using hblank .xsv
        · simpa [T,embStk,hcr] using hblank .ysv
        · simpa [T,embStk,hcr] using hblank .acc
        · simpa [T,embStk,hcr] using hblank .out
        · simpa [T,embStk,couplingArithmeticReg] using hwork 96 (by simp [integerRowWork]) (by decide)
        · simpa [T,embStk,couplingArithmeticReg] using h115
        · simpa [T,embStk,couplingArithmeticReg] using h116
        · simpa [T,embStk,couplingArithmeticReg] using h108
        · simpa [T,embStk,couplingArithmeticReg] using hwork 104 (by simp [integerRowWork]) (by decide)
        · simpa [T,embStk,couplingArithmeticReg] using hwork 105 (by simp [integerRowWork]) (by decide)
        · simpa [T,embStk,couplingArithmeticReg] using hwork 106 (by simp [integerRowWork]) (by decide))
    (by simpa [T,embStk,couplingArithmeticReg] using h109)
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    couplingArithmeticReg_injective (fun p => nomatch p) he₁ v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hu₁,by simpa [T,embStk,couplingArithmeticReg] using hm,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let output := csyms A w (rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum)++S.R 113
  let T₁ : Stacks 117 A := {T with R := Function.update T.R 113 output}
  let T₂ : Stacks 117 A := {T₁ with R := Function.update T₁.R 110 tailX}
  let T₃ : Stacks 117 A := {T₂ with R := Function.update T₂.R 111 tailA}
  change embOvr couplingArithmeticReg ({T₃ with R := Function.update T₃.R 102 []} : Stacks 117 A).get S = _
  rw [embOvr_updR couplingArithmeticReg_injective T₃ S 102,
    embOvr_updR couplingArithmeticReg_injective T₂ S 111,
    embOvr_updR couplingArithmeticReg_injective T₁ S 110,
    embOvr_updR couplingArithmeticReg_injective T S 113,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
