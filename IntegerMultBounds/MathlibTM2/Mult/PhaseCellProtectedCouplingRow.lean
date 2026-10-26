module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedReadyRow

/-! Preserve ordinary geometry while generating readiness, borrowing an RHS,
executing a row, consuming its operands and releasing arithmetic workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def protectedCouplingRow (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  withSavedHeader 97 (withSavedHeader 98 (withSavedHeader 99 (generatedReadyRow hQ)))

theorem protectedCouplingRow_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {L q w : ℕ} (hw5 : 5 ≤ w) (hqw : q+4 ≤ w) (xs as : List GaussianInt) (rhs : GaussianInt)
    (hxlen : xs.length = L) (halen : as.length = L)
    (hxs : ∀ x ∈ xs, Fits w x) (has : ∀ a ∈ as, Fits w a ∧ a.im = 0)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A+4)))
    (hL : (S.R 102).length = L) (hwR : (S.R 94).length = w) (hq : (S.R 112).length = q)
    (hx : S.R 110 = cstream A w xs++tailX) (ha : S.R 111 = cstream A w as++tailA)
    (hrhs : S.R 93 = csyms A w rhs++tailR) (hc : CClean mul S)
    (hblank : ∀ r : CR, S.R (cr r) = [])
    (hleft : ∀ k ∈ [(97 : Fin 117),98,99,100], S.L k = [])
    (hwork : ∀ k ∈ integerRowWork, k ∉ [(97 : Fin 117),98,99] → S.R k = [])
    (h109 : S.R 109 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ generatedReadyRowCost L q w (S.R 100).length+
        4*((S.R 97).length+(S.R 98).length+(S.R 99).length)+12 ∧
      Exec body (protectedCouplingRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          113 (csyms A w (rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum)++S.R 113))
          110 tailX) 111 tailA) 102 [])}) := by
  let F : Stacks 117 A → Stacks 117 A := fun B => {B with R :=
    (Function.update (Function.update (Function.update (Function.update B.R
      113 (csyms A w (rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum)++B.R 113))
      110 tailX) 111 tailA) 102 [])}
  let B₁ := parkedHeader S 97
  let B₂ := parkedHeader B₁ 98
  let B₃ := parkedHeader B₂ 99
  let M := generatedReadyRowCost L q w (S.R 100).length
  have hF (B : Stacks 117 A) (r : Fin 117) (hr : r ∈ [(97 : Fin 117),98,99]) :
      F (parkedHeader B r) = parkedHeader (F B) r := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    all_goals
      refine Stacks.ext rfl rfl ?_ ?_
      · funext k; simp [F,parkedHeader]
      · funext k
        by_cases h : k = 97 <;> by_cases h' : k = 98 <;> by_cases h'' : k = 99 <;>
          simp [F,parkedHeader,h,h',h'',Function.update_apply]
  have hcore (v₃ : HS 117 Q A U) :
      ∃ v' m, v'.user = v₃.user ∧ m ≤ M ∧
        Exec body (generatedReadyRow hQ) (mk v₃ B₃) m (mk v' (parkedHeader (parkedHeader (parkedHeader (F S) 97) 98) 99)) := by
    have hcr (r : CR) : cr r ≠ (97 : Fin 117) ∧ cr r ≠ 98 ∧ cr r ≠ 99 := by
      have hr := (cr_range r).2.1
      constructor
      · intro he; have hv := congrArg Fin.val he; omega
      constructor <;> intro he <;> have hv := congrArg Fin.val he <;> omega
    obtain ⟨v',m,hu,hm,he⟩ := generatedReadyRow_exec (body := body) hQ hA hw5 hqw xs as rhs
      hxlen halen hxs has v₃ B₃ tailX tailA tailR
      (by simpa [B₃,B₂,B₁,parkedHeader] using hL)
      (by simpa [B₃,B₂,B₁,parkedHeader] using hwR)
      (by simpa [B₃,B₂,B₁,parkedHeader] using hq)
      (by simpa [B₃,B₂,B₁,parkedHeader] using hx)
      (by simpa [B₃,B₂,B₁,parkedHeader] using ha)
      (by simpa [B₃,B₂,B₁,parkedHeader] using hrhs)
      (by intro i
          have hn : mul i ≠ (97 : Fin 117) ∧ mul i ≠ 98 ∧ mul i ≠ 99 := by
            have hi := i.isLt
            simp only [mul,ne_eq,Fin.ext_iff]
            omega
          simpa [B₃,B₂,B₁,parkedHeader,hn.1,hn.2.1,hn.2.2] using hc i)
      (by intro r; simpa [B₃,B₂,B₁,parkedHeader,(hcr r).1,(hcr r).2.1,(hcr r).2.2] using hblank r)
      (by simpa [B₃,B₂,B₁,parkedHeader] using hleft 100 (by simp))
      (by intro k hk
          by_cases h : k ∈ [(97 : Fin 117),98,99]
          · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
            rcases h with rfl | rfl | rfl <;> simp [B₃,B₂,B₁,parkedHeader]
          · have hn : k ≠ 97 ∧ k ≠ 98 ∧ k ≠ 99 := by simpa using h
            simpa [B₃,B₂,B₁,parkedHeader,hn.1,hn.2.1,hn.2.2] using hwork k hk h)
      (by simpa [B₃,B₂,B₁,parkedHeader] using h109)
    refine ⟨v',m,hu,by simpa [M,B₃,B₂,B₁,parkedHeader] using hm,he.cast rfl ?_⟩
    apply congrArg (mk v')
    change F B₃ = _
    dsimp only [B₃]
    rw [hF B₂ 99 (by simp)]
    dsimp only [B₂]
    rw [hF B₁ 98 (by simp)]
    dsimp only [B₁]
    rw [hF S 97 (by simp)]
  have h98call (v₂ : HS 117 Q A U) :
      ∃ v' m, v'.user = v₂.user ∧ m ≤ M+4*(S.R 99).length+4 ∧
        Exec body (withSavedHeader 99 (generatedReadyRow hQ)) (mk v₂ B₂) m
          (mk v' (parkedHeader (parkedHeader (F S) 97) 98)) := by
    simpa [B₂,B₁,parkedHeader,F] using
      (withSavedHeader_exec (body := body) 99 (generatedReadyRow hQ) v₂ B₂
        (parkedHeader (parkedHeader (F S) 97) 98) M
        (by simpa [B₂,B₁,parkedHeader] using hleft 99 (by simp))
        (by simpa [F,parkedHeader] using hleft 99 (by simp)) (by simp [F,B₂,B₁,parkedHeader])
        (fun v₃ _ => hcore v₃))
  have h97call (v₁ : HS 117 Q A U) :
      ∃ v' m, v'.user = v₁.user ∧ m ≤ M+4*(S.R 99).length+4+4*(S.R 98).length+4 ∧
        Exec body (withSavedHeader 98 (withSavedHeader 99 (generatedReadyRow hQ)))
          (mk v₁ B₁) m (mk v' (parkedHeader (F S) 97)) := by
    simpa [B₁,parkedHeader] using
      (withSavedHeader_exec (body := body) 98 (withSavedHeader 99 (generatedReadyRow hQ)) v₁ B₁
        (parkedHeader (F S) 97) (M+4*(S.R 99).length+4)
        (by simpa [B₁,parkedHeader] using hleft 98 (by simp))
        (by simpa [F,parkedHeader] using hleft 98 (by simp)) (by simp [F,B₁,parkedHeader])
        (fun v₂ _ => h98call v₂))
  obtain ⟨v',m,hu,hm,he⟩ := withSavedHeader_exec (body := body) 97
    (withSavedHeader 98 (withSavedHeader 99 (generatedReadyRow hQ))) v S (F S)
    (M+4*(S.R 99).length+4+4*(S.R 98).length+4)
    (hleft 97 (by simp)) (by simpa [F] using hleft 97 (by simp)) (by simp [F])
    (fun v₁ _ => h97call v₁)
  exact ⟨v',m,hu,by dsimp only [M] at hm; omega,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
