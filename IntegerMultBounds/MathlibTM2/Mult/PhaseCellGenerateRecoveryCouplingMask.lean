module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedRecoveryGuardMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryGuardSemantics
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Generate interior/exterior zero-row guards from ordinary headers, restoring its temporary width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem recoveryCouplingMask_at_spec {s t A : ℕ} [NeZero s] (hA : 4 ≤ A)
    (hst : s < t) (boundary : Bool) (band a b i : ℕ) (hb : b ≤ s) (hi : i < s) :
    pairRe ((recoveryGuardMaskSymbols boundary A s t (2*band) a b)[i]'(by simp [hi])) = true ↔
      (i : ZMod s) ∈ couplingZeroRows boundary s t band a b := by
  rw [recoveryGuardMaskSymbols_getElem boundary A s t (2*band) a b i hi,pairRe_pairSym hA]
  exact recoveryGuardMaskAt_spec hst boundary band a b i hb hi

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateRecoveryCouplingMask (boundary : Bool) : Pr P₀ 117 Q A U :=
  .seq (umul 2 100 96 104)
    (.seq (embProg (Equiv.swap 96 100) Empty.elim (closedRecoveryGuardMask (P₀ := Empty) boundary)) (uclear 96))

def generateRecoveryCouplingMaskCost (s t band a b : ℕ) : ℕ :=
  closedRecoveryGuardMaskCost s t (2*band) a b+8*band+6

theorem generateRecoveryCouplingMask_exec {s t band a b : ℕ} [NeZero s]
    (boundary : Bool)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t) (hband : (S.R 100).length = band)
    (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (h96 : S.R 96 = []) (h104 : S.R 104 = [])
    (h115 : S.R 115 = []) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generateRecoveryCouplingMaskCost s t band a b ∧
      Exec body (generateRecoveryCouplingMask boundary) (mk v S) m
        (mk v' {S with R := (Function.update S.R 109
          (recoveryGuardMaskSymbols boundary A s t (2*band) a b++S.R 109))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := umul_exec (body := body) 2 (a := 100) (b := 96) (t := 104)
    (by decide) (by decide) (by decide) v S h104
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 96 (List.replicate (2*band) tick)}
  have he₁' : Exec body (umul 2 100 96 104) (mk v S) (4*band+4) (mk v₁ S₁) := by
    simpa [S₁,hband,h96] using he₁
  let e : Fin 117 → Fin 117 := Equiv.swap 96 100
  have he : Function.Injective e := (Equiv.swap 96 100).injective
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := closedRecoveryGuardMask_exec
    (body := fun p : Empty => nomatch p) (band := 2*band) boundary hst haS hbS hA (embDn e v₁) (embStk e S₁)
    (by simpa [e,embStk,S₁,Equiv.swap_apply_def] using hs)
    (by simpa [e,embStk,S₁,Equiv.swap_apply_def] using ht)
    (by simp [e,embStk,S₁,Equiv.swap_apply_def])
    (by simpa [e,embStk,S₁,Equiv.swap_apply_def] using ha)
    (by simpa [e,embStk,S₁,Equiv.swap_apply_def] using hb)
    (by simpa [e,embStk,S₁,Equiv.swap_apply_def] using h115)
    (by simpa [e,embStk,S₁,Equiv.swap_apply_def] using h106)
    (by simpa [e,embStk,S₁,Equiv.swap_apply_def] using h108) (by
      intro r hr
      have h96r : r ≠ 96 := by intro h; subst r; norm_num at hr
      have h100r : r ≠ 100 := by intro h; subst r; norm_num at hr
      simpa [e,embStk,S₁,Equiv.swap_apply_def,h96r,h100r] using hblank r hr)
  obtain ⟨v₃,hv₃,hu₃,he₃⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    he (fun p => nomatch p) he₂ v₁ rfl S₁ rfl
  let S₂ : Stacks 117 A := {S₁ with R := (Function.update S₁.R 109
    (recoveryGuardMaskSymbols boundary A s t (2*band) a b++S₁.R 109))}
  have he₃' : Exec body (embProg e Empty.elim (closedRecoveryGuardMask (P₀ := Empty) boundary))
      (mk v₁ S₁) m₂ (mk v₃ S₂) := by
    convert he₃ using 1
    apply congrArg (mk v₃)
    rw [embOvr_updR he,embOvr_stk]
    simp [S₂,e,embStk,Equiv.swap_apply_def]
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) 96 v₃ S₂
  refine ⟨v₄,(4*band+4)+(m₂+(4*band+2)),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    by dsimp [generateRecoveryCouplingMaskCost]; omega,
    (Exec.seq he₁' (Exec.seq he₃' he₄)).cast ?_ ?_⟩
  · simp [S₂,S₁]; omega
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h96' : k = 96 <;> by_cases h109 : k = 109 <;> simp_all [S₂,S₁]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
