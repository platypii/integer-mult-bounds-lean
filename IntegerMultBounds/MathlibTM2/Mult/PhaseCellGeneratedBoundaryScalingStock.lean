module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryPhysicalScalingStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryUnscale

/-! Generate, use and retire both boundary scaling headers within one linear setup allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.BandFactor
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

theorem boundaryNormalizeHeader_native : mnNativePushBound 3
    (boundaryNormalizationHeader (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [boundaryNormalizationHeader,udiv,divChain,dropTop,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem boundaryUnscaleHeader_native : mnNativePushBound 3
    (boundaryUnscaleHeader (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [boundaryUnscaleHeader,udiv,divChain,umul,umulSym,scanR,drainR,popDo,keepIn,pushN,
    moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem generatedBoundaryNormalize_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (q : ℕ) (hq : 2 ≤ q) (heven : q%2 = 0) (xs : List GaussianInt)
    (hbound : ∀ z ∈ xs, |gv q z.re| ≤ (2 : ℝ)^(q/2) ∧ |gv q z.im| ≤ (2 : ℝ)^(q/2))
    (C : ℕ) (hpush : mnProgPush (cmulBlock (rsbCr boundaryFactorReg .vk .dtab .ya)
      (rmulOne (P := P) (Q := Q) (A := A) (U := U) boundaryFactorMulReg
        boundaryFactorMulReg_injective (by decide) hQ (rsbCr boundaryFactorReg .vk .dtab .ya))) ≤ C)
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hleft : ∀ i, S.L i = []) (hmul : ∀ i : Fin 64, S.R (boundaryFactorMulReg i) = [])
    (hready : RsbReady (boundaryFactorState S) (2*q+8) q) (hmaster : (S.R 119).length = q)
    (h184 : S.R 184 = []) (h220 : S.R 220 = []) (h221 : S.R 221 = []) (h223 : S.R 223 = [])
    (hya : S.R 208 = []) (hac2 : S.R 215 = []) (hsrc : S.R 206 = cstream A (2*q+8) xs) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generatedBoundaryNormalizeCost q xs.length ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (realScalarWorkspace C (2*q+8) xs.length+1000*(q+1))) depth
        (generatedBoundaryNormalize hQ) (mk v S) n
        (mk v' {S with R := (Function.update S.R 206
          (cstream A (2*q+8) (xs.map (normalizeBoundaryWord q (q/2-1)))))}) := by
  let e := q/2-1
  have hsplit : q = q/2+e+1 := by dsimp [e]; omega
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := boundaryNormalizationHeader_exec (body := body) q v S hmaster h184 h223
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 223 (List.replicate e tick)}
  have hstate : boundaryFactorState S₁ = boundaryFactorState S := boundaryFactorState_update_header S _
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := boundaryNormalizePhysical_exec_within (body := body) hQ hA q (q/2) e hsplit xs hbound C hpush
    v₁ S₁ hleft (by
      intro i
      have hi223 : boundaryFactorMulReg i ≠ 223 := by
        intro hi
        have hv := congrArg (fun k : Fin 224 => k.val) hi
        have hi' := i.isLt
        change i.val = 223 at hv
        omega
      simpa only [S₁,Function.update_of_ne hi223] using hmul i)
    (by rw [hstate]; exact hready) (by simp [S₁])
    (by simpa [S₁] using hsrc) (by simpa [S₁] using h184) (by simpa [S₁] using h220)
    (by simpa [S₁] using h221) (by simpa [S₁] using hya) (by simpa [S₁] using hac2)
  let output := cstream A (2*q+8) (xs.map (normalizeBoundaryWord q e))
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 206 output}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 223 v₂ S₂
  have hlen : (S₂.R 223).length = e := by simp [S₂,S₁]
  have he₃' : Exec body (uclear 223) (mk v₂ S₂) (2*e+2)
      (mk v₃ {S₂ with R := Function.update S₂.R 223 []}) := he₃.cast (by rw [hlen]) rfl
  refine ⟨v₃,n₁+(n₂+(2*e+2)),hu₃.trans (hu₂.trans hu₁),?_,
    ?_⟩
  · exact Nat.add_le_add hn₁ (Nat.add_le_add_right hn₂ _)
  · intro depth
    have ht₁ := mn_native_exec_within he₁ 3 boundaryNormalizeHeader_native depth
      (mnSize (mk v S)+depth+3*(4*q+5)) (by omega)
    have ht₃ := mn_native_exec_within he₃' 0 (by
      simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth _ (Nat.le_refl _)
    have ht := mn_seq_within_add ht₁ (mn_seq_within_add (he₂ depth) ht₃)
    refine (ht.mono (by intro d z hz; dsimp only [e] at hz; omega)).cast rfl ?_
    apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi223 : i = 223 <;> by_cases hi206 : i = 206 <;>
      simp [S₂,S₁,output,e,hi223,hi206,h223]

theorem generatedBoundaryUnscale_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (q p : ℕ) (hpq : p ≤ q/2) (xs : List GaussianInt)
    (hbound : ∀ z ∈ xs, |gv q z.re| ≤ 8*p+1 ∧ |gv q z.im| ≤ 8*p+1)
    (C : ℕ) (hpush : mnProgPush (cmulBlock (rsbCr boundaryFactorReg .dout .dtab .ya)
      (rmulOne (P := P) (Q := Q) (A := A) (U := U) boundaryFactorMulReg
        boundaryFactorMulReg_injective (by decide) hQ (rsbCr boundaryFactorReg .dout .dtab .ya))) ≤ C)
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hleft : ∀ i, S.L i = []) (hmul : ∀ i : Fin 64, S.R (boundaryFactorMulReg i) = [])
    (hready : RsbReady (boundaryFactorState S) (2*q+8) q) (hmaster : (S.R 119).length = q)
    (h184 : S.R 184 = []) (h220 : S.R 220 = []) (h221 : S.R 221 = []) (h223 : S.R 223 = [])
    (hya : S.R 208 = []) (hac2 : S.R 215 = []) (hsrc : S.R 217 = cstream A (2*q+8) xs) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generatedBoundaryUnscaleCost q xs.length ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (realScalarWorkspace C (2*q+8) xs.length+1000*(q+1))) depth
        (generatedBoundaryUnscale hQ) (mk v S) n
        (mk v' {S with R := (Function.update S.R 217
          (cstream A (2*q+8) (xs.map (unscaleBoundaryWord q))))}) := by
  let e := q+q/2+1
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := boundaryUnscaleHeader_exec (body := body) q v S hmaster h184 h223
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 223 (List.replicate e tick)}
  have hstate : boundaryFactorState S₁ = boundaryFactorState S := boundaryFactorState_update_header S _
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := boundaryUnscalePhysical_exec_within (body := body) hQ hA q p hpq xs hbound C hpush
    v₁ S₁ hleft (by
      intro i
      have hi223 : boundaryFactorMulReg i ≠ 223 := by
        intro hi
        have hv := congrArg (fun k : Fin 224 => k.val) hi
        have hi' := i.isLt
        change i.val = 223 at hv
        omega
      simpa only [S₁,Function.update_of_ne hi223] using hmul i)
    (by rw [hstate]; exact hready) (by simp [S₁,e])
    (by simpa [S₁] using hsrc) (by simpa [S₁] using h184) (by simpa [S₁] using h220)
    (by simpa [S₁] using h221) (by simpa [S₁] using hya) (by simpa [S₁] using hac2)
  let output := cstream A (2*q+8) (xs.map (unscaleBoundaryWord q))
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 217 output}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 223 v₂ S₂
  have hlen : (S₂.R 223).length = e := by simp [S₂,S₁]
  have he₃' : Exec body (uclear 223) (mk v₂ S₂) (2*e+2)
      (mk v₃ {S₂ with R := Function.update S₂.R 223 []}) := he₃.cast (by rw [hlen]) rfl
  refine ⟨v₃,n₁+(n₂+(2*e+2)),hu₃.trans (hu₂.trans hu₁),?_,
    ?_⟩
  · exact Nat.add_le_add hn₁ (Nat.add_le_add_right hn₂ _)
  · intro depth
    have ht₁ := mn_native_exec_within he₁ 3 boundaryUnscaleHeader_native depth
      (mnSize (mk v S)+depth+3*(8*q+9)) (by omega)
    have ht₃ := mn_native_exec_within he₃' 0 (by
      simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth _ (Nat.le_refl _)
    have ht := mn_seq_within_add ht₁ (mn_seq_within_add (he₂ depth) ht₃)
    refine (ht.mono (by intro d z hz; dsimp only [e] at hz; omega)).cast rfl ?_
    apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi223 : i = 223 <;> by_cases hi217 : i = 217 <;>
      simp [S₂,S₁,output,e,hi223,hi217,h223]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
