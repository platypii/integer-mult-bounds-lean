module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryScalingStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryUnscalePhysical

/-! Physical boundary scaling includes runtime scalar construction and retirement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

theorem powerWordHeader_native {width exponent dst parked saved tmp : Fin 224} :
    mnNativePushBound 2 (powerWordHeader (P := P) (Q := Q) (A := A) (U := U)
      width exponent dst parked saved tmp) := by
  simp [powerWordHeader,setPowerWord,movePrefix,transfer,transferAct,copyR,copyStep,
    dropTop,scanR,drainR,popDo,keepIn,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem boundaryNormalizePhysical_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (q E e : ℕ) (hq : q = E+e+1) (xs : List GaussianInt)
    (hbound : ∀ z ∈ xs, |gv q z.re| ≤ (2 : ℝ)^E ∧ |gv q z.im| ≤ (2 : ℝ)^E)
    (C : ℕ) (hpush : mnProgPush (cmulBlock (rsbCr boundaryFactorReg .vk .dtab .ya)
      (rmulOne (P := P) (Q := Q) (A := A) (U := U) boundaryFactorMulReg
        boundaryFactorMulReg_injective (by decide) hQ (rsbCr boundaryFactorReg .vk .dtab .ya))) ≤ C)
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hleft : ∀ i, S.L i = []) (hmul : ∀ i : Fin 64, S.R (boundaryFactorMulReg i) = [])
    (hready : RsbReady (boundaryFactorState S) (2*q+8) q)
    (he : (S.R 223).length = e) (hsrc : S.R 206 = cstream A (2*q+8) xs)
    (h184 : S.R 184 = []) (h220 : S.R 220 = []) (h221 : S.R 221 = [])
    (hya : S.R 208 = []) (hac2 : S.R 215 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ boundaryNormalizePhysicalCost q e xs.length ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(realScalarWorkspace C (2*q+8) xs.length+2*(4*(2*q+8)+4+(8*e+9))))
        depth (boundaryNormalizePhysical hQ) (mk v S) n
        (mk v' {S with R := (Function.update S.R 206
          (cstream A (2*q+8) (xs.map (normalizeBoundaryWord q e))))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := powerWordHeader_exec (body := body)
    (width := 160) (exponent := 223) (dst := 220) (parked := 221) (saved := 184) (tmp := 0)
    (by decide) (2*q+8) e (by omega) v S hready.wn he h220 h221 h184 (hmul 0)
  let scalar := csyms A (2*q+8) (⟨(2 : ℤ)^e,0⟩ : GaussianInt)
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 220 scalar}
  have hstate : boundaryFactorState S₁ = Function.update (boundaryFactorState S) .dtab scalar :=
    boundaryFactorState_update S .dtab scalar
  have hrun := boundary_normalize_runs_within (body := body) boundaryFactorReg_injective boundaryFactorReg_disjoint
    boundaryFactorMulReg_injective (by decide) hQ hA q E e hq (boundaryFactorState S₁)
    (by rw [hstate]; exact hready.update .dtab (fun _ => by simp) scalar) xs hbound
    (by rw [hstate]; exact hsrc) (by rw [hstate]; rfl)
    (by rw [hstate]; exact hya) (by rw [hstate]; exact hac2) C hpush
  obtain ⟨v₂,S₂,n₂,hu₂,hn₂,hholds,hframe,he₂⟩ := hrun v₁ S₁ ⟨hleft,by
    intro i
    have hi220 : boundaryFactorMulReg i ≠ 220 := by
      intro hi
      have hv := congrArg (fun k : Fin 224 => k.val) hi
      have hi' := i.isLt
      change i.val = 220 at hv
      omega
    simpa only [S₁,Function.update_of_ne hi220] using hmul i⟩ (fun _ => rfl)
  have hS₂ := boundaryFactorFr_update .vk _ hframe hholds
  rw [hS₂] at he₂
  let output := cstream A (2*q+8) (xs.map (normalizeBoundaryWord q e))
  let S₂' : Stacks 224 A := {S₁ with R := Function.update S₁.R 206 output}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 220 v₂ S₂'
  have hlen : (S₂'.R 220).length = 2*q+8 := by simp [S₂',S₁,scalar]
  have he₃' : Exec body (uclear 220) (mk v₂ S₂') (2*(2*q+8)+2)
      (mk v₃ {S₂' with R := Function.update S₂'.R 220 []}) := he₃.cast (by rw [hlen]) rfl
  refine ⟨v₃,(4*(2*q+8)+4+(8*e+9))+(n₂+(2*(2*q+8)+2)),hu₃.trans (hu₂.trans hu₁),
    Nat.add_le_add_left (Nat.add_le_add_right hn₂ _) _,?_⟩
  intro depth
  have ht₁ := mn_native_exec_within he₁ 2 powerWordHeader_native depth _ (Nat.le_refl _)
  have ht₃ := mn_native_exec_within he₃' 0 (by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth _ (Nat.le_refl _)
  have ht := mn_seq_within_add ht₁ (mn_seq_within_add (he₂ depth) ht₃)
  refine (ht.mono (by intro d z hz; omega)).cast rfl ?_
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi220 : i = 220 <;> by_cases hi206 : i = 206 <;>
    simp [S₂',S₁,scalar,output,hi220,hi206,h220]

theorem boundaryUnscalePhysical_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (q p : ℕ) (hpq : p ≤ q/2) (xs : List GaussianInt)
    (hbound : ∀ z ∈ xs, |gv q z.re| ≤ 8*p+1 ∧ |gv q z.im| ≤ 8*p+1)
    (C : ℕ) (hpush : mnProgPush (cmulBlock (rsbCr boundaryFactorReg .dout .dtab .ya)
      (rmulOne (P := P) (Q := Q) (A := A) (U := U) boundaryFactorMulReg
        boundaryFactorMulReg_injective (by decide) hQ (rsbCr boundaryFactorReg .dout .dtab .ya))) ≤ C)
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hleft : ∀ i, S.L i = []) (hmul : ∀ i : Fin 64, S.R (boundaryFactorMulReg i) = [])
    (hready : RsbReady (boundaryFactorState S) (2*q+8) q)
    (he : (S.R 223).length = (q+q/2+1)) (hsrc : S.R 217 = cstream A (2*q+8) xs)
    (h184 : S.R 184 = []) (h220 : S.R 220 = []) (h221 : S.R 221 = [])
    (hya : S.R 208 = []) (hac2 : S.R 215 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ boundaryUnscalePhysicalCost q xs.length ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(realScalarWorkspace C (2*q+8) xs.length+2*(4*(2*q+8)+4+(8*(q+q/2+1)+9))))
        depth (boundaryUnscalePhysical hQ) (mk v S) n
        (mk v' {S with R := (Function.update S.R 217
          (cstream A (2*q+8) (xs.map (unscaleBoundaryWord q))))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := powerWordHeader_exec (body := body)
    (width := 160) (exponent := 223) (dst := 220) (parked := 221) (saved := 184) (tmp := 0)
    (by decide) (2*q+8) (q+q/2+1) (by omega) v S hready.wn he h220 h221 h184 (hmul 0)
  let scalar := csyms A (2*q+8) (⟨(2 : ℤ)^(q+q/2+1),0⟩ : GaussianInt)
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 220 scalar}
  have hstate : boundaryFactorState S₁ = Function.update (boundaryFactorState S) .dtab scalar :=
    boundaryFactorState_update S .dtab scalar
  have hrun := boundary_unscale_runs_within (body := body) boundaryFactorReg_injective boundaryFactorReg_disjoint
    boundaryFactorMulReg_injective (by decide) hQ hA q p hpq (boundaryFactorState S₁)
    (by rw [hstate]; exact hready.update .dtab (fun _ => by simp) scalar) xs hbound
    (by rw [hstate]; exact hsrc) (by rw [hstate]; rfl)
    (by rw [hstate]; exact hya) (by rw [hstate]; exact hac2) C hpush
  obtain ⟨v₂,S₂,n₂,hu₂,hn₂,hholds,hframe,he₂⟩ := hrun v₁ S₁ ⟨hleft,by
    intro i
    have hi220 : boundaryFactorMulReg i ≠ 220 := by
      intro hi
      have hv := congrArg (fun k : Fin 224 => k.val) hi
      have hi' := i.isLt
      change i.val = 220 at hv
      omega
    simpa only [S₁,Function.update_of_ne hi220] using hmul i⟩ (fun _ => rfl)
  have hS₂ := boundaryFactorFr_update .dout _ hframe hholds
  rw [hS₂] at he₂
  let output := cstream A (2*q+8) (xs.map (unscaleBoundaryWord q))
  let S₂' : Stacks 224 A := {S₁ with R := Function.update S₁.R 217 output}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 220 v₂ S₂'
  have hlen : (S₂'.R 220).length = 2*q+8 := by simp [S₂',S₁,scalar]
  have he₃' : Exec body (uclear 220) (mk v₂ S₂') (2*(2*q+8)+2)
      (mk v₃ {S₂' with R := Function.update S₂'.R 220 []}) := he₃.cast (by rw [hlen]) rfl
  refine ⟨v₃,(4*(2*q+8)+4+(8*(q+q/2+1)+9))+(n₂+(2*(2*q+8)+2)),hu₃.trans (hu₂.trans hu₁),
    Nat.add_le_add_left (Nat.add_le_add_right hn₂ _) _,?_⟩
  intro depth
  have ht₁ := mn_native_exec_within he₁ 2 powerWordHeader_native depth _ (Nat.le_refl _)
  have ht₃ := mn_native_exec_within he₃' 0 (by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth _ (Nat.le_refl _)
  have ht := mn_seq_within_add ht₁ (mn_seq_within_add (he₂ depth) ht₃)
  refine (ht.mono (by intro d z hz; omega)).cast rfl ?_
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi220 : i = 220 <;> by_cases hi217 : i = 217 <;>
    simp [S₂',S₁,scalar,output,hi220,hi217,h220]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
