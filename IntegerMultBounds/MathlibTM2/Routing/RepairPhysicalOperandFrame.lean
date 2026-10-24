module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRepairOperandReady
public import IntegerMultBounds.MathlibTM2.Routing.FramedCoreCopy

/-! Read generated repair scalars in physical core order. Every nonstream
scratch register is included, sharing one restored empty source. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def repairPhysicalOperandSource : Fin repairT → Fin 130 :=
  Function.extend repairSetupSource canonicalRepairOperandSource (fun _ => 128)

theorem repairPhysicalOperandSource_scratch (i : Fin repairT) :
    repairPhysicalOperandSource i ≠ 40 ∧ repairPhysicalOperandSource i ≠ 41 := by
  by_cases hi : ∃ key, repairSetupSource key = i
  · obtain ⟨key,rfl⟩ := hi
    rw [repairPhysicalOperandSource,repairSetupSource_injective.extend_apply]
    cases key with
    | inl key =>
      cases key with
      | field f => fin_cases f <;> decide
      | _ => simp [canonicalRepairOperandSource]
    | inr key => cases key <;> decide
  · rw [repairPhysicalOperandSource,Function.extend_apply' _ _ _ hi]
    decide

theorem canonicalRepairBlockGeneratedBank_physical (R : Fin T → List (Fin (A+4)))
    (rg : Fin 130 → Fin T) (hrg : Function.Injective rg) (L n B : ℕ)
    (hlarge : canonicalRouterStride n ≤ n) (r : Fin (canonicalRouterStride n))
    (hblank : R (rg 128) = []) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    (fun i => canonicalRepairBlockGeneratedBank R rg L n r.val B (rg (repairPhysicalOperandSource i))) =
      canonicalRepairInput p 0 (canonicalScalarWidth 1) (canonicalScalarWidth (n+B+1)) (n+1)
        (canonicalScalarWidth B) (canonicalScalarWidth (n+1)) 1 B [] := by
  dsimp only
  have bank := canonicalRepairBlockGeneratedBank_operands R rg hrg L n B hlarge r hblank
  funext i
  by_cases hi : ∃ key, repairSetupSource key = i
  · obtain ⟨key,rfl⟩ := hi
    rw [repairPhysicalOperandSource,repairSetupSource_injective.extend_apply,
      canonicalRepairInput_source]
    exact congrFun bank key
  · rw [repairPhysicalOperandSource,Function.extend_apply' _ _ _ hi,
      canonicalRepairInput,Function.extend_apply' _ _ _ hi]
    have empty := congrFun bank (.inr .row)
    simpa [canonicalRepairOperandSource,canonicalRepairPayload] using empty

def repairPhysicalOperandCopy (rg : Fin 130 → Fin T) (dst : Fin T)
    (delimiter : Fin (A+4)) : Pr P T Q A U :=
  delimitedBankCopy dst (rg 40) (rg 41) delimiter
    (framedCoreDestinations (rg ∘ repairPhysicalOperandSource) repairHost.src)

def repairPhysicalOperandFrame (delimiter : Fin (A+4)) (rg : Fin 130 → Fin T)
    (words : Fin repairT → List (Fin (A+4))) :=
  delimitedBankFrames delimiter (framedCoreJobs (rg ∘ repairPhysicalOperandSource) repairHost.src words)

theorem repairPhysicalOperandCopy_exec (body : P → Pr P T Q A U)
    (rg : Fin 130 → Fin T) (hrg : Function.Injective rg) (dst : Fin T)
    (hoff : ∀ i, rg i ≠ dst) (delimiter : Fin (A+4))
    (words : Fin repairT → List (Fin (A+4))) (B : ℕ)
    (hwords : ∀ i, i ≠ repairHost.src → (words i).length ≤ B)
    (v : HS T Q A U) (S : Stacks T A)
    (hbank : ∀ i, i ≠ repairHost.src → S.R (rg (repairPhysicalOperandSource i)) = words i)
    (htmp : S.R (rg 40) = []) (hwork : S.R (rg 41) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 6*(repairT*(B+1))+repairT+1 ∧
      Exec body (repairPhysicalOperandCopy rg dst delimiter) (mk v S) m
        (mk v' { S with R := (Function.update S.R dst
          (repairPhysicalOperandFrame delimiter rg words ++ S.R dst)) }) := by
  obtain ⟨v',hu,he⟩ := framedCoreCopy_exec body (rg ∘ repairPhysicalOperandSource) repairHost.src
    dst (rg 40) (rg 41) (by simp [List.nodup_cons,(hoff 40).symm,(hoff 41).symm,hrg.eq_iff])
    (by intro i; exact ⟨hoff _,hrg.ne (repairPhysicalOperandSource_scratch i).1,
      hrg.ne (repairPhysicalOperandSource_scratch i).2⟩) delimiter words v S hbank htmp hwork
  have hc := framedCoreCopyCost_le (rg ∘ repairPhysicalOperandSource) repairHost.src delimiter words B hwords
  exact ⟨v',_,hu,hc,he⟩

end
end IntegerMultBounds.MathlibTM2.Routing
