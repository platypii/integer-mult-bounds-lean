module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRepairOperandReady
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankCopy
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankTrace

/-! Serialize the complete initial repair bank in setup-key order. Repeated
zero and empty sources are preserved by the generic delimited copier. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def repairOperandFrameJobs (rg : Fin 130 → Fin T) (words : RepairSetupKey → List (Fin (A+4))) :=
  repairSetupKeys.map (fun key => (rg (canonicalRepairOperandSource key),words key))

def repairOperandFrame (delimiter : Fin (A+4)) (rg : Fin 130 → Fin T)
    (words : RepairSetupKey → List (Fin (A+4))) :=
  delimitedBankFrames delimiter (repairOperandFrameJobs rg words)

def repairOperandCopy (rg : Fin 130 → Fin T) (dst : Fin T)
    (delimiter : Fin (A+4)) : Pr P T Q A U :=
  delimitedBankCopy dst (rg 40) (rg 41) delimiter
    (repairSetupKeys.map (fun key => rg (canonicalRepairOperandSource key)))

theorem canonicalRepairOperandSource_scratch (key : RepairSetupKey) :
    canonicalRepairOperandSource key ≠ 40 ∧ canonicalRepairOperandSource key ≠ 41 := by
  cases key with
  | inl key =>
    cases key with
    | field f => fin_cases f <;> decide
    | _ => simp [canonicalRepairOperandSource]
  | inr key => cases key <;> decide

theorem repairOperandCopy_exec (body : P → Pr P T Q A U)
    (rg : Fin 130 → Fin T) (hrg : Function.Injective rg) (dst : Fin T)
    (hoff : ∀ i, rg i ≠ dst) (delimiter : Fin (A+4))
    (words : RepairSetupKey → List (Fin (A+4))) (B : ℕ) (hwords : ∀ key, (words key).length ≤ B)
    (v : HS T Q A U) (S : Stacks T A)
    (hbank : ∀ key, S.R (rg (canonicalRepairOperandSource key)) = words key)
    (htmp : S.R (rg 40) = []) (hwork : S.R (rg 41) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ repairSetupKeys.length * (6*B+7)+1 ∧
      Exec body (repairOperandCopy rg dst delimiter) (mk v S) m
        (mk v' { S with R := (Function.update S.R dst
          (repairOperandFrame delimiter rg words ++ S.R dst)) }) := by
  have hreg : [dst,rg 40,rg 41].Nodup := by
    simp [List.nodup_cons,(hoff 40).symm,(hoff 41).symm,hrg.ne (by decide : (40 : Fin 130) ≠ 41)]
  obtain ⟨v',hu,he⟩ := delimitedBankCopy_exec body dst (rg 40) (rg 41) hreg delimiter
    (repairOperandFrameJobs rg words) (by
      intro j hj
      obtain ⟨key,_,rfl⟩ := List.mem_map.mp hj
      exact ⟨hoff _,hrg.ne (canonicalRepairOperandSource_scratch key).1,
        hrg.ne (canonicalRepairOperandSource_scratch key).2⟩) v S
    (by intro j hj; obtain ⟨key,_,rfl⟩ := List.mem_map.mp hj; exact hbank key) htmp hwork
  have hl : (repairOperandFrameJobs rg words).length = repairSetupKeys.length := by
    simp [repairOperandFrameJobs]
  have hf := delimitedBankFrames_length_le delimiter (repairOperandFrameJobs rg words) B (by
    intro j hj
    obtain ⟨key,_,rfl⟩ := List.mem_map.mp hj
    exact hwords key)
  have hc : delimitedBankCopyCost (repairOperandFrameJobs rg words) ≤
      repairSetupKeys.length * (6*B+7)+1 := by
    rw [delimitedBankCopyCost_eq delimiter,hl]
    rw [hl] at hf
    nlinarith only [hf]
  refine ⟨v',delimitedBankCopyCost (repairOperandFrameJobs rg words),hu,hc,?_⟩
  simpa only [repairOperandCopy,repairOperandFrame,repairOperandFrameJobs,List.map_map,Function.comp_def] using he

end
end IntegerMultBounds.MathlibTM2.Routing
