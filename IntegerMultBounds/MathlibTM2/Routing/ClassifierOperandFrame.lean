module

public import IntegerMultBounds.MathlibTM2.Routing.ClassifierOperandBank
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankCopy
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankTrace

/-! Serialize the complete classifier bank in its sixteen-register order,
preserving operands and restoring copy scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def classifierOperandFrameJobs (rg : Fin 118 → Fin T) (words : Fin 16 → List (Fin (A + 4))) :=
  (List.finRange 16).map (fun i => (rg (classifierOperandSource i),words i))

def classifierOperandFrame (delimiter : Fin (A + 4)) (rg : Fin 118 → Fin T)
    (words : Fin 16 → List (Fin (A + 4))) :=
  delimitedBankFrames delimiter (classifierOperandFrameJobs rg words)

def classifierOperandCopy (rg : Fin 118 → Fin T) (dst : Fin T)
    (delimiter : Fin (A + 4)) : Pr P T Q A U :=
  delimitedBankCopy dst (rg 40) (rg 41) delimiter
    ((List.finRange 16).map (fun i => rg (classifierOperandSource i)))

theorem classifierOperandCopy_exec (body : P → Pr P T Q A U)
    (rg : Fin 118 → Fin T) (hrg : Function.Injective rg) (dst : Fin T)
    (hoff : ∀ i, rg i ≠ dst) (delimiter : Fin (A + 4))
    (words : Fin 16 → List (Fin (A + 4))) (B : ℕ) (hwords : ∀ i, (words i).length ≤ B)
    (v : HS T Q A U) (S : Stacks T A)
    (hbank : ∀ i, S.R (rg (classifierOperandSource i)) = words i)
    (htmp : S.R (rg 40) = []) (hwork : S.R (rg 41) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 16 * (6 * B + 7) + 1 ∧
      Exec body (classifierOperandCopy rg dst delimiter) (mk v S) m
        (mk v' { S with R := (Function.update S.R dst
          (classifierOperandFrame delimiter rg words ++ S.R dst)) }) := by
  have hreg : [dst,rg 40,rg 41].Nodup := by
    simp [List.nodup_cons,(hoff 40).symm,(hoff 41).symm,hrg.ne (by decide : (40 : Fin 118) ≠ 41)]
  obtain ⟨v',hu,he⟩ := delimitedBankCopy_exec body dst (rg 40) (rg 41) hreg delimiter
    (classifierOperandFrameJobs rg words) (by
      intro j hj
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
      exact ⟨hoff _,hrg.ne (classifierOperandSource_scratch i).1,
        hrg.ne (classifierOperandSource_scratch i).2⟩) v S
    (by intro j hj; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj; exact hbank i) htmp hwork
  have hl : (classifierOperandFrameJobs rg words).length = 16 := by simp [classifierOperandFrameJobs]
  have hf := delimitedBankFrames_length_le delimiter (classifierOperandFrameJobs rg words) B (by
    intro j hj
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
    exact hwords i)
  have hc : delimitedBankCopyCost (classifierOperandFrameJobs rg words) ≤ 16 * (6 * B + 7) + 1 := by
    rw [delimitedBankCopyCost_eq delimiter,hl]
    rw [hl] at hf
    omega
  refine ⟨v',delimitedBankCopyCost (classifierOperandFrameJobs rg words),hu,hc,?_⟩
  simpa only [classifierOperandCopy,classifierOperandFrame,classifierOperandFrameJobs,
    List.map_map,Function.comp_def] using he

end
end IntegerMultBounds.MathlibTM2.Routing
