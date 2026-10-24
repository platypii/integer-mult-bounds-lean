module

public import IntegerMultBounds.MathlibTM2.Routing.ClassifierGenerate
public import IntegerMultBounds.MathlibTM2.Routing.BinaryScalarWidthBatchClean

/-! Restore the classifier operand and width banks after a framed call. All
original descriptor inputs and a disjoint output stream are preserved. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def classifierScalarTargets (rg : Fin 118 → Fin T) : List (Fin T) :=
  classifierScalarJobs.map (fun i => rg (classifierScalarDestination i))
def classifierWidthTargets (rg : Fin 118 → Fin T) : List (Fin T) :=
  classifierWidthJobs.map (fun i => rg (classifierWidthDestination i))
def classifierOperandCleanProgram (rg : Fin 118 → Fin T) : Pr P T Q A U :=
  .seq (metadataClean (classifierScalarTargets rg)) (metadataClean (classifierWidthTargets rg))

theorem classifierOperandClean_exec (body : P → Pr P T Q A U)
    (rg : Fin 118 → Fin T) (hrg : Function.Injective rg) (L W : ℕ) (p : Par)
    (hfit : ∀ i, classifierScalarValue p i < 2 ^ classifierScalarInputWidth L W i)
    (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i : Fin 118, 108 ≤ i.val → S.R (rg i) = [])
    (dst : Fin T) (hoff : ∀ i, rg i ≠ dst) (output : List (Fin (A + 4))) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 20 * (L+W) + 22 ∧
      Exec body (classifierOperandCleanProgram rg)
        (mk v { S with R := Function.update (classifierGeneratedBank S.R rg L W p) dst output }) m
        (mk v' { S with R := Function.update S.R dst output }) := by
  let B := classifierWidthBank S.R rg L W p
  let C := classifierGeneratedBank S.R rg L W p
  have hs : (classifierScalarTargets rg).Nodup := by
    simp [classifierScalarTargets,classifierScalarJobs,classifierScalarDestination,hrg.eq_iff]
  have hw : (classifierWidthTargets rg).Nodup := by
    simp [classifierWidthTargets,classifierWidthJobs,classifierWidthDestination,hrg.eq_iff]
  have scalarBlank (i : Fin 6) : B (rg (classifierScalarDestination i)) = [] := by
    unfold B classifierWidthBank
    rw [binaryScalarWidthBatchBank_keep]
    · apply hblank
      change 108 ≤ 112 + i.val
      omega
    · simp [classifierWidthJobs,classifierWidthSlot,classifierWidthDestination,
        classifierScalarDestination,hrg.eq_iff,Fin.ext_iff]
      all_goals have := i.isLt; omega
  have restoreS : metadataCleared C (classifierScalarTargets rg) = B :=
    binaryResizeBatchBank_clean B (fun i => rg ∘ classifierScalarSlot i)
      (classifierScalarWidth p) (classifierScalarValue p) classifierScalarJobs (fun i _ => scalarBlank i)
  have restoreW : metadataCleared B (classifierWidthTargets rg) = S.R :=
    binaryScalarWidthBatchBank_clean S.R (fun i => rg ∘ classifierWidthSlot i)
      (classifierWidthRawWidth L W) (classifierWidthValue p) classifierWidthJobs (by
        intro i _
        apply hblank
        change 108 ≤ 108 + i.val
        omega)
  have offS : dst ∉ classifierScalarTargets rg := by
    intro hm
    obtain ⟨i,_,he⟩ := List.mem_map.mp hm
    exact hoff _ he
  have offW : dst ∉ classifierWidthTargets rg := by
    intro hm
    obtain ⟨i,_,he⟩ := List.mem_map.mp hm
    exact hoff _ he
  obtain ⟨v₁,hu₁,he₁⟩ := metadataClean_framed_exec body _ hs C B restoreS dst offS output v S
  obtain ⟨v₂,hu₂,he₂⟩ := metadataClean_framed_exec body _ hw B S.R restoreW dst offW output v₁ S
  have costS : metadataCleanCost C (classifierScalarTargets rg) ≤ 6 * (2 * (L+W) + 2) + 1 := by
    have hx := binaryResizeBatchBank_cleanCost_le B (fun i => rg ∘ classifierScalarSlot i)
      (classifierScalarWidth p) (classifierScalarValue p) classifierScalarJobs hs (L+W)
      (fun i _ => (classifierScalarWidth_le_input L W p hfit i).trans (classifierScalarInputWidth_le L W i))
    simpa [C,classifierGeneratedBank,classifierScalarInstalledBank,classifierScalarTargets,
      classifierScalarSlot,classifierScalarJobs] using hx
  have costW : metadataCleanCost B (classifierWidthTargets rg) ≤ 4 * (2 * (L+W) + 2) + 1 := by
    have hx := binaryScalarWidthBatchBank_cleanCost_le S.R (fun i => rg ∘ classifierWidthSlot i)
      (classifierWidthRawWidth L W) (classifierWidthValue p) classifierWidthJobs hw (L+W)
      (by intro i _; fin_cases i <;> simp [classifierWidthRawWidth])
    simpa [B,classifierWidthBank,classifierWidthTargets,classifierWidthSlot,classifierWidthJobs] using hx
  refine ⟨v₂,_,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  nlinarith only [costS,costW]

end
end IntegerMultBounds.MathlibTM2.Routing
