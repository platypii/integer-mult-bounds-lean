module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorScalarFields
public import IntegerMultBounds.MathlibTM2.Routing.BinaryResizeBatchScope

/-! Install the 55 descriptor scalars from one shared palette. The first 46
registers are the canonical scalar scope; destinations occupy the next 55. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def descriptorScalarJobs : List (Fin 11 × Fin 5) :=
  (List.finRange 11).product (List.finRange 5)

def descriptorScalarDestination (q : Fin 11 × Fin 5) : Fin 101 :=
  ⟨46 + 5 * q.1.val + q.2.val, by have := q.1.isLt; have := q.2.isLt; omega⟩

theorem descriptorScalarDestination_injective : Function.Injective descriptorScalarDestination := by
  rintro ⟨j,f⟩ ⟨k,g⟩ h
  have hv := congrArg Fin.val h
  simp only [descriptorScalarDestination] at hv
  have := j.isLt; have := k.isLt; have := f.isLt; have := g.isLt
  have hj : j = k := Fin.ext (by omega)
  have hf : f = g := Fin.ext (by omega)
  cases hj; cases hf; rfl

def descriptorScalarInstallSlot (q : Fin 11 × Fin 5) : Fin 9 → Fin 101 :=
  ![(if q.2 = 0 then 21 else 26),
    ⟨28 + (repairDescriptorScalarSlot q.1 q.2).val, by
      have := (repairDescriptorScalarSlot q.1 q.2).isLt; omega⟩,
    45, descriptorScalarDestination q,39,40,41,42,43]

theorem descriptorScalarInstallSlot_injective (q : Fin 11 × Fin 5) :
    Function.Injective (descriptorScalarInstallSlot q) := by
  obtain ⟨j,f⟩ := q
  fin_cases j <;> fin_cases f <;> decide +kernel

theorem descriptorScalarInstallSlot_separate (q : Fin 11 × Fin 5) (i : Fin 9)
    (hi : i ≠ 3) (k : Fin 11 × Fin 5) :
    descriptorScalarInstallSlot q i ≠ descriptorScalarInstallSlot k 3 := by
  have hp := (repairDescriptorScalarSlot q.1 q.2).isLt
  have hk := k.1.isLt
  have hf := k.2.isLt
  have hs : (descriptorScalarInstallSlot q i).val < 46 := by
    fin_cases i <;> simp_all [descriptorScalarInstallSlot] <;>
      first | omega | (split <;> norm_num)
  intro h
  rw [h] at hs
  change 46 + 5 * k.1.val + k.2.val < 46 at hs
  omega

def descriptorScalarInstallProgram (rg : Fin 101 → Fin T) : Pr P T Q A U :=
  binaryResizeBatchProgram (fun q => rg ∘ descriptorScalarInstallSlot q) descriptorScalarJobs

def descriptorScalarInstalledBank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 101 → Fin T) (p : Par) (w : LiveDescriptorWidths) :=
  binaryResizeBatchBank R (fun q => rg ∘ descriptorScalarInstallSlot q)
    (fun q => repairDescriptorScalarWidth w q.2)
    (fun q => repairDescriptorScalarPalette p (repairDescriptorScalarSlot q.1 q.2)) descriptorScalarJobs

theorem descriptorScalarJobs_nodup : descriptorScalarJobs.Nodup := by
  decide +kernel

theorem descriptorScalarJobs_mem (q : Fin 11 × Fin 5) : q ∈ descriptorScalarJobs := by
  obtain ⟨j,f⟩ := q
  fin_cases j <;> fin_cases f <;> decide +kernel

theorem descriptorScalarInstallCost_le (M W B : ℕ) (w : LiveDescriptorWidths)
    (hB : ∀ f, repairDescriptorScalarWidth w f ≤ B) :
    binaryResizeBatchCost (fun _ => M) (fun _ => W)
      (fun q : Fin 11 × Fin 5 => repairDescriptorScalarWidth w q.2) descriptorScalarJobs ≤
      55 * (2 * M * (4 * B + 11) + 12 * W + 26 * B + 42) + 1 := by
  have bound (jobs : List (Fin 11 × Fin 5)) :
      binaryResizeBatchCost (fun _ => M) (fun _ => W)
        (fun q => repairDescriptorScalarWidth w q.2) jobs ≤
        jobs.length * (2 * M * (4 * B + 11) + 12 * W + 26 * B + 42) + 1 := by
    induction jobs with
    | nil => simp [binaryResizeBatchCost]
    | cons q jobs ih =>
        have hf := hB q.2
        have hm := Nat.mul_le_mul_left (2 * M)
          (show 4 * repairDescriptorScalarWidth w q.2 + 11 ≤ 4 * B + 11 by omega)
        simp only [binaryResizeBatchCost, List.length_cons]
        nlinarith only [ih, hf, hm]
  have hl : descriptorScalarJobs.length = 55 := by decide +kernel
  simpa only [hl] using bound descriptorScalarJobs

theorem descriptorScalarInstalledBank_operands (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 101 → Fin T) (hrg : Function.Injective rg)
    (p : Par) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (source : Fin p.n → SlotSource p 0)
    (w : LiveDescriptorWidths) (q : Fin 11 × Fin 5) :
    descriptorScalarInstalledBank R rg p w (rg (descriptorScalarDestination q)) =
      canonicalDescriptorOperands p 0 hG hK active source w (descriptorScalarRole q.1 q.2) := by
  have hd : (descriptorScalarJobs.map
      (fun q => (rg ∘ descriptorScalarInstallSlot q) 3)).Nodup := by
    exact descriptorScalarJobs_nodup.map (hrg.comp descriptorScalarDestination_injective)
  rw [descriptorScalarInstalledBank,
    show rg (descriptorScalarDestination q) = (rg ∘ descriptorScalarInstallSlot q) 3 from rfl,
    binaryResizeBatchBank_at _ _ _ _ _ hd q (descriptorScalarJobs_mem q)]
  exact descriptorScalarRole_operands p hG hK active source w q.1 q.2

theorem descriptorScalarInstall_exec (body : P → Pr P T Q A U)
    (rg : Fin 101 → Fin T) (hrg : Function.Injective rg)
    (M W : ℕ) (p : Par) (w : LiveDescriptorWidths)
    (hwidthFit : ∀ f, repairDescriptorScalarWidth w f < 2 ^ M)
    (hfit : ∀ j, repairDescriptorScalarPalette p j < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : ∀ q, S.R (rg (descriptorScalarInstallSlot q 0)) =
      binSyms M (repairDescriptorScalarWidth w q.2))
    (hpalette : ∀ j : Fin 11,
      S.R (rg ⟨28 + j.val, by have := j.isLt; omega⟩) =
        binSyms W (repairDescriptorScalarPalette p j))
    (houtput : ∀ q, S.R (rg (descriptorScalarDestination q)) = [])
    (hblank : ∀ i : Fin 101, i ∈ ([39,40,41,42,43,45] : List (Fin 101)) →
      S.R (rg i) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ binaryResizeBatchCost (fun _ => M) (fun _ => W)
        (fun q => repairDescriptorScalarWidth w q.2) descriptorScalarJobs ∧
      Exec body (descriptorScalarInstallProgram rg) (mk v S) m
        (mk v' { S with R := descriptorScalarInstalledBank S.R rg p w }) := by
  apply binaryResizeBatch_exec body (fun q => rg ∘ descriptorScalarInstallSlot q)
    (fun q => hrg.comp (descriptorScalarInstallSlot_injective q))
    (fun _ => M) (fun _ => W) (fun q => repairDescriptorScalarWidth w q.2)
    (fun q => repairDescriptorScalarPalette p (repairDescriptorScalarSlot q.1 q.2))
    (fun q => hwidthFit q.2) (fun q => hfit _) descriptorScalarJobs
  · exact descriptorScalarJobs_nodup.map (hrg.comp descriptorScalarDestination_injective)
  · intro q i hi k
    exact hrg.ne (descriptorScalarInstallSlot_separate q i hi k)
  · exact hwidth
  · intro q
    exact hpalette (repairDescriptorScalarSlot q.1 q.2)
  · intro q _
    exact houtput q
  · intro q i h0 h1 h3
    apply hblank
    fin_cases i <;> simp_all [descriptorScalarInstallSlot]

end
end IntegerMultBounds.MathlibTM2.Routing
