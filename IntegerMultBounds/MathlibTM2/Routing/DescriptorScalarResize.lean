module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorScalarGenerate
public import IntegerMultBounds.MathlibTM2.Routing.BinaryResizeBatchScope

/-! Resize five compact geometric inputs into the shared descriptor encoding,
then generate all six derived palette operands. The fixed schedule is numeric-free. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}

def descriptorScalarInputIndex : Fin 5 → Fin 11 := ![0,1,2,5,6]
def descriptorScalarCoreSlot : Fin 17 → Fin 24 := Fin.castLE (by decide)
def descriptorScalarResizeSlot (j : Fin 5) : Fin 9 → Fin 24 :=
  ![22, ⟨17 + j.val, by have := j.isLt; omega⟩, 23,
    Fin.castLE (by decide) (descriptorScalarInputIndex j), 11,12,13,14,15]
theorem descriptorScalarResizeSlot_injective (j : Fin 5) : Function.Injective (descriptorScalarResizeSlot j) := by
  fin_cases j <;> decide +kernel

def descriptorScalarResizeProgram (rg : Fin 24 → Fin T) : Pr P T Q A U :=
  .seq (binaryResizeBatchProgram (fun j => rg ∘ descriptorScalarResizeSlot j) [0,1,2,3,4])
    (descriptorScalarGenerateProgram (rg ∘ descriptorScalarCoreSlot))

def descriptorScalarResizedBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 24 → Fin T) (W : ℕ) (p : Par) :=
  descriptorScalarBank (binaryResizeBatchBank R (fun j => rg ∘ descriptorScalarResizeSlot j)
    (fun _ => W) (fun j => repairDescriptorScalarPalette p (descriptorScalarInputIndex j)) [0,1,2,3,4])
    (rg ∘ descriptorScalarCoreSlot) W p

theorem descriptorScalarResize_exec (body : P → Pr P T Q A U)
    (rg : Fin 24 → Fin T) (hrg : Function.Injective rg) (M L W : ℕ) (p : Par)
    (hW : W < 2 ^ M)
    (hfit : p.wy + 2 * p.wc + 1 < 2 ^ W)
    (hrawFit : ∀ j : Fin 5, repairDescriptorScalarPalette p (descriptorScalarInputIndex j) < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (hwidth : S.R (rg 22) = binSyms M W)
    (hraw : ∀ j : Fin 5, S.R (rg ⟨17 + j.val, by have := j.isLt; omega⟩) =
      binSyms L (repairDescriptorScalarPalette p (descriptorScalarInputIndex j)))
    (hblank : ∀ j : Fin 24, j ∉ ([16,17,18,19,20,21,22] : List (Fin 24)) → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 10 * M * (4 * W + 11) + 60 * L + 224 * W + 315 ∧
      Exec body (descriptorScalarResizeProgram rg) (mk v S) m
        (mk v' { S with R := descriptorScalarResizedBank S.R rg W p }) := by
  let slots := fun j => rg ∘ descriptorScalarResizeSlot j
  let values := fun j => repairDescriptorScalarPalette p (descriptorScalarInputIndex j)
  have hdst : (([0,1,2,3,4] : List (Fin 5)).map (fun j => slots j 3)).Nodup := by
    simp [slots, descriptorScalarResizeSlot, descriptorScalarInputIndex, hrg.eq_iff]
  have sep : ∀ j i, i ≠ 3 → ∀ k, descriptorScalarResizeSlot j i ≠ descriptorScalarResizeSlot k 3 := by decide +kernel
  have scratch : ∀ j i, i ≠ 0 → i ≠ 1 → i ≠ 3 →
      descriptorScalarResizeSlot j i ∉ ([16,17,18,19,20,21,22] : List (Fin 24)) := by decide +kernel
  obtain ⟨v₁, m₁, hu₁, hm₁, hex₁⟩ := binaryResizeBatch_exec body slots
    (fun j => hrg.comp (descriptorScalarResizeSlot_injective j))
    (fun _ => M) (fun _ => L) (fun _ => W) values (fun _ => hW) hrawFit [0,1,2,3,4] hdst
    (fun j i hi k => hrg.ne (sep j i hi k)) v S
    (by intro j; exact hwidth)
    (by intro j; exact hraw j)
    (by intro j hj; apply hblank; fin_cases j <;> decide)
    (by intro j i h0 h1 h3; exact hblank _ (scratch j i h0 h1 h3))
  let C : Stacks T A := { S with R := binaryResizeBatchBank S.R slots (fun _ => W) values [0,1,2,3,4] }
  have ready (j : Fin 5) : C.R (slots j 3) = binSyms W (values j) :=
    binaryResizeBatchBank_at S.R slots (fun _ => W) values [0,1,2,3,4] hdst j (by fin_cases j <;> simp)
  have off : ∀ j : Fin 17, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 5 → j ≠ 6 → j ≠ 16 →
      descriptorScalarCoreSlot j ∉ ([0,1,2,5,6] : List (Fin 24)) ∧
      descriptorScalarCoreSlot j ∉ ([16,17,18,19,20,21,22] : List (Fin 24)) := by decide +kernel
  have cb : ∀ j : Fin 17, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 5 → j ≠ 6 → j ≠ 16 →
      C.R ((rg ∘ descriptorScalarCoreSlot) j) = [] := by
    intro j h0 h1 h2 h5 h6 h16
    obtain ⟨ho,hb⟩ := off j h0 h1 h2 h5 h6 h16
    have hk : rg (descriptorScalarCoreSlot j) ∉ ([0,1,2,3,4] : List (Fin 5)).map (fun k => slots k 3) := by
      simpa [slots, descriptorScalarResizeSlot, descriptorScalarInputIndex, hrg.eq_iff] using ho
    exact (binaryResizeBatchBank_keep S.R slots (fun _ => W) values [0,1,2,3,4] _ hk).trans (hblank _ hb)
  obtain ⟨v₂, m₂, hu₂, hm₂, hex₂⟩ := descriptorScalarGenerate_exec body (rg ∘ descriptorScalarCoreSlot)
    (hrg.comp (by decide +kernel : Function.Injective descriptorScalarCoreSlot)) W p hfit v₁ C
    (by exact ready 3) (by exact ready 4) (by exact ready 2) cb
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, Exec.seq hex₁ hex₂⟩
  simp only [binaryResizeBatchCost] at hm₁
  nlinarith only [hm₁, hm₂]

theorem descriptorScalarResizedBank_palette (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 24 → Fin T) (hrg : Function.Injective rg) (W : ℕ) (p : Par) (j : Fin 11) :
    descriptorScalarResizedBank R rg W p (rg (descriptorScalarCoreSlot (descriptorScalarPaletteSlot j))) =
      binSyms W (repairDescriptorScalarPalette p j) := by
  let slots := fun k => rg ∘ descriptorScalarResizeSlot k
  let values := fun k => repairDescriptorScalarPalette p (descriptorScalarInputIndex k)
  have hdst : (([0,1,2,3,4] : List (Fin 5)).map (fun k => slots k 3)).Nodup := by
    simp [slots, descriptorScalarResizeSlot, descriptorScalarInputIndex, hrg.eq_iff]
  have ready (k : Fin 5) :
      binaryResizeBatchBank R slots (fun _ => W) values [0,1,2,3,4] (slots k 3) = binSyms W (values k) :=
    binaryResizeBatchBank_at R slots (fun _ => W) values [0,1,2,3,4] hdst k (by fin_cases k <;> simp)
  unfold descriptorScalarResizedBank
  apply descriptorScalarBank_palette _ (rg ∘ descriptorScalarCoreSlot)
    (hrg.comp (by decide +kernel : Function.Injective descriptorScalarCoreSlot)) W p _ j
  intro k hk
  fin_cases k <;> first | exact ready 0 | exact ready 1 | exact ready 2 | exact ready 3 | exact ready 4 | simp at hk

end IntegerMultBounds.MathlibTM2.Routing
