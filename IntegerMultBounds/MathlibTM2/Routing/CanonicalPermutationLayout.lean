module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalProfileScope
public import IntegerMultBounds.MathlibTM2.Routing.PermutationReservoirFixed

/-! Canonical geometry and the concrete permutation producer share their scalar
inputs directly: reservoir/span are generated in the producer's input registers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {A : ℕ}

def canonicalPermutationGeometrySlot (j : Fin 28) : Fin 126 :=
  ⟨if j.val = 0 then 57 else if j.val = 9 then 70 else 98 + j.val, by have := j.isLt; split_ifs <;> omega⟩

def canonicalPermutationProducerSlot (j : Fin 98) : Fin 126 :=
  ⟨if j.val = 58 then 115 else if j.val = 59 then 114 else j.val, by have := j.isLt; split_ifs <;> omega⟩

theorem canonicalPermutationGeometrySlot_injective : Function.Injective canonicalPermutationGeometrySlot := by
  intro i j h
  have hi := i.isLt
  have hj := j.isLt
  have hv := congrArg (fun x : Fin 126 => x.val) h
  apply Fin.ext
  dsimp only [canonicalPermutationGeometrySlot] at hv
  split_ifs at hv <;> omega

theorem canonicalPermutationProducerSlot_injective : Function.Injective canonicalPermutationProducerSlot := by
  intro i j h
  have hi := i.isLt
  have hj := j.isLt
  have hv := congrArg (fun x : Fin 126 => x.val) h
  apply Fin.ext
  dsimp only [canonicalPermutationProducerSlot] at hv
  split_ifs at hv <;> omega

theorem canonicalPermutationProducerSlot_off (j : Fin 98) (h58 : j ≠ 58) (h59 : j ≠ 59) :
    canonicalPermutationProducerSlot j ∉ canonicalProfileTargets canonicalPermutationGeometrySlot := by
  have hj := j.isLt
  have hj58 : j.val ≠ 58 := fun h => h58 (Fin.ext h)
  have hj59 : j.val ≠ 59 := fun h => h59 (Fin.ext h)
  simp [canonicalProfileTargets, canonicalPermutationProducerSlot, canonicalPermutationGeometrySlot,
    hj58, hj59, Fin.ext_iff]
  omega

theorem canonicalPermutationProducer_keep (R : Fin 126 → List (Fin (A + 4))) (L n r : ℕ)
    (j : Fin 98) (h58 : j ≠ 58) (h59 : j ≠ 59) :
    canonicalProfileSetupBank R canonicalPermutationGeometrySlot L n r (canonicalPermutationProducerSlot j) =
      R (canonicalPermutationProducerSlot j) :=
  canonicalProfileSetupBank_keep R canonicalPermutationGeometrySlot L n r _
    (canonicalPermutationProducerSlot_off j h58 h59)

theorem canonicalPermutationProducer_scalars (R : Fin 126 → List (Fin (A + 4))) (L n r : ℕ) :
    let B := canonicalProfileSetupBank R canonicalPermutationGeometrySlot L n r
    B (canonicalPermutationProducerSlot 58) = binSyms L (routingReservoirWidth n (canonicalRouterGap n)) ∧
      B (canonicalPermutationProducerSlot 59) =
        binSyms L (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) := by
  simp [canonicalProfileSetupBank, canonicalDescriptorWidthsBank, canonicalResidueGeometryBank,
    canonicalGeometryBank, routerReservoirGeometryBank, routerGeometryBank,
    canonicalPermutationGeometrySlot, canonicalPermutationProducerSlot, canonicalProfileWidthSlot,
    canonicalProfileGeometrySlot, canonicalResidueCommonSlot, routerReservoirCommonSlot, canonicalRouterStride]

theorem canonicalPermutationProducer_blank (R : Fin 126 → List (Fin (A + 4))) (L n r : ℕ)
    (hblank : ∀ j : Fin 126, j.val < 98 → j ≠ 57 → j ≠ 70 → j ≠ 84 → j ≠ 85 → R j = [])
    (j : Fin 98) (h57 : j ≠ 57) (h58 : j ≠ 58) (h59 : j ≠ 59)
    (h70 : j ≠ 70) (h85 : j ≠ 85) (h84 : j ≠ 84) :
    canonicalProfileSetupBank R canonicalPermutationGeometrySlot L n r (canonicalPermutationProducerSlot j) = [] := by
  rw [canonicalPermutationProducer_keep R L n r j h58 h59]
  have hj := j.isLt
  have hj58 : j.val ≠ 58 := fun h => h58 (Fin.ext h)
  have hj59 : j.val ≠ 59 := fun h => h59 (Fin.ext h)
  have hv : (canonicalPermutationProducerSlot j).val = j.val := by
    simp [canonicalPermutationProducerSlot, hj58, hj59]
  have hneq (k : Fin 98) (hk : j ≠ k) :
      canonicalPermutationProducerSlot j ≠ Fin.castLE (by decide : 98 ≤ 126) k := by
    intro h
    apply hk
    apply Fin.ext
    have hh := congrArg (fun x : Fin 126 => x.val) h
    change (canonicalPermutationProducerSlot j).val = k.val at hh
    omega
  exact hblank _ (by omega) (hneq 57 h57) (hneq 70 h70) (hneq 84 h84) (hneq 85 h85)

end IntegerMultBounds.MathlibTM2.Routing
