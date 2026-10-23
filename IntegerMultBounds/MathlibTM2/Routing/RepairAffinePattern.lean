module

public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorCoordinates

/-! A single affine profile interface covers the key descriptor and all rotations
except the two temporary-bit A descriptors, which need grouped positions. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

def repairAffineStride : RepairDescriptorKey → ℕ
  | none | some (.Z, _) => p.K
  | _ => p.G

def repairAffineOffset : RepairDescriptorKey → ℕ
  | none | some (.Z, _) => p.ρ
  | _ => 0

def repairAffineSources : (key : RepairDescriptorKey) →
    Fin p.n → Option (Fin (repairCompactSourceWidth p X key))
  | none => selectiveKeySources p X active s
  | some (.A, _) => fun _ => none
  | some (.Z, j) => repairRotationSources p X hG hK active s .Z j
  | some (.Y, j) => repairRotationSources p X hG hK active s .Y j
  | some (.YZ, j) => repairRotationSources p X hG hK active s .YZ j
  | some (.X, j) => repairRotationSources p X hG hK active s .X j

theorem repairAffinePattern_eq (key : RepairDescriptorKey) (hkey : ∀ j, key ≠ some (.A, j)) :
    sparsePattern (L := repairCompactRows p key)
      (fun c => c * repairAffineStride p key + repairAffineOffset p key)
      (repairAffineSources p X hG hK active s key) = repairCompactPattern p X hG hK active s key := by
  cases key with
  | none =>
    change sparsePattern (fun c => c * p.K + p.ρ) _ = sparsePattern (posS p) _
    congr 1
    funext c
    exact Nat.add_comm _ _
  | some pair =>
    obtain ⟨off, j⟩ := pair
    cases off with
    | A => exact (hkey j rfl).elim
    | Z =>
      rw [show repairCompactPattern p X hG hK active s (some (.Z, j)) =
        sparsePattern (posS p) (repairRotationSources p X hG hK active s .Z j) from
          repairRotationPattern_sparse p X hG hK active s .Z j]
      change sparsePattern (fun c => c * p.K + p.ρ) _ = sparsePattern (posS p) _
      congr 1
      funext c
      exact Nat.add_comm _ _
    | Y => exact repairRotationPattern_sparse p X hG hK active s .Y j |>.symm
    | YZ => exact repairRotationPattern_sparse p X hG hK active s .YZ j |>.symm
    | X => exact repairRotationPattern_sparse p X hG hK active s .X j |>.symm

theorem repairAffinePattern_word {A : ℕ} (key : RepairDescriptorKey) (hkey : ∀ j, key ≠ some (.A, j)) :
    (patternTable (sparsePattern (L := repairCompactRows p key)
      (fun c => c * repairAffineStride p key + repairAffineOffset p key)
      (repairAffineSources p X hG hK active s key))).flatten.map (IntegerMultBounds.bitSymbol (a := A)) =
      repairDescriptorWord p X hG hK active s key := by
  rw [repairAffinePattern_eq p X hG hK active s key hkey]
  exact repairCompactPattern_word p X hG hK active s key

include hG hK in
theorem repairAffineStride_positive (key : RepairDescriptorKey) : 0 < repairAffineStride p key := by
  cases key with
  | none => exact hK
  | some pair => obtain ⟨off, j⟩ := pair; cases off <;> first | exact hG | exact hK

theorem repairAffineOffset_le_rows (key : RepairDescriptorKey) : repairAffineOffset p key ≤ repairCompactRows p key := by
  cases key with
  | none => dsimp only [repairAffineOffset, repairCompactRows, Par.wy]; omega
  | some pair =>
    obtain ⟨off, j⟩ := pair
    cases off <;> simp [repairAffineOffset, repairCompactRows, selectiveTargetWidth, Par.wy] <;> omega

include hG hK in
theorem repairAffinePosition_bound (key : RepairDescriptorKey) (hkey : ∀ j, key ≠ some (.A, j))
    (c : Fin p.n) : c.val * repairAffineStride p key + repairAffineOffset p key < repairCompactRows p key := by
  cases key with
  | none =>
    have hh := repairKeyCoordinates_bound p hK c.val c.isLt
    simpa only [posS, repairAffineStride, repairAffineOffset, repairCompactRows, Nat.add_comm p.ρ] using hh
  | some pair =>
    obtain ⟨off, j⟩ := pair
    cases off with
    | A => exact (hkey j rfl).elim
    | Z =>
      have hh := repairKeyCoordinates_bound p hK c.val c.isLt
      simpa only [posS, repairAffineStride, repairAffineOffset, repairCompactRows, selectiveTargetWidth, Nat.add_comm p.ρ] using hh
    | Y => exact Nat.mul_lt_mul_of_pos_right c.isLt hG
    | YZ => exact Nat.mul_lt_mul_of_pos_right c.isLt hG
    | X => exact Nat.mul_lt_mul_of_pos_right c.isLt hG

end
end IntegerMultBounds.MathlibTM2.Routing
