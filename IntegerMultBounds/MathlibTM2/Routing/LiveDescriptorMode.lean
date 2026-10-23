module

public import IntegerMultBounds.MathlibTM2.Routing.RepairAffineDescriptor
public import IntegerMultBounds.MathlibTM2.Routing.RepairADescriptor

/-! Static descriptor modes choose the affine or grouped engine. The mode only
selects a fixed program; numerical dimensions remain live tape inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

inductive LiveDescriptorMode where
  | affine (key : RepairDescriptorKey) (hkey : ∀ j, key ≠ some (.A, j))
  | grouped (j : Fin 2)

namespace LiveDescriptorMode

def key : LiveDescriptorMode → RepairDescriptorKey
  | .affine key _ => key
  | .grouped j => some (.A, j)

def ofKey : RepairDescriptorKey → LiveDescriptorMode
  | none => .affine none (by intro j; simp)
  | some (.A, j) => .grouped j
  | some (.Z, j) => .affine (some (.Z, j)) (by intro i; simp)
  | some (.Y, j) => .affine (some (.Y, j)) (by intro i; simp)
  | some (.YZ, j) => .affine (some (.YZ, j)) (by intro i; simp)
  | some (.X, j) => .affine (some (.X, j)) (by intro i; simp)

theorem key_ofKey (key : RepairDescriptorKey) : (ofKey key).key = key := by
  cases key with
  | none => rfl
  | some pair => obtain ⟨off, j⟩ := pair; cases off <;> rfl

def stride (p : Par) : LiveDescriptorMode → ℕ
  | .affine key _ => repairAffineStride p key
  | .grouped _ => p.K

def base (p : Par) : LiveDescriptorMode → ℕ
  | .affine key _ => repairAffineOffset p key
  | .grouped _ => p.ρ + 1

def slots (p : Par) : LiveDescriptorMode → ℕ
  | .affine _ _ => p.n
  | .grouped _ => p.n * p.G

noncomputable section

def profileFrames {A : ℕ} (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (Ls : ℕ) : LiveDescriptorMode → List (Fin (A + 4))
  | .affine key _ => affineProfileFrames Ls (affineSourceProfile (repairAffineSources p X hG hK active s key))
  | .grouped j => affineProfileFrames Ls (affineSourceProfile (repairRotationSources p X hG hK active s .A j))

def backendCost (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (Li Lg Lk Ls Lw : ℕ) : LiveDescriptorMode → ℕ
  | .affine key _ => affineProfileDescriptorCost Li Lk Ls Lw (repairAffineStride p key) (repairAffineOffset p key)
      (repairCompactRows p key) (repairAffineSources p X hG hK active s key)
  | .grouped j => repairADescriptorCost p X hG hK active s j Li Lg Lk Ls Lw

end
end LiveDescriptorMode

structure LiveDescriptorWidths where
  indexBits : ℕ
  groupBits : ℕ
  strideBits : ℕ
  selectorBits : ℕ
  widthBits : ℕ

def LiveDescriptorWidths.coordinateBits (w : LiveDescriptorWidths) : ℕ := w.indexBits + w.strideBits

end IntegerMultBounds.MathlibTM2.Routing
