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

def backendBound (p : Par) (X Li Lg Lk Ls Lw : ℕ) : LiveDescriptorMode → ℕ
  | .affine key _ => affineProfileDescriptorBound Li Lk Ls Lw p.n
      (repairCompactRows p key) (repairCompactSourceWidth p X key)
  | .grouped _ => repairADescriptorBound p X Li Lg Lk Ls Lw

def uniformBackendBudget (n slots Li Lg Lk Ls Lw : ℕ) : ℕ :=
  affineProfileDescriptorBound Li Lk Ls Lw slots n n +
    groupedProfileDescriptorBound Li Lg Lk Ls Lw slots n n

theorem uniformBackendBudget_widths_mono (n slots : ℕ)
    {Li Li' Lg Lg' Lk Lk' Ls Ls' Lw Lw' : ℕ}
    (hi : Li ≤ Li') (hg : Lg ≤ Lg') (hk : Lk ≤ Lk') (hs : Ls ≤ Ls') (hw : Lw ≤ Lw') :
    uniformBackendBudget n slots Li Lg Lk Ls Lw ≤
      uniformBackendBudget n slots Li' Lg' Lk' Ls' Lw' :=
  Nat.add_le_add (affineProfileDescriptorBound_widths_mono hi hk hs hw slots n n)
    (groupedProfileDescriptorBound_widths_mono hi hg hk hs hw slots n n)

theorem backendBound_uniform (p : Par) (X n slots Li Lg Lk Ls Lw : ℕ)
    (hfields : IntegerMultBounds.MathlibTM2.Layer.CompactDigits.fieldsLen (selectiveLen p X) = n)
    (hn : p.n ≤ slots) (hgroup : p.n * p.G ≤ slots) (mode : LiveDescriptorMode) :
    backendBound p X Li Lg Lk Ls Lw mode ≤
      uniformBackendBudget n slots Li Lg Lk Ls Lw := by
  cases mode with
  | affine key hkey =>
    have hr := repairCompactRows_le_fields p X key
    have hw := repairCompactSourceWidth_le_fields p X key
    rw [hfields] at hr hw
    have hc := affineProfileDescriptorBound_mono Li Lk Ls Lw hn hr hw
    change affineProfileDescriptorBound Li Lk Ls Lw p.n _ _ ≤ _
    unfold uniformBackendBudget
    omega
  | grouped j =>
    have hr := repairCompactRows_le_fields p X (some (.A, j))
    have hw := repairCompactSourceWidth_le_fields p X (some (.A, j))
    rw [hfields] at hr hw
    have hc := groupedProfileDescriptorBound_mono Li Lg Lk Ls Lw hgroup hr hw
    change groupedProfileDescriptorBound Li Lg Lk Ls Lw (p.n * p.G) p.wy
      (selectiveSourceWidth p X .A) ≤ _
    dsimp only [repairCompactRows, repairCompactSourceWidth, selectiveTargetWidth] at hc
    unfold uniformBackendBudget
    omega

theorem backendCost_le (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (hGK : p.G < p.K) (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (Li Lg Lk Ls Lw : ℕ) (mode : LiveDescriptorMode)
    (hfit : repairCompactRows p mode.key < 2 ^ (Li + Lk)) :
    backendCost p X hG hK active s Li Lg Lk Ls Lw mode ≤
      backendBound p X Li Lg Lk Ls Lw mode := by
  cases mode with
  | affine key hkey =>
    exact affineProfileDescriptorCost_le_of_positions Li Lk Ls Lw _ _ _ _
      (repairAffineStride_positive p hG hK key) hfit
      (repairAffinePosition_bound p hG hK key hkey)
  | grouped j =>
    exact repairADescriptorCost_le_all p X hG hK hGK active s j Li Lg Lk Ls Lw hfit

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
