module

public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorData

/-! The common bank supplies all compiler workspace invariants. These facts
hold for every job and survive earlier descriptor writes through Ready.update_core. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section
namespace LiveDescriptorReady

variable {N J A : ℕ} {p : Par} {X : ℕ} {hG : 0 < p.G} {hK : 0 < p.K}
  {active : Fin p.n → Bool} {s : Fin p.n → SlotSource p X}
  {mode : Fin J → LiveDescriptorMode} {w : LiveDescriptorWidths}
  {R : Fin (liveDescriptorT N J) → List (Fin (A + 4))}
  (h : LiveDescriptorReady p X hG hK active s mode w R)

include h

theorem profile (j : Fin J) (r : GroupedProfileReg) :
    R (liveBankProfile j r) = liveDescriptorData p X hG hK active s mode w (liveProfileRole j r) :=
  h.bank _

theorem coordinate (r : SparseCoordinateReg) :
    R (liveBankCoordinate r) = liveDescriptorData p X hG hK active s mode w (liveCoordinateRole r) := h.bank _

theorem zero (r : BinaryZeroReg) :
    R (liveBankZero r) = liveDescriptorData p X hG hK active s mode w (liveZeroRole r) := h.bank _

theorem runs (r : SelectorRunReg) :
    R (liveBankRuns r) = liveDescriptorData p X hG hK active s mode w (liveRunRole r) := h.bank _

theorem mask (j : Fin J) (r : BinaryMaskReg) :
    R (liveBankMask j r) = liveDescriptorData p X hG hK active s mode w (liveMaskRole j r) := h.bank _

theorem profile_archive (j : Fin J) : R (liveBankProfile j .archive) = [] := by rw [h.profile]; rfl

theorem profile_blank (j : Fin J) (r : GroupedProfileReg) (hr : r ∉ groupedProfileLive) :
    R (liveBankProfile j r) = [] := by
  rw [h.profile]
  cases r <;> simp_all [groupedProfileLive, liveProfileRole, liveDescriptorData]

theorem affine_blank (j : Fin J) (r : AffineProfileReg)
    (hs : r ≠ .src) (ha : r ≠ .archive) (hi : r ≠ .index) (hk : r ≠ .stride)
    (ho : r ≠ .offset) (hl : r ≠ .last) (h1 : r ≠ .one) (hd : r ≠ .dst) :
    R (sharedAffineProfile (liveBankProfile j) r) = [] := by
  change R (liveBankProfile j (affineGroupedRole r)) = []
  rw [h.profile]
  cases r <;> simp_all [affineGroupedRole, liveProfileRole, liveDescriptorData]

theorem coordinate_blank (r : SparseCoordinateReg) (hc : r ≠ .cursor) (ho : r ≠ .one) :
    R (liveBankCoordinate r) = [] := by
  rw [h.coordinate]
  cases r <;> simp_all [liveCoordinateRole, liveDescriptorData]

theorem coordinate_cursor : R (liveBankCoordinate .cursor) = binSyms w.coordinateBits 0 := by rw [h.coordinate]; rfl

theorem coordinate_one : R (liveBankCoordinate .one) = binSyms w.coordinateBits 1 := by rw [h.coordinate]; rfl

theorem zero_width : R (liveBankZero .width) = binSyms w.widthBits w.selectorBits := by rw [h.zero]; rfl

theorem zero_blank (r : BinaryZeroReg) (hr : r ≠ .width) : R (liveBankZero r) = [] := by
  rw [h.zero]
  cases r <;> simp_all [liveZeroRole, liveDescriptorData]

theorem runs_blank (r : SelectorRunReg) : R (liveBankRuns r) = [] := by
  rw [h.runs]
  cases r <;> rfl

theorem compiler (j : Fin J) :
    DescriptorCompileReady (liveBankMask j) R w.selectorBits (repairCompactSourceWidth p X (mode j).key + 1) := by
  constructor
  · rw [h.mask]; rfl
  · intro r hr
    rw [h.mask]
    cases r <;> simp_all [liveMaskRole, liveDescriptorData]

theorem profile_saved : R (liveDescriptorAux .profileSaved) = [] := by rw [h.bank]; rfl

theorem coordinate_saved : R (liveDescriptorAux .coordinateSaved) = [] := by rw [h.bank]; rfl

theorem compiler_archive : R (liveDescriptorAux .archive) = [] := by rw [h.bank]; rfl

theorem rows (j : Fin J) :
    R (liveDescriptorAux (.rows j)) = binSyms w.coordinateBits (repairCompactRows p (mode j).key) := by rw [h.bank]; rfl

end LiveDescriptorReady
end
end IntegerMultBounds.MathlibTM2.Routing
