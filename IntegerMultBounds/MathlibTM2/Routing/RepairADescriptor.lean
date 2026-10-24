module

public import IntegerMultBounds.MathlibTM2.Routing.RepairAProfileGenerate
public import IntegerMultBounds.MathlibTM2.Routing.RepairCoordinateDescriptor

/-! Compile both actual temporary-bit A descriptors from live grouped profiles.
Generated coordinates, compact runs and dense selector streams are all erased;
only the required descriptor output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def repairADescriptorProgram (profile : GroupedProfileReg → Fin T) (profileSaved : Fin T)
    (coord : SparseCoordinateReg → Fin T) (saved : Fin T)
    (zero : BinaryZeroReg → Fin T) (rg : SelectorRunReg → Fin T)
    (mask : BinaryMaskReg → Fin T) (archive out : Fin T) : Pr P T Q A U :=
  .seq (groupedProfileTerminalProgram profile profileSaved)
    (.seq (coordinateDescriptorProgram coord saved zero rg mask archive out) (bclear (coord .src)))

noncomputable section

open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

def repairADescriptorCost (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (j : Fin 2) (Li Lg Lk Ls Lw : ℕ) :=
  let key := some (Off.A, j)
  let entries := repairDescriptorCoordinates p X hG hK active s key
  ((22 * (Li + Lk) + 12 * Ls + 37) +
    (p.n * p.G * (groupedProfileCallCost Li Lg Lk Ls + 2) + 2 * (p.n * p.G * (Ls + 3)) + 16 * Li + 20)) +
    (coordinateSelectorCost Lw (Li + Lk) Ls 0 entries +
      (repairCompactRows p key * (descriptorCompileCallCost Ls (repairCompactSourceWidth p X key + 1) + 2) +
        2 * (repairCompactRows p key * (Ls + 1)) + 4) + (2 * (repairCompactRows p key * (Ls + 1)) + 2)) +
    (2 * (entries.length * (Li + Lk + Ls + 2)) + 2)

def groupedProfileDescriptorBound (Li Lg Lk Ls Lw m N W : ℕ) :=
  ((22 * (Li + Lk) + 12 * Ls + 37) +
    (m * (groupedProfileCallCost Li Lg Lk Ls + 2) +
      2 * (m * (Ls + 3)) + 16 * Li + 20)) +
    ((m + 1) * (55 * (Li + Lk) + 30 * Ls + 105) +
      N * (4 * (Li + Lk) + 6 * Ls + 21) +
      Lw * (4 * Ls + 11) + 16 * (Li + Lk) + 10 * Ls + 43 +
      (N * (descriptorCompileCallCost Ls (W + 1) + 2) +
        2 * (N * (Ls + 1)) + 4) + (2 * (N * (Ls + 1)) + 2)) +
    (2 * ((m + 1) * (Li + Lk + Ls + 2)) + 2)

def repairADescriptorBound (p : Par) (X Li Lg Lk Ls Lw : ℕ) :=
  groupedProfileDescriptorBound Li Lg Lk Ls Lw (p.n * p.G) p.wy (selectiveSourceWidth p X .A)

theorem groupedProfileDescriptorBound_mono (Li Lg Lk Ls Lw : ℕ)
    {m m' N N' W W' : ℕ} (hm : m ≤ m') (hN : N ≤ N') (hW : W ≤ W') :
    groupedProfileDescriptorBound Li Lg Lk Ls Lw m N W ≤
      groupedProfileDescriptorBound Li Lg Lk Ls Lw m' N' W' := by
  unfold groupedProfileDescriptorBound descriptorCompileCallCost
  gcongr

theorem groupedProfileDescriptorBound_widths_mono
    {Li Li' Lg Lg' Lk Lk' Ls Ls' Lw Lw' : ℕ}
    (hi : Li ≤ Li') (hg : Lg ≤ Lg') (hk : Lk ≤ Lk') (hs : Ls ≤ Ls') (hw : Lw ≤ Lw')
    (m N W : ℕ) :
    groupedProfileDescriptorBound Li Lg Lk Ls Lw m N W ≤
      groupedProfileDescriptorBound Li' Lg' Lk' Ls' Lw' m N W := by
  unfold groupedProfileDescriptorBound groupedProfileCallCost binaryGroupedPositionCost
    descriptorCompileCallCost
  gcongr

theorem repairADescriptorCost_le (p : Par) (X : ℕ)
    (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (j : Fin 2)
    (Li Lg Lk Ls Lw : ℕ) (hrows : 0 < p.wy) (hfit : p.wy < 2 ^ (Li + Lk)) :
    repairADescriptorCost p X hG hK active s j Li Lg Lk Ls Lw ≤
      repairADescriptorBound p X Li Lg Lk Ls Lw := by
  have hs := repairCoordinateSelectorCost_le p X hG hK hGK active s
    (some (.A, j)) Lw (Li + Lk) Ls hrows hfit
  have hl := repairDescriptorCoordinates_length p X hG hK active s (some (.A, j))
  dsimp only [repairDescriptorCoordinateSlots, repairRotationSlots, repairCompactRows,
    selectiveTargetWidth] at hs hl
  have hd := Nat.mul_le_mul_right (Li + Lk + Ls + 2) hl
  unfold repairADescriptorCost repairADescriptorBound groupedProfileDescriptorBound
  dsimp only [repairCompactRows, repairCompactSourceWidth, selectiveTargetWidth] at hs hd ⊢
  omega

theorem repairADescriptorCost_le_all (p : Par) (X : ℕ)
    (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (j : Fin 2)
    (Li Lg Lk Ls Lw : ℕ) (hfit : p.wy < 2 ^ (Li + Lk)) :
    repairADescriptorCost p X hG hK active s j Li Lg Lk Ls Lw ≤
      repairADescriptorBound p X Li Lg Lk Ls Lw := by
  by_cases hrows : 0 < p.wy
  · exact repairADescriptorCost_le p X hG hK hGK active s j Li Lg Lk Ls Lw hrows hfit
  · have hzero : p.wy = 0 := by omega
    have hn : p.n = 0 := by
      have hz : p.n * p.K = 0 := by unfold Par.wy at hzero; omega
      exact (Nat.mul_eq_zero.mp hz).resolve_right (by omega)
    simp [repairADescriptorCost, repairADescriptorBound, groupedProfileDescriptorBound,
      repairDescriptorCoordinates, repairRotationCoordinates, sparsePatternCoordinates,
      repairRotationSlots, repairCompactRows, repairCompactSourceWidth, selectiveTargetWidth,
      hn, hzero, sparseCoordinateClose, coordinateSelectorCost_eq, sparseCoordinateRuns]

theorem repairADescriptor_exec (body : P → Pr P T Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (j : Fin 2)
    (profile : GroupedProfileReg → Fin T) (hprofile : Function.Injective profile)
    (profileSaved : Fin T) (hprofileSaved : ∀ r, profileSaved ≠ profile r)
    (coord : SparseCoordinateReg → Fin T) (hcoord : Function.Injective coord)
    (hinput : profile (.coordinate .dst) = coord .src)
    (saved : Fin T) (hsavedSep : ∀ r, saved ≠ coord r)
    (zero : BinaryZeroReg → Fin T) (hzero : Function.Injective zero)
    (rg : SelectorRunReg → Fin T) (hrg : Function.Injective rg)
    (hjoin : rg .src = coord .dst) (hblockReg : zero .dst = rg .block)
    (hzeroSep : ∀ r, zero r ≠ coord .dst) (hrunSep : ∀ r, r ≠ .src → rg r ≠ coord .dst)
    (hzeroInput : ∀ r, zero r ≠ coord .src) (hrunInput : ∀ r, rg r ≠ coord .src)
    (mask : BinaryMaskReg → Fin T) (hmask : Function.Injective mask) (archive out : Fin T)
    (hsa : rg .dst ≠ archive) (hso : rg .dst ≠ out) (hao : archive ≠ out)
    (hselectorMask : ∀ r, rg .dst ≠ mask r) (harchiveMask : ∀ r, archive ≠ mask r) (houtMask : ∀ r, out ≠ mask r)
    (hmaskInput : ∀ r, mask r ≠ coord .src) (harchiveInput : archive ≠ coord .src) (houtInput : out ≠ coord .src)
    (Li Lg Lk Ls Lw : ℕ) (hg : p.G < 2 ^ Lg) (hk : p.K < 2 ^ Lk) (hwidths : Lg ≤ Li + Lk)
    (hN : p.wy < 2 ^ (Li + Lk)) (hpositive : 0 < p.wy) (hi : p.n * p.G ≤ 2 ^ Li)
    (hW : selectiveSourceWidth p X .A + 1 < 2 ^ Ls) (hLs : Ls < 2 ^ Lw)
    (v : HS T Q A U) (S : Stacks T A)
    (hprofileSrc : S.R (profile .src) = affineProfileFrames Ls (affineSourceProfile (repairRotationSources p X hG hK active s .A j)))
    (hprofileArchive : S.R (profile .archive) = []) (hprofileIndex : S.R (profile (.coordinate (.arithmetic .index))) = binSyms Li 0)
    (hprofileGroup : S.R (profile (.coordinate (.arithmetic .group))) = binSyms Lg p.G)
    (hprofileStride : S.R (profile (.coordinate (.arithmetic .stride))) = binSyms Lk p.K)
    (hprofileOffset : S.R (profile (.coordinate (.arithmetic .base))) = binSyms (Li + Lk) (p.ρ + 1))
    (hprofileLast : S.R (profile (.coordinate .last)) = binSyms (Li + Lk) (p.wy - 1))
    (hprofileOne : S.R (profile (.coordinate .one)) = binSyms Ls 1) (hprofileSave : S.R profileSaved = [])
    (hprofileBlank : ∀ r, r ∉ groupedProfileLive → S.R (profile r) = [])
    (hinputBlank : S.R (coord .src) = [])
    (harchive : S.R (coord .archive) = []) (hcursor : S.R (coord .cursor) = binSyms (Li + Lk) 0)
    (hone : S.R (coord .one) = binSyms (Li + Lk) 1) (hsaved : S.R saved = []) (hcompact : S.R (coord .dst) = [])
    (hcoordBlank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .cursor → r ≠ .one → r ≠ .dst → S.R (coord r) = [])
    (hwidth : S.R (zero .width) = binSyms Lw Ls) (hunary : S.R (zero .unary) = [])
    (hscratch : ∀ i, S.R (zero (.scratch i)) = [])
    (hrArchive : S.R (rg .archive) = []) (hrBlock : S.R (rg .block) = [])
    (hrBlank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .block → r ≠ .dst → S.R (rg r) = [])
    (hselectors : S.R (rg .dst) = []) (hmaskReady : DescriptorCompileReady mask S.R Ls (selectiveSourceWidth p X .A + 1))
    (harchiveBlank : S.R archive = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ repairADescriptorCost p X hG hK active s j Li Lg Lk Ls Lw ∧
      Exec body (repairADescriptorProgram profile profileSaved coord saved zero rg mask archive out)
        (mk v S) steps (mk v' { S with R := Function.update S.R out (repairDescriptorWord p X hG hK active s (some (.A, j)) ++ S.R out) }) := by
  let key := some (Off.A, j)
  let entries := repairDescriptorCoordinates p X hG hK active s key
  let input := sparseCoordinateFrames (A := A) (Li + Lk) Ls (sparseCoordinateValues entries)
  obtain ⟨v₁, n₁, hu₁, ht₁, he₁⟩ := repairAProfileGenerate_exec body p X hG hK hGK active s j
    profile hprofile profileSaved hprofileSaved Li Lg Lk Ls hg hk hwidths hN hpositive hi hW v S
    hprofileSrc hprofileArchive hprofileIndex hprofileGroup hprofileStride hprofileOffset hprofileLast hprofileOne hprofileSave hprofileBlank
  rw [hinput, hinputBlank, List.append_nil] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R (coord .src) input }
  have hkeep (r : Fin T) (hr : r ≠ coord .src) : S₁.R r = S.R r := Function.update_of_ne hr _ _
  have hm : DescriptorCompileReady mask S₁.R Ls (selectiveSourceWidth p X .A + 1) := by
    constructor
    · exact (hkeep _ (hmaskInput .width)).trans hmaskReady.width
    · intro r hr; exact (hkeep _ (hmaskInput r)).trans (hmaskReady.blank r hr)
  obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := repairCoordinateDescriptor_exec body p X hG hK hGK active s key
    coord hcoord saved hsavedSep zero hzero rg hrg hjoin hblockReg hzeroSep hrunSep
    Lw (Li + Lk) Ls hLs hpositive hN v₁ S₁ (by simp [S₁, input, entries])
    ((hkeep _ (hcoord.ne (by decide))).trans harchive) ((hkeep _ (hcoord.ne (by decide))).trans hcursor)
    ((hkeep _ (hcoord.ne (by decide))).trans hone) ((hkeep _ (hsavedSep .src)).trans hsaved)
    ((hkeep _ (hcoord.ne (by decide))).trans hcompact)
    (by intro r hs ha hc ho hd; rw [hkeep _ (hcoord.ne hs)]; exact hcoordBlank r hs ha hc ho hd)
    ((hkeep _ (hzeroInput .width)).trans hwidth) ((hkeep _ (hzeroInput .unary)).trans hunary)
    (fun i => (hkeep _ (hzeroInput (.scratch i))).trans (hscratch i))
    ((hkeep _ (hrunInput .archive)).trans hrArchive) ((hkeep _ (hrunInput .block)).trans hrBlock)
    (by intro r hs ha hb hd; rw [hkeep _ (hrunInput r)]; exact hrBlank r hs ha hb hd)
    mask hmask archive out hsa hso hao hselectorMask harchiveMask houtMask hW
    ((hkeep _ (hrunInput .dst)).trans hselectors) hm ((hkeep _ harchiveInput).trans harchiveBlank)
  rw [hkeep _ houtInput] at he₂
  let word := repairDescriptorWord p X hG hK active s key ++ S.R out
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R out word }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (coord .src) v₂ S₂
  have hs : S₂.R (coord .src) = input := by simp [S₂, S₁, houtInput.symm]
  have hf : Function.update S₂.R (coord .src) [] = Function.update S.R out word := by
    funext r
    by_cases hr : r = coord .src
    · subst r; simp [houtInput.symm, hinputBlank]
    · by_cases ho : r = out
      · subst r; simp [S₂, S₁, hr]
      · simp [S₂, S₁, hr, ho]
  rw [hf, hs] at he₃
  have hl : input.length = entries.length * (Li + Lk + Ls + 2) := by
    simp only [input, sparseCoordinateFrames_length, sparseCoordinateValues, List.length_map]
  rw [hl] at he₃
  refine ⟨v₃, n₁ + (n₂ + (2 * (entries.length * (Li + Lk + Ls + 2)) + 2)),
    hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  dsimp only [repairADescriptorCost, entries, key] at ht₂ ⊢
  omega

end
end IntegerMultBounds.MathlibTM2.Routing
