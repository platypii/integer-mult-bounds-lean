module

public import IntegerMultBounds.MathlibTM2.Routing.CoordinateDescriptorCompile
public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorCoordinates

/-! Execute coordinate compilation for every actual repair descriptor. Ordered
coordinates and the exact descriptor word are derived from the repair profile;
coordinate input generation remains a separate obligation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

noncomputable section

theorem repairCoordinateSelectorCost_le
    (p : IntegerMultBounds.MathlibTM2.Layer.CompactGadget.Par) (X : ℕ)
    (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (key : RepairDescriptorKey) (Lw L Ls : ℕ)
    (hrows : 0 < repairCompactRows p key) (hfit : repairCompactRows p key < 2 ^ L) :
    coordinateSelectorCost Lw L Ls 0 (repairDescriptorCoordinates p X hG hK active s key) ≤
      (repairDescriptorCoordinateSlots p key + 1) * (55 * L + 30 * Ls + 105) +
        repairCompactRows p key * (4 * L + 6 * Ls + 21) +
        Lw * (4 * Ls + 11) + 16 * L + 10 * Ls + 43 := by
  have hr := repairDescriptorCoordinates_ready p X hG hK active s hGK key L hrows hfit
  have hd := repairDescriptorCoordinates_dense_length p X hG hK active s hGK key L hrows hfit
  have he := sparseCoordinateRuns_coverage L 0
    (repairDescriptorCoordinates p X hG hK active s key) hr
  rw [hd] at he
  have hs := coordinateSelectorCost_le Lw L Ls 0 (repairCompactRows p key)
    (repairDescriptorCoordinates p X hG hK active s key) hr (by omega)
  have hl := Nat.mul_le_mul_right (55 * L + 30 * Ls + 105)
    (repairDescriptorCoordinates_length p X hG hK active s key)
  omega

theorem repairCoordinateDescriptor_exec (body : P → Pr P T Q A U)
    (p : IntegerMultBounds.MathlibTM2.Layer.CompactGadget.Par) (X : ℕ)
    (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (key : RepairDescriptorKey)
    (coord : SparseCoordinateReg → Fin T) (hcoord : Function.Injective coord)
    (saved : Fin T) (hsavedSep : ∀ r, saved ≠ coord r)
    (zero : BinaryZeroReg → Fin T) (hzero : Function.Injective zero)
    (rg : SelectorRunReg → Fin T) (hrg : Function.Injective rg)
    (hjoin : rg .src = coord .dst) (hblockReg : zero .dst = rg .block)
    (hzeroSep : ∀ r, zero r ≠ coord .dst)
    (hrunSep : ∀ r, r ≠ .src → rg r ≠ coord .dst)
    (Lw L Ls : ℕ) (hLs : Ls < 2 ^ Lw)
    (hrows : 0 < repairCompactRows p key) (hfit : repairCompactRows p key < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (coord .src) = sparseCoordinateFrames L Ls (sparseCoordinateValues (repairDescriptorCoordinates p X hG hK active s key)))
    (harchive : S.R (coord .archive) = []) (hcursor : S.R (coord .cursor) = binSyms L 0)
    (hone : S.R (coord .one) = binSyms L 1) (hsaved : S.R saved = []) (hcompact : S.R (coord .dst) = [])
    (hcoordBlank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .cursor → r ≠ .one → r ≠ .dst → S.R (coord r) = [])
    (hwidth : S.R (zero .width) = binSyms Lw Ls) (hunary : S.R (zero .unary) = [])
    (hscratch : ∀ i, S.R (zero (.scratch i)) = [])
    (hrArchive : S.R (rg .archive) = []) (hrBlock : S.R (rg .block) = [])
    (hrBlank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .block → r ≠ .dst → S.R (rg r) = [])
    (mask : BinaryMaskReg → Fin T) (hmask : Function.Injective mask) (archive out : Fin T)
    (hsa : rg .dst ≠ archive) (hso : rg .dst ≠ out) (hao : archive ≠ out)
    (hselectorMask : ∀ r, rg .dst ≠ mask r) (harchiveMask : ∀ r, archive ≠ mask r) (houtMask : ∀ r, out ≠ mask r)
    (hW : repairCompactSourceWidth p X key + 1 < 2 ^ Ls) (hselectors : S.R (rg .dst) = [])
    (hmaskReady : DescriptorCompileReady mask S.R Ls (repairCompactSourceWidth p X key + 1)) (harchiveBlank : S.R archive = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ coordinateSelectorCost Lw L Ls 0 (repairDescriptorCoordinates p X hG hK active s key) +
        (repairCompactRows p key * (descriptorCompileCallCost Ls (repairCompactSourceWidth p X key + 1) + 2) + 2 * (repairCompactRows p key * (Ls + 1)) + 4) +
        (2 * (repairCompactRows p key * (Ls + 1)) + 2) ∧
      Exec body (coordinateDescriptorProgram coord saved zero rg mask archive out) (mk v S) steps
        (mk v' { S with R := Function.update S.R out (repairDescriptorWord p X hG hK active s key ++ S.R out) }) := by
  let entries := repairDescriptorCoordinates p X hG hK active s key
  let qs := (SparseSelectorRun.expand (sparseCoordinateRuns 0 entries)).reverse
  have hready := repairDescriptorCoordinates_ready p X hG hK active s hGK key L hrows hfit
  obtain ⟨v', steps, hu, ht, he⟩ := coordinateDescriptor_exec body coord hcoord saved hsavedSep zero hzero rg hrg
    hjoin hblockReg hzeroSep hrunSep Lw L Ls 0 hLs entries hready v S hsrc harchive hcursor hone hsaved hcompact
    hcoordBlank hwidth hunary hscratch hrArchive hrBlock hrBlank mask hmask archive out hsa hso hao
    hselectorMask harchiveMask houtMask qs (by simp only [qs, List.reverse_reverse]) hW hselectors hmaskReady harchiveBlank
  have hw := repairDescriptorCoordinates_indices (A := A) p X hG hK active s hGK key L hrows hfit
  change (sourceTable qs).flatten.map (IntegerMultBounds.bitSymbol (a := A)) = _ at hw
  rw [hw] at he
  have hl : qs.length = repairCompactRows p key := by
    simpa only [qs, List.length_reverse] using
      repairDescriptorCoordinates_dense_length p X hG hK active s hGK key L hrows hfit
  rw [hl] at ht
  exact ⟨v', steps, hu, ht, he⟩

end
end IntegerMultBounds.MathlibTM2.Routing
