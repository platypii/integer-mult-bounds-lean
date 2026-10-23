module

public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileDescriptor
public import IntegerMultBounds.MathlibTM2.Routing.RepairAffinePattern

/-! Compile each of the nine affine repair descriptors directly from live source
profiles and dimensions. No coordinate stream or descriptor table is supplied;
all generated coordinate, compact and dense intermediates are erased. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {T Q A : ℕ} {P U : Type}

noncomputable section

theorem repairAffineDescriptor_exec (body : P → Pr P T Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (key : RepairDescriptorKey) (hkey : ∀ j, key ≠ some (.A, j))
    (profile : AffineProfileReg → Fin T) (hprofile : Function.Injective profile)
    (profileSaved : Fin T) (hprofileSaved : ∀ r, profileSaved ≠ profile r)
    (coord : SparseCoordinateReg → Fin T) (hcoord : Function.Injective coord)
    (hinput : profile .dst = coord .src)
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
    (Li Lk Ls Lw : ℕ)
    (hk : (repairAffineStride p key) < 2 ^ Lk) (hN : (repairCompactRows p key) < 2 ^ (Li + Lk))
    (hpositive : 0 < (repairCompactRows p key)) (hi : p.n ≤ 2 ^ Li)
    (hW : (repairCompactSourceWidth p X key) + 1 < 2 ^ Ls) (hLs : Ls < 2 ^ Lw)
    (v : HS T Q A U) (S : Stacks T A)
    (hprofileSrc : S.R (profile .src) = affineProfileFrames Ls (affineSourceProfile (repairAffineSources p X hG hK active s key)))
    (hprofileArchive : S.R (profile .archive) = []) (hprofileIndex : S.R (profile .index) = binSyms Li 0)
    (hprofileStride : S.R (profile .stride) = binSyms Lk (repairAffineStride p key))
    (hprofileOffset : S.R (profile .offset) = binSyms (Li + Lk) (repairAffineOffset p key))
    (hprofileLast : S.R (profile .last) = binSyms (Li + Lk) ((repairCompactRows p key) - 1))
    (hprofileOne : S.R (profile .one) = binSyms Ls 1) (hprofileSave : S.R profileSaved = [])
    (hprofileBlank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .index → r ≠ .stride →
      r ≠ .offset → r ≠ .last → r ≠ .one → r ≠ .dst → S.R (profile r) = [])
    (hinputBlank : S.R (coord .src) = [])
    (harchive : S.R (coord .archive) = []) (hcursor : S.R (coord .cursor) = binSyms (Li + Lk) 0)
    (hone : S.R (coord .one) = binSyms (Li + Lk) 1) (hsaved : S.R saved = []) (hcompact : S.R (coord .dst) = [])
    (hcoordBlank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .cursor → r ≠ .one → r ≠ .dst → S.R (coord r) = [])
    (hwidth : S.R (zero .width) = binSyms Lw Ls) (hunary : S.R (zero .unary) = [])
    (hscratch : ∀ i, S.R (zero (.scratch i)) = [])
    (hrArchive : S.R (rg .archive) = []) (hrBlock : S.R (rg .block) = [])
    (hrBlank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .block → r ≠ .dst → S.R (rg r) = [])
    (hselectors : S.R (rg .dst) = []) (hmaskReady : DescriptorCompileReady mask S.R Ls ((repairCompactSourceWidth p X key) + 1))
    (harchiveBlank : S.R archive = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ affineProfileDescriptorCost Li Lk Ls Lw (repairAffineStride p key) (repairAffineOffset p key) (repairCompactRows p key) (repairAffineSources p X hG hK active s key) ∧
      Exec body (affineProfileDescriptorProgram profile profileSaved coord saved zero rg mask archive out)
        (mk v S) steps (mk v' { S with R := Function.update S.R out (repairDescriptorWord p X hG hK active s key ++ S.R out) }) := by
  have ho : repairAffineOffset p key < 2 ^ (Li + Lk) :=
    (repairAffineOffset_le_rows p key).trans_lt hN
  have hp := repairAffinePosition_bound p hG hK key hkey
  obtain ⟨v', steps, hu, ht, he⟩ := affineProfileDescriptor_exec body profile hprofile profileSaved hprofileSaved
    coord hcoord hinput saved hsavedSep zero hzero rg hrg hjoin hblockReg hzeroSep hrunSep hzeroInput hrunInput
    mask hmask archive out hsa hso hao hselectorMask harchiveMask houtMask hmaskInput harchiveInput houtInput
    Li Lk Ls Lw (repairAffineStride p key) (repairAffineOffset p key) (repairCompactRows p key)
    (repairAffineSources p X hG hK active s key) (repairAffineStride_positive p hG hK key) hk hN ho hpositive hi hp hW hLs
    v S hprofileSrc hprofileArchive hprofileIndex hprofileStride hprofileOffset hprofileLast hprofileOne hprofileSave
    hprofileBlank hinputBlank harchive hcursor hone hsaved hcompact hcoordBlank hwidth hunary hscratch
    hrArchive hrBlock hrBlank hselectors hmaskReady harchiveBlank
  rw [repairAffinePattern_word p X hG hK active s key hkey] at he
  exact ⟨v', steps, hu, ht, he⟩

end
end IntegerMultBounds.MathlibTM2.Routing
