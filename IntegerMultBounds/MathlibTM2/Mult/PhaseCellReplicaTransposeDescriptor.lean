module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaTransposeProfile
public import IntegerMultBounds.MathlibTM2.Routing.GroupedProfileDescriptor

/-! Compile a terminal-complete replica transpose descriptor from its live source
profile. Absolute positions and every intermediate selector stream are derived. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Routing
variable {T Q A M B W C : ℕ} {P U : Type}

theorem replicaTransposeDescriptor_exec (body : P → Pr P T Q A U)
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
    (Li Lg Lk Ls Lw : ℕ) (replica : Fin B) (src : Fin (M*W) → Option (Fin C))
    (hg : W < 2^Lg) (hWpos : 0 < W) (hk : (B*W) < 2 ^ Lk) (hgroupWidth : Lg ≤ Li+Lk)
    (hN : ((M*B)*W) < 2 ^ (Li + Lk))
    (hM : 0 < M) (hi : (M*W) ≤ 2 ^ Li)
    (hchoices : C + 1 < 2 ^ Ls) (hLs : Ls < 2 ^ Lw)
    (v : HS T Q A U) (S : Stacks T A)
    (hprofileSrc : S.R (profile .src) = affineProfileFrames Ls (affineSourceProfile src))
    (hprofileArchive : S.R (profile .archive) = []) (hprofileIndex : S.R (profile (.coordinate (.arithmetic .index))) = binSyms Li 0)
    (hprofileGroup : S.R (profile (.coordinate (.arithmetic .group))) = binSyms Lg W)
    (hprofileStride : S.R (profile (.coordinate (.arithmetic .stride))) = binSyms Lk (B*W))
    (hprofileOffset : S.R (profile (.coordinate (.arithmetic .base))) = binSyms (Li + Lk) (replica.val*W))
    (hprofileLast : S.R (profile (.coordinate .last)) = binSyms (Li + Lk) (((M*B)*W) - 1))
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
    (hselectors : S.R (rg .dst) = []) (hmaskReady : DescriptorCompileReady mask S.R Ls (C + 1))
    (harchiveBlank : S.R archive = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ groupedProfileDescriptorCost Li Lg Lk Ls Lw W (B*W) (replica.val*W) ((M*B)*W) src ∧
      Exec body (groupedProfileDescriptorProgram profile profileSaved coord saved zero rg mask archive out)
        (mk v S) steps (mk v' { S with R := Function.update S.R out ((patternTable (sparsePattern (L := ((M*B)*W)) (fun j => j / W * (B*W) + (j % W + (replica.val*W))) src)).flatten.map
            (bitSymbol (a := A)) ++ S.R out) }) := by
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) replica.isLt
  have hpositive : 0 < (M*B)*W := Nat.mul_pos (Nat.mul_pos hM hB) hWpos
  have hbaseFit : replica.val*W < 2^(Li+Lk) := by
    have hr := Nat.mul_lt_mul_of_pos_right replica.isLt hWpos
    have hm := Nat.mul_le_mul_right (B*W) (show 1 ≤ M by omega)
    simp only [Nat.one_mul,←Nat.mul_assoc] at hm
    omega
  exact groupedProfileDescriptor_exec body profile hprofile profileSaved hprofileSaved
    coord hcoord hinput saved hsavedSep zero hzero rg hrg hjoin hblockReg hzeroSep hrunSep
    hzeroInput hrunInput mask hmask archive out hsa hso hao hselectorMask harchiveMask houtMask
    hmaskInput harchiveInput houtInput Li Lg Lk Ls Lw W (B*W) (replica.val*W) ((M*B)*W) src
    hg hWpos hk hgroupWidth (replicaProfilePosition_strictMono hB hWpos replica.val)
    hN hbaseFit hpositive hi (fun j => replicaProfilePosition_lt replica j) hchoices hLs
    v S hprofileSrc hprofileArchive hprofileIndex hprofileGroup hprofileStride hprofileOffset
    hprofileLast hprofileOne hprofileSave hprofileBlank hinputBlank harchive hcursor hone hsaved hcompact
    hcoordBlank hwidth hunary hscratch hrArchive hrBlock hrBlank hselectors hmaskReady harchiveBlank

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
