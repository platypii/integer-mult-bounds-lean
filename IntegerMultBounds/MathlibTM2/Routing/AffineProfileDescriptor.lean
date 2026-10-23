module

public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileClosedGenerate
public import IntegerMultBounds.MathlibTM2.Routing.CoordinateDescriptorCompile

/-! Generate a complete coordinate stream from live affine source profiles,
compile the actual sparse descriptor and erase the generated coordinate stream.
Only descriptor output changes; positions and selector frames are not inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A W m : ℕ} {P U : Type}

def affineProfileDescriptorProgram (profile : AffineProfileReg → Fin T) (profileSaved : Fin T)
    (coord : SparseCoordinateReg → Fin T) (saved : Fin T)
    (zero : BinaryZeroReg → Fin T) (rg : SelectorRunReg → Fin T)
    (mask : BinaryMaskReg → Fin T) (archive out : Fin T) : Pr P T Q A U :=
  .seq (affineProfileClosedProgram profile profileSaved)
    (.seq (coordinateDescriptorProgram coord saved zero rg mask archive out) (bclear (coord .src)))

def affineProfileDescriptorCost (Li Lk Ls Lw k o N : ℕ) (src : Fin m → Option (Fin W)) :=
  let entries := sparseCoordinateClose N (sparsePatternCoordinates (N := N) (fun j => j * k + o) src)
  affineProfileClosedCost Li Lk Ls m +
    (coordinateSelectorCost Lw (Li + Lk) Ls 0 entries +
      (N * (descriptorCompileCallCost Ls (W + 1) + 2) + 2 * (N * (Ls + 1)) + 4) +
      (2 * (N * (Ls + 1)) + 2)) +
    (2 * (entries.length * (Li + Lk + Ls + 2)) + 2)

theorem affineProfileDescriptor_exec (body : P → Pr P T Q A U)
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
    (Li Lk Ls Lw k o N : ℕ) (src : Fin m → Option (Fin W))
    (hkpositive : 0 < k) (hk : k < 2 ^ Lk) (hN : N < 2 ^ (Li + Lk))
    (ho : o < 2 ^ (Li + Lk)) (hpositive : 0 < N) (hi : m ≤ 2 ^ Li)
    (hpos : ∀ j : Fin m, j.val * k + o < N) (hW : W + 1 < 2 ^ Ls) (hLs : Ls < 2 ^ Lw)
    (v : HS T Q A U) (S : Stacks T A)
    (hprofileSrc : S.R (profile .src) = affineProfileFrames Ls (affineSourceProfile src))
    (hprofileArchive : S.R (profile .archive) = []) (hprofileIndex : S.R (profile .index) = binSyms Li 0)
    (hprofileStride : S.R (profile .stride) = binSyms Lk k)
    (hprofileOffset : S.R (profile .offset) = binSyms (Li + Lk) o)
    (hprofileLast : S.R (profile .last) = binSyms (Li + Lk) (N - 1))
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
    (hselectors : S.R (rg .dst) = []) (hmaskReady : DescriptorCompileReady mask S.R Ls (W + 1))
    (harchiveBlank : S.R archive = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ affineProfileDescriptorCost Li Lk Ls Lw k o N src ∧
      Exec body (affineProfileDescriptorProgram profile profileSaved coord saved zero rg mask archive out)
        (mk v S) steps (mk v' { S with R := Function.update S.R out ((patternTable (sparsePattern (L := N) (fun j => j * k + o) src)).flatten.map
            (bitSymbol (a := A)) ++ S.R out) }) := by
  let entries := sparseCoordinateClose N (sparsePatternCoordinates (N := N) (fun j => j * k + o) src)
  let input := sparseCoordinateFrames (A := A) (Li + Lk) Ls (sparseCoordinateValues entries)
  let qs := List.ofFn (patternIndex (sparsePattern (L := N) (fun j => j * k + o) src))
  have hmono : StrictMono (fun j : ℕ => j * k + o) := by
    intro a b hab
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right hab hkpositive) o
  have hbound : ∀ j < m, j * k + o < N := fun j hj => hpos ⟨j, hj⟩
  have hr := sparseCoordinateClose_ready (Li + Lk) N hpositive hN _
    (sparsePatternCoordinates_ordered _ hmono src hbound) (sparsePatternCoordinates_bound _ src hbound)
  have hindices := sparsePatternComplete_indices (Li + Lk) hpositive hN _ hmono src hbound
  obtain ⟨v₁, n₁, hu₁, ht₁, he₁⟩ := affineProfileClosed_exec body profile hprofile profileSaved hprofileSaved
    Li Lk Ls k o N src hk hN ho hpositive hi hpos hW v S hprofileSrc hprofileArchive hprofileIndex
    hprofileStride hprofileOffset hprofileLast hprofileOne hprofileSave hprofileBlank
  rw [hinput, hinputBlank, List.append_nil] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R (coord .src) input }
  have hkeep (j : Fin T) (hj : j ≠ coord .src) : S₁.R j = S.R j := Function.update_of_ne hj _ _
  have hm : DescriptorCompileReady mask S₁.R Ls (W + 1) := by
    constructor
    · exact (hkeep _ (hmaskInput .width)).trans hmaskReady.width
    · intro r hr; exact (hkeep _ (hmaskInput r)).trans (hmaskReady.blank r hr)
  obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := coordinateDescriptor_exec body coord hcoord saved hsavedSep zero hzero rg hrg
    hjoin hblockReg hzeroSep hrunSep Lw (Li + Lk) Ls 0 hLs entries hr v₁ S₁
    (by simp [S₁, input])
    ((hkeep _ (hcoord.ne (by decide))).trans harchive) ((hkeep _ (hcoord.ne (by decide))).trans hcursor)
    ((hkeep _ (hcoord.ne (by decide))).trans hone) ((hkeep _ (hsavedSep .src)).trans hsaved)
    ((hkeep _ (hcoord.ne (by decide))).trans hcompact)
    (by intro r hs ha hc ho hd; rw [hkeep _ (hcoord.ne hs)]; exact hcoordBlank r hs ha hc ho hd)
    ((hkeep _ (hzeroInput .width)).trans hwidth) ((hkeep _ (hzeroInput .unary)).trans hunary)
    (fun i => (hkeep _ (hzeroInput (.scratch i))).trans (hscratch i))
    ((hkeep _ (hrunInput .archive)).trans hrArchive) ((hkeep _ (hrunInput .block)).trans hrBlock)
    (by intro r hs ha hb hd; rw [hkeep _ (hrunInput r)]; exact hrBlank r hs ha hb hd)
    mask hmask archive out hsa hso hao hselectorMask harchiveMask houtMask qs hindices hW
    ((hkeep _ (hrunInput .dst)).trans hselectors) hm ((hkeep _ harchiveInput).trans harchiveBlank)
  rw [hkeep _ houtInput] at he₂
  let word := (sourceTable qs).flatten.map (bitSymbol (a := A)) ++ S.R out
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R out word }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (coord .src) v₂ S₂
  have hs : S₂.R (coord .src) = input := by simp [S₂, S₁, houtInput.symm]
  have hf : Function.update S₂.R (coord .src) [] = Function.update S.R out word := by
    funext j
    by_cases hj : j = coord .src
    · subst j; simp [houtInput.symm, hinputBlank]
    · by_cases ho : j = out
      · subst j; simp [S₂, S₁, hj]
      · simp [S₂, S₁, hj, ho]
  rw [hf, hs] at he₃
  have hl : input.length = entries.length * (Li + Lk + Ls + 2) := by
    simp only [input, sparseCoordinateFrames_length, sparseCoordinateValues, List.length_map]
  rw [hl] at he₃
  have hq : qs.length = N := by simp [qs]
  rw [hq] at ht₂
  refine ⟨v₃, n₁ + (n₂ + (2 * (entries.length * (Li + Lk + Ls + 2)) + 2)),
    hu₃.trans (hu₂.trans hu₁), by dsimp only [affineProfileDescriptorCost, entries] at ht₂ ⊢; omega, ?_⟩
  exact Exec.seq he₁ (Exec.seq he₂ he₃)

end IntegerMultBounds.MathlibTM2.Routing
