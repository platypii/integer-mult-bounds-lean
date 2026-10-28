module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedRawCallerCompiled
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawCallerInitialStock

/-! Match the raw ABI's initial stock to the complete compiled resource bound. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

/-- Borrowed tails and the native/left frame stay explicit. Every other initial
register and all transient work fit in a uniform two-box-volume allowance. -/
theorem selectedFamilyInverseCaller_framed_compiled_volume_le
    {Q A : ℕ} {P U : Type} [Fintype P]
    (body : P → Pr P 303 Q A U) (main : P) (ct : ℕ) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (hmain : body main = familyInverseCaller recovery hR hQ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let W := inverseCallerWordWidth p u l target s t
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
        (haloBoundary s t (PhaseCellBand.width p u) 0 s).card
      let w := executionWidth p l (initialSchurTarget p u bits 2) 2
      ∀ (v : HS 303 Q A U) (S : Stacks 303 A)
        (R : Store (HΓ (T := 303) A) (HS 303 Q A U)) (steps : ℕ)
        (F : ZMod s → GaussianInt) (tail wl : List (Fin (A+4))),
      wl.length = W →
      tblHolds familyInverseScalarReg S (tblRho W wl [] (inverseInputScalars p u l target s t 0 s)) →
      (∀ j, j ≠ 110 → j ≠ 132 → S.R (familyInverseCoreReg j) = []) →
      S.R 110 = cstream A w (chirpLine s F)++tail →
      (∀ C, mnProgPush (familyInverseCaller (P := P) (U := U) (A := A) recovery hR hQ) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*familyInverseCallerStockCost A W p u l target s t)
          depth (familyInverseCaller recovery hR hQ) (mk v S) steps R) →
      ReachWithin (mcode body main) (fun c => compiledSize body c ≤
        hostFrameStock S+303*(tail.length+(S.R 132).length)+1+2*Sizes.T n)
        (cfg (some .entry) (mk v S) none []) (steps+2) (cfg none R none []) := by
  filter_upwards [selectedFamilyInverseCaller_compiled_volume_le body main ct recovery hR hQ hmain,
    selectedFamilyInverseCallerStock_scaled_volume_le ct 303] with n hn hc
  intro h i _ u target hu htarget hband
  dsimp only
  intro v S R steps F tail wl hwl hscalar hblank hsource htrace
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let W := inverseCallerWordWidth p u l target s t
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
    (haloBoundary s t (PhaseCellBand.width p u) 0 s).card
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  have hi : mnSize (mk v S) ≤ hostFrameStock S+303*(tail.length+(S.R 132).length)+303*(s*w+W) :=
    familyInverseCaller_initial_stock_le v S F tail wl hwl hscalar hblank hsource
  have hdata : 303*(s*w+W) ≤ Sizes.T n :=
    (Nat.mul_le_mul_left 303 (familyInverseCallerStockCost_input_le A W p u l target s t)).trans
      (hc h i A u target hu htarget hband)
  have hstock : mnSize (mk v S) ≤ hostFrameStock S+303*(tail.length+(S.R 132).length)+Sizes.T n :=
    hi.trans (Nat.add_le_add_left hdata _)
  have hr := hn h i u target hu htarget hband (mk v S) R steps htrace
  apply hr.mono
  intro c hbound
  omega

end IntegerMultBounds.MathlibTM2.Cost
