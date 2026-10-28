module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRhsSelection
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedCouplingSourceMask

/-! The existing generated boundary-mask format selects the exact ordered RHS in one scan. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem boundaryRhsFlags_halo {s t : ℕ} [NeZero s] (hst : s < t) (band a b : ℕ) (hb : b ≤ s) :
    boundaryRhsFlags s (haloBoundary s t band a b) = (List.range s).map (haloMaskAt true s t band a b) := by
  unfold boundaryRhsFlags physOrder
  rw [List.map_map]
  apply List.map_congr_left
  intro k hk
  have hh := haloMaskAt_spec true hst band a b k hb (List.mem_range.mp hk)
  simp only [Bool.true_eq,↓reduceIte] at hh
  exact Bool.eq_iff_iff.mpr (by simpa using hh.symm)

theorem boundaryRhsMask_flags {s t : ℕ} [NeZero s] (hst : s < t) (hA : 4 ≤ A)
    (band a b : ℕ) (hb : b ≤ s) :
    (couplingSourceMaskSymbols true A s t band a b).map pairRe = boundaryRhsFlags s (haloBoundary s t band a b) := by
  rw [boundaryRhsFlags_halo hst band a b hb]
  simp only [couplingSourceMaskSymbols,List.map_map]
  apply List.map_congr_left
  intro k hk
  simp only [Function.comp_apply]
  cases hf : haloMaskAt true s t band a b k <;> simp [hf,pairRe_pairSym hA]

theorem boundaryRhsHaloGather_exec {src mask width symbols ts tm acc out cs : Fin T}
    (hreg : [src,mask,width,symbols,ts,tm,acc,out].Nodup)
    {s t : ℕ} [NeZero s] (hst : s < t) (hA : 4 ≤ A) (band a b : ℕ) (hb : b ≤ s)
    (C : ZMod s → GaussianInt) (w : ℕ) (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w (chirpLine s C)++tail)
    (hmask : S.R mask = couplingSourceMaskSymbols true A s t band a b) (hw : (S.R width).length = w)
    (hfresh : ∀ k ∈ [symbols,ts,tm,acc], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ s*(16*w+10)+16 ∧
      Exec body (gatherRecords src mask width symbols ts tm acc out cs pairRe) (mk v S) m
        (mk v' {S with R := Function.update S.R out (cstream A w ((bOrder s (haloBoundary s t band a b)).map C)++S.R out)}) := by
  exact boundaryRhsOrderedGather_exec (body := body) hreg s (haloBoundary s t band a b) C w
    (couplingSourceMaskSymbols true A s t band a b) pairRe (boundaryRhsMask_flags hst hA band a b hb)
    tail v S hsrc hmask hw hfresh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
