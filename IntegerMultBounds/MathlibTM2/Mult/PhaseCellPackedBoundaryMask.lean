module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySelection
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingSourceIntervalMaskHost

/-! The generated local halo mask is exactly the selector of the packed RHS. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem packedBoundaryRhsMask_flags {A s t origin N : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a b : ℕ) (hb : b ≤ s) (hfit : origin+N ≤ s) :
    (couplingSourceIntervalMaskSymbols true A s t band a b origin N).map pairRe =
      packedBoundaryRhsFlags origin N (haloBoundary s t band a b) := by
  apply List.ext_getElem (by simp only [List.length_map,couplingSourceIntervalMaskSymbols_length,
    packedBoundaryRhsFlags_length _ hfit])
  intro j hj hk
  have hjN : j < N := by simpa only [List.length_map,couplingSourceIntervalMaskSymbols_length] using hj
  have hh := haloMaskAt_spec true hst band a b (origin+j) hb (by omega)
  simp only [↓reduceIte] at hh
  simp only [couplingSourceIntervalMaskSymbols,packedBoundaryRhsFlags,physOrder,
    List.getElem_map,List.getElem_take,List.getElem_drop,List.getElem_range,pairRe_pairSym hA]
  exact Bool.eq_iff_iff.mpr (by simpa using hh)

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem packedBoundaryRhsHaloGather_exec {src mask width symbols ts tm acc out cs : Fin T}
    (hreg : [src,mask,width,symbols,ts,tm,acc,out].Nodup)
    {s t origin N : ℕ} [NeZero s] (hst : s < t) (hA : 4 ≤ A) (band a b : ℕ)
    (hb : b ≤ s) (hfit : origin+N ≤ s)
    (hB : ∀ i ∈ haloBoundary s t band a b, origin ≤ i.val ∧ i.val < origin+N)
    (C : ZMod s → GaussianInt) (w : ℕ) (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w (packedInterval origin N C)++tail)
    (hmask : S.R mask = couplingSourceIntervalMaskSymbols true A s t band a b origin N)
    (hw : (S.R width).length = w) (hfresh : ∀ k ∈ [symbols,ts,tm,acc], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ N*(16*w+10)+16 ∧
      Exec body (gatherRecords src mask width symbols ts tm acc out cs pairRe) (mk v S) m
        (mk v' {S with R := (Function.update S.R out
          (cstream A w ((bOrder s (haloBoundary s t band a b)).map C)++S.R out))}) := by
  exact packedBoundaryRhsOrderedGather_exec (body := body) hreg s origin N
    (haloBoundary s t band a b) C w hfit hB _ pairRe
    (packedBoundaryRhsMask_flags hst hA band a b hb hfit) tail v S hsrc hmask hw hfresh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
