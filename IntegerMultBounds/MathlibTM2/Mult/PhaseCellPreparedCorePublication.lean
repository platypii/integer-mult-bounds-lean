module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPackedSlice
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublication

/-! Publish an owned core with generated symbol controls and an error guarantee
on the actual destination words. Counts and every scratch stack are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem preparedCorePublication_exec {s : ℕ} [NeZero s]
    (offsetRows rows wordWidth src dst skip count savedSkip saved trash tmp : Fin T)
    (hreg : [offsetRows,rows,wordWidth,src,dst,skip,count,savedSkip,saved,trash,tmp].Nodup)
    (q w width k radius : ℕ) (F : ZMod s → GaussianInt) (x : ZMod s → ℝ) (ε : ℝ)
    (hleft : radius ≤ coreStart width k)
    (hright : coreStart width k+coreLength s width k+radius ≤ s)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hoffset : (S.R offsetRows).length = radius)
    (hrows : (S.R rows).length = coreLength s width k) (hwidth : (S.R wordWidth).length = w)
    (hsrc : S.R src = cstream A w
      (packedInterval (coreStart width k-radius) (coreLength s width k+2*radius) F)++tail)
    (hfresh : ∀ i ∈ [skip,count,savedSkip,saved,trash,tmp], S.R i = [])
    (herror : PhaseCellInterface.ErrorOn
      (haloVertices s (coreStart width k-radius) (coreStart width k+coreLength s width k+radius))
      (fun i => (packedIntervalRead q w (coreStart width k-radius) (S.R src) i).re) x ε) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ preparedPackedSliceCost radius (coreLength s width k) w ∧
      Exec body (preparedPackedSlice offsetRows rows wordWidth src dst skip count savedSkip saved trash tmp)
        (mk v S) m (mk v' {S with R := (Function.update S.R dst
          (cstream A w (ownedCoreWords width k F)++S.R dst))}) ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (fun i => (packedIntervalRead q w (coreStart width k)
          (cstream A w (ownedCoreWords width k F)++S.R dst) i).re) x ε := by
  obtain ⟨v',m,hu,hm,he⟩ := preparedPackedSlice_exec (body := body)
    offsetRows rows wordWidth src dst skip count savedSkip saved trash tmp hreg
    (coreStart width k-radius) (coreLength s width k+2*radius) radius (coreLength s width k) w F
    (by omega) (by omega) tail v S hoffset hrows hwidth hsrc hfresh
  refine ⟨v',m,hu,hm,?_,?_⟩
  · simpa only [Nat.sub_add_cancel hleft,packedInterval,ownedCoreWords] using he
  · intro i hi
    have hi' := (mem_haloVertices _ _ i).mp hi
    have hh := herror i ((mem_haloVertices _ _ i).mpr ⟨by omega,by omega⟩)
    have hfit : coreStart width k-radius+(coreLength s width k+2*radius) ≤ s := by omega
    dsimp only at hh
    rw [hsrc,packedIntervalRead_eq q w _ _ F tail [] hfit i (by omega) (by omega)] at hh
    change ‖(packedIntervalRead q w (coreStart width k)
      (cstream A w (packedInterval (coreStart width k) (coreLength s width k) F)++S.R dst) i).re-x i‖ ≤ ε
    rw [packedIntervalRead_eq q w _ _ F (S.R dst) [] (by omega) i hi'.1 hi'.2]
    exact hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
