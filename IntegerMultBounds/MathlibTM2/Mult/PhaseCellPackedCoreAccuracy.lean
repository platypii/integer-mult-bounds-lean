module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublication

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- Crop a decoded halo certificate to its owned core, with any output suffix.
Both readers decode the same ambient word; no new numerical loss is incurred. -/
theorem packedCore_error {A s : ℕ} [NeZero s] (q w a b width k : ℕ)
    (D : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (ha : a ≤ coreStart width k) (hcore : coreStart width k+coreLength s width k ≤ b)
    (hb : b ≤ s) (y : ZMod s → ℝ) (e : ℝ)
    (herror : PhaseCellInterface.ErrorOn (haloVertices s a b)
      (fun i => (packedIntervalRead q w a (cstream A w (packedInterval a (b-a) D)) i).re) y e) :
    PhaseCellInterface.ErrorOn (ownedCore s width k)
      (fun i => (packedIntervalRead q w (coreStart width k)
        (cstream A w (ownedCoreWords width k D)++tail) i).re) y e := by
  intro i hi
  have hval := (mem_haloVertices (coreStart width k) (coreStart width k+coreLength s width k) i).mp hi
  have hihalo : i ∈ haloVertices s a b := (mem_haloVertices a b i).mpr ⟨by omega,by omega⟩
  have hreadCore := packedIntervalRead_eq (A := A) q w (coreStart width k) (coreLength s width k)
    D tail [] (by omega) i hval.1 hval.2
  have hreadHalo := packedIntervalRead_eq (A := A) q w a (b-a) D [] []
    (by omega) i (by omega) (by omega)
  have hread : packedIntervalRead q w (coreStart width k)
      (cstream A w (ownedCoreWords width k D)++tail) i =
      packedIntervalRead q w a (cstream A w (packedInterval a (b-a) D)) i := by
    simpa only [ownedCoreWords,packedInterval,List.append_nil] using hreadCore.trans hreadHalo.symm
  dsimp only
  rw [hread]
  exact herror i hihalo

variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

/-- The executed restoring publisher preserves the halo's error bound on the
actual destination prefix. Its cost traverses only the halo padding. -/
theorem publishPackedCore_accurate_exec {skip count src dst savedSkip saved tmp : Fin T}
    (hreg : [skip,count,src,dst,savedSkip,saved,tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (q w width k radius : ℕ)
    (hleft : radius ≤ coreStart width k)
    (hright : coreStart width k+coreLength s width k+radius ≤ s)
    (D : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (hsrc : S.R src = cstream A w
      (packedInterval (coreStart width k-radius) (coreLength s width k+2*radius) D)++tail)
    (hskip : (S.R skip).length = radius*w)
    (hcount : (S.R count).length = coreLength s width k*w)
    (hsavedSkip : S.R savedSkip = []) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (y : ZMod s → ℝ) (e : ℝ)
    (herror : PhaseCellInterface.ErrorOn
      (haloVertices s (coreStart width k-radius) (coreStart width k+coreLength s width k+radius))
      (fun i => (packedIntervalRead q w (coreStart width k-radius)
        (cstream A w (packedInterval (coreStart width k-radius) (coreLength s width k+2*radius) D)) i).re) y e) :
    ∃ v', v'.user = v.user ∧
      Exec body (copySlice skip count src dst savedSkip saved tmp) (mk v S)
        (6*(radius*w)+10*(coreLength s width k*w)+16)
        (mk v' {S with R := (Function.update S.R dst
          (cstream A w (ownedCoreWords width k D)++S.R dst))}) ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (fun i => (packedIntervalRead q w (coreStart width k)
          (cstream A w (ownedCoreWords width k D)++S.R dst) i).re) y e := by
  obtain ⟨v',hu,he⟩ := publishPackedCore_exec hreg v S w width k radius hleft hright D tail
    hsrc hskip hcount hsavedSkip hsaved htmp
  refine ⟨v',hu,he,?_⟩
  apply packedCore_error q w (coreStart width k-radius)
    (coreStart width k+coreLength s width k+radius) width k D (S.R dst)
    (by omega) (by omega) hright y e
  have hlength : coreStart width k+coreLength s width k+radius-(coreStart width k-radius) =
      coreLength s width k+2*radius := by omega
  simpa only [hlength] using herror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
