module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublication

/-! Publish a complex S3 result on its owned core. The numerical certificate
concerns the bytes returned by the restoring publication execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem publishOwnedCore_accuracy_exec {skip count src dst savedSkip saved tmp : Fin T}
    (hreg : [skip,count,src,dst,savedSkip,saved,tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (q w width k : ℕ)
    (hstart : coreStart width k ≤ s) (Z : ZMod s → GaussianInt)
    (tail : List (Fin (A+4)))
    (hsrc : S.R src = cstream A w (chirpLine s Z)++tail)
    (hskip : (S.R skip).length = coreStart width k*w)
    (hcount : (S.R count).length = coreLength s width k*w)
    (hsavedSkip : S.R savedSkip = []) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (target : ZMod s → ℂ) (error : ℝ)
    (herror : PhaseCellInterface.ErrorOn (ownedCore s width k)
      (pairedCellRead q w (cstream A w (chirpLine s Z))) target error) :
    ∃ v', v'.user = v.user ∧
      Exec body (copySlice skip count src dst savedSkip saved tmp) (mk v S)
        (6*(coreStart width k*w)+10*(coreLength s width k*w)+16)
        (mk v' {S with R := (Function.update S.R dst
          (cstream A w (ownedCoreWords width k Z)++S.R dst))}) ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (packedIntervalRead q w (coreStart width k)
          (cstream A w (ownedCoreWords width k Z)++S.R dst)) target error := by
  obtain ⟨v',hu,he⟩ := publishOwnedCore_exec (body := body) hreg v S w width k
    hstart Z tail hsrc hskip hcount hsavedSkip hsaved htmp
  refine ⟨v',hu,he,?_⟩
  apply packedInterval_error q w (coreStart width k) (coreLength s width k) Z (S.R dst) []
    (by dsimp only [coreLength]; have := Nat.min_le_right width (s-coreStart width k); omega)
    (ownedCore s width k) ?_ target error
    (by simpa only [List.append_nil] using herror)
  intro i hi
  exact (mem_haloVertices _ _ i).mp hi

/-- Packed halo publication traverses only the padding; the error is unchanged. -/
theorem publishPackedCore_accuracy_exec {skip count src dst savedSkip saved tmp : Fin T}
    (hreg : [skip,count,src,dst,savedSkip,saved,tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (q w width k radius : ℕ)
    (hleft : radius ≤ coreStart width k)
    (hright : coreStart width k+coreLength s width k+radius ≤ s) (Z : ZMod s → GaussianInt)
    (tail : List (Fin (A+4)))
    (hsrc : S.R src = cstream A w
      (packedInterval (coreStart width k-radius) (coreLength s width k+2*radius) Z)++tail)
    (hskip : (S.R skip).length = radius*w)
    (hcount : (S.R count).length = coreLength s width k*w)
    (hsavedSkip : S.R savedSkip = []) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (target : ZMod s → ℂ) (error : ℝ)
    (herror : PhaseCellInterface.ErrorOn (ownedCore s width k)
      (pairedCellRead q w (cstream A w (chirpLine s Z))) target error) :
    ∃ v', v'.user = v.user ∧
      Exec body (copySlice skip count src dst savedSkip saved tmp) (mk v S)
        (6*(radius*w)+10*(coreLength s width k*w)+16)
        (mk v' {S with R := (Function.update S.R dst
          (cstream A w (ownedCoreWords width k Z)++S.R dst))}) ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (packedIntervalRead q w (coreStart width k)
          (cstream A w (ownedCoreWords width k Z)++S.R dst)) target error := by
  obtain ⟨v',hu,he⟩ := publishPackedCore_exec (body := body) hreg v S w width k radius
    hleft hright Z tail hsrc hskip hcount hsavedSkip hsaved htmp
  refine ⟨v',hu,he,?_⟩
  apply packedInterval_error q w (coreStart width k) (coreLength s width k) Z (S.R dst) []
    (by dsimp only [coreLength]; have := Nat.min_le_right width (s-coreStart width k); omega)
    (ownedCore s width k) ?_ target error
    (by simpa only [List.append_nil] using herror)
  intro i hi
  exact (mem_haloVertices _ _ i).mp hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
