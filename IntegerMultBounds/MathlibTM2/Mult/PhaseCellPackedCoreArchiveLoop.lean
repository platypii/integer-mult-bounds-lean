module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntervalArchive

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {T Q A s : ℕ} {P U : Type} {body : P → Pr P T Q A U}


theorem packedCoreArchiveLoop_exec
    (clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T)
    (hreg : [clock,skip,count,src,dst,savedSkip,saved,tmp,rows,width,retireCount,trash,retireTmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (w coreWidth k radius : ℕ)
    (hleft : radius ≤ coreStart coreWidth k)
    (hright : coreStart coreWidth k+coreLength s coreWidth k+radius ≤ s)
    (Ds : List (ZMod s → GaussianInt)) (tail : List (Fin (A+4)))
    (hsrc : S.R src = (Ds.map (fun D => cstream A w
      (packedInterval (coreStart coreWidth k-radius) (coreLength s coreWidth k+2*radius) D))).flatten++tail)
    (hclock : (S.R clock).length = Ds.length)
    (hskip : (S.R skip).length = radius*w)
    (hcount : (S.R count).length = coreLength s coreWidth k*w)
    (hrows : (S.R rows).length = coreLength s coreWidth k+2*radius)
    (hwidth : (S.R width).length = w)
    (hclean : ∀ i ∈ [savedSkip,saved,tmp,retireCount,trash,retireTmp], S.R i = []) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ Ds.length*(packedCoreArchiveStepCost radius (coreLength s coreWidth k)
        (coreLength s coreWidth k+2*radius) w+3)+2 ∧
      Exec body (packedCoreArchiveLoop clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)
        (mk v S) n (mk v' F) ∧
      F.R src = tail ∧ F.R dst = (Ds.reverse.map (fun D => cstream A w (ownedCoreWords coreWidth k D))).flatten++S.R dst ∧
      F.R clock = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ src → i ≠ dst → i ≠ clock → F.R i = S.R i := by
  obtain ⟨v',F,n,hu,hn,he,hsrc',hdst,hclock',hi,ho,hl,hframe⟩ := packedCoreArchiveLoop_interval_exec
    clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp hreg
    v S w (coreStart coreWidth k-radius) (coreLength s coreWidth k+2*radius)
    radius (coreLength s coreWidth k) (by omega) (by omega) Ds tail hsrc hclock
    hskip hcount hrows hwidth hclean
  refine ⟨v',F,n,hu,hn,he,hsrc',?_,hclock',hi,ho,hl,hframe⟩
  simpa only [Nat.sub_add_cancel hleft,packedInterval,ownedCoreWords] using hdst

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
