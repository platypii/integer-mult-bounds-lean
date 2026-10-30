module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCoreArchiveLoop

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

/-- Publish the solver's reversed archive into forward input order, with no
extra reversal pass. Every cropped block retains its input's halo accuracy. -/
theorem packedCoreArchiveLoop_accurate_exec
    (clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T)
    (hreg : [clock,skip,count,src,dst,savedSkip,saved,tmp,rows,width,retireCount,trash,retireTmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (q w coreWidth k radius : ℕ)
    (hleft : radius ≤ coreStart coreWidth k)
    (hright : coreStart coreWidth k+coreLength s coreWidth k+radius ≤ s)
    (Ds : List (ZMod s → GaussianInt)) (tail : List (Fin (A+4)))
    (hsrc : S.R src = (Ds.reverse.map (fun D => cstream A w
      (packedInterval (coreStart coreWidth k-radius) (coreLength s coreWidth k+2*radius) D))).flatten++tail)
    (hclock : (S.R clock).length = Ds.length)
    (hskip : (S.R skip).length = radius*w)
    (hcount : (S.R count).length = coreLength s coreWidth k*w)
    (hrows : (S.R rows).length = coreLength s coreWidth k+2*radius)
    (hwidth : (S.R width).length = w)
    (hclean : ∀ i ∈ [savedSkip,saved,tmp,retireCount,trash,retireTmp], S.R i = [])
    (inputs : List ((ZMod s → GaussianInt) × (ZMod s → ℝ))) (e : ℝ)
    (hgood : List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn
      (haloVertices s (coreStart coreWidth k-radius) (coreStart coreWidth k+coreLength s coreWidth k+radius))
      (fun i => (packedIntervalRead q w (coreStart coreWidth k-radius)
        (cstream A w (packedInterval (coreStart coreWidth k-radius) (coreLength s coreWidth k+2*radius) D)) i).re)
      x.2 e) inputs Ds) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ Ds.length*(packedCoreArchiveStepCost radius (coreLength s coreWidth k)
        (coreLength s coreWidth k+2*radius) w+3)+2 ∧
      Exec body (packedCoreArchiveLoop clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)
        (mk v S) n (mk v' F) ∧
      F.R src = tail ∧ F.R dst = (Ds.map (fun D => cstream A w (ownedCoreWords coreWidth k D))).flatten++S.R dst ∧
      F.R clock = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ i, i ≠ src → i ≠ dst → i ≠ clock → F.R i = S.R i) ∧
      List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
        (fun i => (packedIntervalRead q w (coreStart coreWidth k)
          (cstream A w (ownedCoreWords coreWidth k D)++S.R dst) i).re) x.2 e) inputs Ds := by
  obtain ⟨v',F,n,hu,hn,he,hsrc',hdst,hclock',hi,ho,hl,hframe⟩ := packedCoreArchiveLoop_exec
    clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp hreg
    v S w coreWidth k radius hleft hright Ds.reverse tail hsrc
    (by simpa only [List.length_reverse] using hclock) hskip hcount hrows hwidth hclean
  refine ⟨v',F,n,hu,by simpa only [List.length_reverse] using hn,he,hsrc',?_,hclock',hi,ho,hl,hframe,?_⟩
  · simpa only [List.reverse_reverse] using hdst
  · apply List.Forall₂.imp _ hgood
    intro x D hD
    apply packedCore_error q w (coreStart coreWidth k-radius)
      (coreStart coreWidth k+coreLength s coreWidth k+radius) coreWidth k D (S.R dst)
      (by omega) (by omega) hright x.2 e
    have hlength : coreStart coreWidth k+coreLength s coreWidth k+radius-(coreStart coreWidth k-radius) =
        coreLength s coreWidth k+2*radius := by omega
    simpa only [hlength] using hD

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
