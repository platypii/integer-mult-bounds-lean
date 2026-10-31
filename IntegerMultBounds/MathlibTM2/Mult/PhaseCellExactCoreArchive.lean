module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridDispatchExactCoreTrace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntervalArchive

/-! Archive the exact-inverse-certified S3 output. Both accuracy and the unit
ball survive cropping, with the same decoded bytes and reversed input pairing. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement PhaseCellInterface
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem exactCoreArchive_exec
    (clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T)
    (hreg : [clock,skip,count,src,dst,savedSkip,saved,tmp,rows,width,retireCount,trash,retireTmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (p coreWidth k : ℕ)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (output : List (Fin (A+4)))
    (hproduced : ExactCoreProduced p coreWidth (fun _ => k) J r output)
    (hstart : coreStart coreWidth k ≤ s)
    (tail : List (Fin (A+4)))
    (hsrc : S.R src = output++tail)
    (hclock : (S.R clock).length = r.inputs.length)
    (hskip : (S.R skip).length = coreStart coreWidth k*(2*p+13))
    (hcount : (S.R count).length = coreLength s coreWidth k*(2*p+13))
    (hrows : (S.R rows).length = s)
    (hwidth : (S.R width).length = (2*p+13))
    (hclean : ∀ i ∈ [savedSkip,saved,tmp,retireCount,trash,retireTmp], S.R i = []) :
    ∃ Ds : List (ZMod s → GaussianInt), ∃ v' F n, v'.user = v.user ∧
      n ≤ r.inputs.length*(packedCoreArchiveStepCost (coreStart coreWidth k) (coreLength s coreWidth k)
        (s) (2*p+13)+3)+2 ∧
      Exec body (packedCoreArchiveLoop clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)
        (mk v S) n (mk v' F) ∧
      F.R src = tail ∧ F.R dst = (Ds.reverse.map (fun D => cstream A (2*p+13) (ownedCoreWords coreWidth k D))).flatten++S.R dst ∧
      F.R clock = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ i, i ≠ src → i ≠ dst → i ≠ clock → F.R i = S.R i) ∧
      List.Forall₂ (fun input D =>
        let out := packedIntervalRead p (2*p+13) (coreStart coreWidth k)
          (cstream A (2*p+13) (ownedCoreWords coreWidth k D)++S.R dst)
        (∀ i ∈ ownedCore s coreWidth k, ‖out i‖ ≤ 1) ∧
        ErrorOn (ownedCore s coreWidth k) out
          ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J r) ((1/2 : ℂ) • fun i => value p (input i)))
          (3/(2 : ℝ)^p))
        r.inputs.reverse Ds.reverse := by
  obtain ⟨Ds,houtput,hgood⟩ := hproduced
  have hlen : r.inputs.length = Ds.length := List.Forall₂.length_eq hgood
  obtain ⟨v',F,n,hu,hn,he,hsrc',hdst,hclock',hi,ho,hl,hframe⟩ := fullLineCoreArchive_exec
    clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp hreg
    v S (2*p+13) coreWidth k hstart Ds tail (by simpa only [houtput,FamilyDispatchInput.normalizedOutput] using hsrc)
    (hclock.trans hlen) hskip hcount hrows hwidth hclean
  refine ⟨Ds,v',F,n,hu,by simpa only [hlen] using hn,he,hsrc',hdst,hclock',hi,ho,hl,hframe,?_⟩
  apply List.Forall₂.imp _ (List.rel_reverse hgood)
  intro input D hD
  have hfit : coreStart coreWidth k+coreLength s coreWidth k ≤ s := by
    dsimp only [coreLength]
    have := Nat.min_le_right coreWidth (s-coreStart coreWidth k)
    omega
  have hread (i : ZMod s) (hi : i ∈ ownedCore s coreWidth k) :
      packedIntervalRead p (2*p+13) (coreStart coreWidth k)
        (cstream A (2*p+13) (ownedCoreWords coreWidth k D)++S.R dst) i =
      pairedCellRead p (2*p+13) (cstream A (2*p+13) (chirpLine s D)) i := by
    have hval := (mem_haloVertices _ _ i).mp hi
    simpa only [ownedCoreWords,packedInterval,List.append_nil] using
      packedIntervalRead_eq p (2*p+13) (coreStart coreWidth k) (coreLength s coreWidth k)
        D (S.R dst) [] hfit i hval.1 hval.2
  constructor
  · intro i hi
    rw [hread i hi]
    exact hD.1 i hi
  · intro i hi
    rw [hread i hi]
    exact hD.2 i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
