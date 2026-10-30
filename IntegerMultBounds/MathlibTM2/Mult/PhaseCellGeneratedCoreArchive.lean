module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridDispatchCoreTrace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntervalArchive

/-! Consume the actual normalized S3 result and archive its owned cores.
The same fields witness the returned bytes and accuracy in reversed input order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement PhaseCellInterface
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem generatedCoreArchive_exec
    (clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T)
    (hreg : [clock,skip,count,src,dst,savedSkip,saved,tmp,rows,width,retireCount,trash,retireTmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (p coreWidth k target : ℕ)
    (r : FamilyDispatchInput s A)
    (X Y : FamilyDispatchInput s A → (ZMod s → GaussianInt) → ZMod s → ℝ)
    (output : List (Fin (A+4)))
    (hproduced : GeneratedCoreProduced p coreWidth target (fun _ => k) X Y r output)
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
      List.Forall₂ (fun input D => ErrorOn (ownedCore s coreWidth k)
        (packedIntervalRead p (2*p+13) (coreStart coreWidth k)
          (cstream A (2*p+13) (ownedCoreWords coreWidth k D)++S.R dst))
        (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(⟨X r input i,Y r input i⟩ : ℂ))
        ((2/(2 : ℝ)^p+(1/(2 : ℝ)^r.target)/(2 : ℝ)^inverseNormalizationShift p)+
          (1/(2 : ℝ)^target+1/(2 : ℝ)^target)/(2 : ℝ)^inverseNormalizationShift p))
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
  apply packedInterval_error p (2*p+13) (coreStart coreWidth k) (coreLength s coreWidth k) D (S.R dst) []
    (by dsimp only [coreLength]; have := Nat.min_le_right coreWidth (s-coreStart coreWidth k); omega)
    (ownedCore s coreWidth k) ?_ _ _ (by simpa only [List.append_nil] using hD)
  intro i hi
  exact (mem_haloVertices _ _ i).mp hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
