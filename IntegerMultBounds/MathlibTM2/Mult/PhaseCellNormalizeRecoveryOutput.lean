module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryNormalizeStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryMagnitude

/-! Execute the existing final-rounding/publication program on cropped recovery
packets. Magnitude, common width and locality follow from the core job. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace RecoveryNormalizePlan
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def timeCost (r : PackedNormalizedJob A s) (N : ℕ) : ℕ :=
  preparedNormalizePackedBatchCost r.Bcore r.p r.u r.l r.targetOut s r.t r.a r.b r.W N
    (coreLength s r.coreWidth r.k)+214*r.Bcore+217

theorem exec (plan : RecoveryNormalizePlan T) (hA : 4 ≤ A) (r : PackedNormalizedJob A s)
    (Ds : List (ZMod s → GaussianInt)) (oldTail tail headerTail : List (Fin (A+4)))
    (wl : List (Fin (A+4))) (hwl : wl.length = r.Bcore) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (plan.scalar .wr) = wl)
    (hscalar : ∀ i : TblR 25, i ≠ .wr → S.R (plan.scalar i) = [])
    (hparameters : S.R plan.header = (inverseParameterWords r.p r.u r.l r.targetOut s r.t r.a r.b).flatMap
      (fun i => binSyms r.Bcore i.2)++headerTail)
    (hp : (S.R plan.precision).length = r.p) (hW : (S.R plan.wide).length = r.W)
    (hrows : (S.R plan.rows).length = coreLength s r.coreWidth r.k)
    (hN : (S.R plan.replicas).length = Ds.length)
    (hblank : ∀ k ∈ [plan.count,plan.work,plan.saved,plan.tmp,plan.sp,plan.sg,plan.cy], S.R k = [])
    (hheaders : ∀ i, S.R (plan.ports i) = [])
    (hinputWidth : (S.R plan.inputWidth).length = coreLength s r.coreWidth r.k*(2*r.q+8))
    (hsrc : S.R plan.src = (Ds.map (fun D => cstream A (2*r.q+8)
      (ownedCoreWords r.coreWidth r.k D))).flatten++tail)
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (ownedCore s r.coreWidth r.k)
      (packedIntervalRead r.q (2*r.q+8) (coreStart r.coreWidth r.k)
        (cstream A (2*r.q+8) (ownedCoreWords r.coreWidth r.k D)++oldTail)) z (1/(2 : ℝ)^r.targetOut))
      (r.Fs.map (componentSolution r.localSolution)).reverse Ds) :
    let Gs := Ds.map (fun D i => finalRoundWord (2*r.q+8) r.q r.p (inverseNormalizationShift r.p) (D i))
    Gs.length = Ds.length ∧
    ∃ v' n, v'.user = v.user ∧
      n ≤ timeCost r Ds.length ∧
      Exec body plan.program (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R plan.header headerTail) plan.src
          ((Gs.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten++tail))}) ∧
      List.Forall₂ (fun F D => PhaseCellInterface.ErrorOn (ownedCore s r.coreWidth r.k)
        (packedIntervalRead r.p r.W (coreStart r.coreWidth r.k)
          (cstream A r.W (ownedCoreWords r.coreWidth r.k D)++tail)) (r.rowTarget F) r.rowError) r.Fs.reverse Gs ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+13*timeCost r Ds.length)
        depth plan.program (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R plan.header headerTail) plan.src
          ((Gs.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten++tail))}) := by
  dsimp only
  have hfit : coreStart r.coreWidth r.k+coreLength s r.coreWidth r.k ≤ s := by have := r.hright; omega
  have hactive : ∀ i ∈ ownedCore s r.coreWidth r.k,
      coreStart r.coreWidth r.k ≤ i.val ∧ i.val < coreStart r.coreWidth r.k+coreLength s r.coreWidth r.k := by
    intro i hi; exact (mem_haloVertices _ _ i).mp hi
  have hcover : ∀ i : ZMod s, coreStart r.coreWidth r.k ≤ i.val →
      i.val < coreStart r.coreWidth r.k+coreLength s r.coreWidth r.k → i ∈ ownedCore s r.coreWidth r.k := by
    intro i hi hj; exact (mem_haloVertices _ _ i).mpr ⟨hi,hj⟩
  have hmag : ∀ z ∈ (r.Fs.map (componentSolution r.localSolution)).reverse,
      ∀ i ∈ ownedCore s r.coreWidth r.k, ‖z i‖ ≤ 4*(2 : ℝ)^(r.p+8) := by
    intro z hz i hi
    obtain ⟨F,hF,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hz)
    exact r.localSolution_round_magnitude F hF i hi
  have hgood' := hgood
  rw [← component_error_bit r.targetOut] at hgood'
  obtain ⟨hlen,v',n,hu,hn,hex,haccuracy⟩ := ordinaryNormalizeNativeBatch_exec (body := body) hA
    plan.scalar plan.scalar_injective plan.ports plan.ports_injective plan.regs plan.separate plan.ports_off plan.header_off
    r.hvaluesFit wl hwl r.bounds.hst r.bounds.has r.bounds.hbs r.bounds.hband r.hbandRoom r.hgeometryRoom r.hprecisionRoom
    r.W (coreStart r.coreWidth r.k) (coreLength s r.coreWidth r.k) r.normalization_width hfit
    (ownedCore s r.coreWidth r.k) hactive hcover r.q r.hqSizing
    (r.Fs.map (componentSolution r.localSolution)).reverse Ds hmag oldTail tail headerTail v S
    hwidth hscalar hparameters hp hW hrows hN hblank hheaders hinputWidth hsrc hgood'
  refine ⟨hlen,v',n,hu,hn,hex,?_,fun depth => plan.within_stock hex hn depth⟩
  have hback := List.rel_reverse haccuracy
  simp only [List.map_reverse,List.reverse_reverse] at hback
  have hglobal := r.normalized_recovery_core_accuracy _ tail hback
  simpa only [List.reverse_reverse] using List.rel_reverse hglobal

end RecoveryNormalizePlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
