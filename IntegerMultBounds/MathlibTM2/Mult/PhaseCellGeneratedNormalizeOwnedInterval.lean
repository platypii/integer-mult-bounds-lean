module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedNormalizeStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseMasterInput

/-! Owned-interval publication starting with a blank byte-count tape. -/
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

noncomputable def generatedIntervalTimeCost (d : InverseMasterInput s) (W L N : ℕ) : ℕ :=
  generatedNormalizePackedBatchCost d.B d.p d.u d.l d.target s d.t d.a d.b W N L+
    214*d.B+217

theorem generated_interval_exec (plan : RecoveryNormalizePlan T) (hA : 4 ≤ A) (d : InverseMasterInput s)
    (W c L q : ℕ) (hWout : 2*d.p+13 ≤ W) (hfit : c+L ≤ s)
    (active : Finset (ZMod s))
    (hactive : ∀ i ∈ active, c ≤ i.val ∧ i.val < c+L)
    (hcover : ∀ i : ZMod s, c ≤ i.val → i.val < c+L → i ∈ active)
    (hq : q = executionPrecision d.p d.l (boundaryHaloTarget d.p d.u (boundaryRecoveryTarget d.p (d.target+1)) 2
      (haloBoundary s d.t (PhaseCellBand.width d.p d.u) d.a d.b).card) 2)
    (Zs : List (ZMod s → ℂ))
    (hmag : ∀ z ∈ Zs, ∀ i ∈ active, ‖z i‖ ≤ 4*(2 : ℝ)^(d.p+8))
    (Ds : List (ZMod s → GaussianInt)) (oldTail tail headerTail : List (Fin (A+4)))
    (wl : List (Fin (A+4))) (hwl : wl.length = d.B) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (plan.scalar .wr) = wl)
    (hscalar : ∀ i : TblR 25, i ≠ .wr → S.R (plan.scalar i) = [])
    (hparameters : S.R plan.header = (inverseParameterWords d.p d.u d.l d.target s d.t d.a d.b).flatMap
      (fun i => binSyms d.B i.2)++headerTail)
    (hp : (S.R plan.precision).length = d.p) (hW : (S.R plan.wide).length = W)
    (hrows : (S.R plan.rows).length = L)
    (hN : (S.R plan.replicas).length = Ds.length)
    (hblank : ∀ k ∈ [plan.count,plan.work,plan.saved,plan.tmp,plan.sp,plan.sg,plan.cy], S.R k = [])
    (hheaders : ∀ i, S.R (plan.ports i) = [])
    (hinputBlank : S.R plan.inputWidth = [])
    (hsrc : S.R plan.src = (Ds.map (fun D => cstream A (2*q+8)
      (packedInterval c L D))).flatten++tail)
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
      (packedIntervalRead q (2*q+8) c
        (cstream A (2*q+8) (packedInterval c L D)++oldTail)) z (1/(2 : ℝ)^d.target))
      Zs Ds) :
    let Gs := Ds.map (fun D i => finalRoundWord (2*q+8) q d.p (inverseNormalizationShift d.p) (D i))
    Gs.length = Ds.length ∧
    ∃ v' n, v'.user = v.user ∧
      n ≤ generatedIntervalTimeCost d W L Ds.length ∧
      Exec body plan.generatedProgram (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R plan.header headerTail) plan.src
          ((Gs.map (fun D => cstream A W (packedInterval c L D))).flatten++tail))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
        (packedIntervalRead d.p W c (cstream A W (packedInterval c L D)++tail)) z
        (2/(2 : ℝ)^d.p+(1/(2 : ℝ)^d.target)/(2 : ℝ)^(inverseNormalizationShift d.p)))
        (Zs.map (fun z i => ((2 : ℂ)^(inverseNormalizationShift d.p))⁻¹*z i)) Gs ∧
      ∀ depth, ExecWithin body (fun depthNow z => mnSize z+depthNow ≤ mnSize (Host.mk v S)+depth+13*generatedIntervalTimeCost d W L Ds.length)
        depth plan.generatedProgram (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R plan.header headerTail) plan.src
          ((Gs.map (fun D => cstream A W (packedInterval c L D))).flatten++tail))}) := by
  dsimp only
  have hq' : q = 4*inverseExecutionExponent d.p d.l d.target
      (haloBoundary s d.t (PhaseCellBand.width d.p d.u) d.a d.b).card (PhaseCellBand.width d.p d.u) := by
    rw [hq,packedRound_precision]
  have hw : 2*q+8 = 8*inverseExecutionExponent d.p d.l d.target
      (haloBoundary s d.t (PhaseCellBand.width d.p d.u) d.a d.b).card (PhaseCellBand.width d.p d.u)+8 := by omega
  have he : 1/(2 : ℝ)^d.target ≤ 1 :=
    (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hrun := ordinaryGeneratedNormalizePackedBatch_exec (body := body) hA
    plan.scalar plan.scalar_injective plan.ports plan.ports_injective plan.regs plan.separate plan.ports_off plan.header_off
    d.values_fit wl hwl d.hst d.has d.hbs d.hband d.band_room d.geometry_room d.precision_room
    W c L hWout hfit active hactive hcover Zs Ds (1/(2 : ℝ)^d.target) he hmag
    oldTail tail headerTail v S hwidth hscalar hparameters hp hW hrows hN hblank hheaders hinputBlank
  dsimp only at hrun
  rw [←hq',←hw] at hrun
  obtain ⟨hlen,v',n,hu,hn,hex,haccuracy⟩ := hrun hsrc hgood
  exact ⟨hlen,v',n,hu,hn,hex,haccuracy,fun depth =>
    mn_native_exec_within hex 13 plan.generated_native depth _ (by
      change n ≤ generatedIntervalTimeCost d W L Ds.length at hn
      omega)⟩

end RecoveryNormalizePlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
