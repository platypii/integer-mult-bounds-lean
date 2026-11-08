module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedNormalizeOwnedInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseMasterInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryParameterQueueExec

/-! Prepare ordinary parameter words and execute owned-interval publication. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace RecoveryParameterQueue
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def normalizeProgram {plan : RecoveryNormalizePlan T} (queue : RecoveryParameterQueue plan) : Pr P T Q A U :=
  .seq queue.program plan.generatedProgram

noncomputable def prepareTimeCost (d : InverseMasterInput s) : ℕ :=
  (d.p+d.u+d.l+d.target+s+d.t+d.a+d.b)*(4*d.B+10)+8*(8*d.B+12)+1

theorem normalize_exec {plan : RecoveryNormalizePlan T} (queue : RecoveryParameterQueue plan) (hA : 4 ≤ A) (d : InverseMasterInput s)
    (W c L q : ℕ) (hWout : 2*d.p+13 ≤ W) (hfit : c+L ≤ s)
    (active : Finset (ZMod s))
    (hactive : ∀ i ∈ active, c ≤ i.val ∧ i.val < c+L)
    (hcover : ∀ i : ZMod s, c ≤ i.val → i.val < c+L → i ∈ active)
    (hq : q = executionPrecision d.p d.l (boundaryHaloTarget d.p d.u (boundaryRecoveryTarget d.p (d.target+1)) 2
      (haloBoundary s d.t (PhaseCellBand.width d.p d.u) d.a d.b).card) 2)
    (Zs : List (ZMod s → ℂ))
    (hmag : ∀ z ∈ Zs, ∀ i ∈ active, ‖z i‖ ≤ 4*(2 : ℝ)^(d.p+8))
    (Ds : List (ZMod s → GaussianInt)) (oldTail tail headerTail : List (Fin (A+4)))
    (wl : List (Fin (A+4))) (hwl : wl.length = d.B) (depth : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (plan.scalar .wr) = wl)
    (hscalar : ∀ i : TblR 25, i ≠ .wr → S.R (plan.scalar i) = [])
    (hparameters : ∀ i : Fin 8, (S.R (queue.parameters i)).length = d.values i)
    (hqueueBlank : ∀ i ∈ [queue.word,queue.saved,queue.tmp], S.R i = [])
    (hheader : S.R plan.header = headerTail)
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
      n ≤ prepareTimeCost d+RecoveryNormalizePlan.generatedIntervalTimeCost d W L Ds.length ∧
      Exec body queue.normalizeProgram (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R plan.header headerTail) plan.src
          ((Gs.map (fun D => cstream A W (packedInterval c L D))).flatten++tail))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
        (packedIntervalRead d.p W c (cstream A W (packedInterval c L D)++tail)) z
        (2/(2 : ℝ)^d.p+(1/(2 : ℝ)^d.target)/(2 : ℝ)^(inverseNormalizationShift d.p)))
        (Zs.map (fun z i => ((2 : ℂ)^(inverseNormalizationShift d.p))⁻¹*z i)) Gs ∧
      ExecWithin body (fun depthNow z => mnSize z+depthNow ≤ mnSize (Host.mk v S)+depth+(8*(2*(4*d.B+4))+13*RecoveryNormalizePlan.generatedIntervalTimeCost d W L Ds.length))
        depth queue.normalizeProgram (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R plan.header headerTail) plan.src
          ((Gs.map (fun D => cstream A W (packedInterval c L D))).flatten++tail))}) := by
  dsimp only
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := queue.exec (body := body) d.B d.p d.u d.l d.target s d.t d.a d.b
    v S (by rw [hwidth,hwl]) hparameters hqueueBlank depth
  let F : Stacks T A := {S with R := (Function.update S.R plan.header
    ((inverseParameterWords d.p d.u d.l d.target s d.t d.a d.b).flatMap
      (fun i => binSyms d.B i.2)++headerTail))}
  have hframe i (hi : i ≠ plan.header) : F.R i = S.R i := Function.update_of_ne hi _ _
  have hr := plan.regs
  regs_ne hr
  have hscalarF : ∀ i : TblR 25, i ≠ .wr → F.R (plan.scalar i) = [] := by
    intro i hi
    rw [hframe _ (plan.header_off i)]
    exact hscalar i hi
  have hblankF : ∀ k ∈ [plan.count,plan.work,plan.saved,plan.tmp,plan.sp,plan.sg,plan.cy], F.R k = [] := by
    intro k hk
    rcases (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hk) with hk | hk | hk | hk | hk | hk | hk <;>
      subst k <;> rw [hframe _ (Ne.symm (by assumption))] <;> exact hblank _ (by simp)
  have hheadersF i : F.R (plan.ports i) = [] := by
    have hi : plan.ports i ≠ plan.header := by fin_cases i <;> exact Ne.symm (by assumption)
    rw [hframe _ hi]
    exact hheaders i
  obtain ⟨hlen,v₂,n₂,hu₂,hn₂,he₂,haccuracy,htrace⟩ := plan.generated_interval_exec (body := body) hA d
    W c L q hWout hfit active hactive hcover hq Zs hmag Ds oldTail tail headerTail wl hwl v₁ F
    ((hframe _ (plan.header_off .wr)).trans hwidth) hscalarF (by simp [F])
    ((hframe _ ‹plan.header ≠ plan.precision›.symm) ▸ hp)
    ((hframe _ ‹plan.header ≠ plan.wide›.symm) ▸ hW)
    ((hframe _ ‹plan.header ≠ plan.rows›.symm) ▸ hrows)
    ((hframe _ ‹plan.header ≠ plan.replicas›.symm) ▸ hN)
    hblankF hheadersF ((hframe _ ‹plan.header ≠ plan.inputWidth›.symm) ▸ hinputBlank)
    ((hframe _ ‹plan.header ≠ plan.src›.symm) ▸ hsrc) hgood
  let output := ((Ds.map (fun D i => finalRoundWord (2*q+8) q d.p (inverseNormalizationShift d.p) (D i))).map
    (fun D => cstream A W (packedInterval c L D))).flatten++tail
  have hfinal : {F with R := Function.update (Function.update F.R plan.header headerTail) plan.src output} =
      {S with R := Function.update (Function.update S.R plan.header headerTail) plan.src output} := by
    congr 1
    simp only [F,Function.update_idem]
  have he₁' := he₁
  rw [hheader] at he₁'
  change ExecWithin body _ depth queue.program (Host.mk v S) n₁ (Host.mk v₁ F) at he₁'
  have hwhole := mn_seq_within_add he₁' (htrace depth)
  rw [hfinal] at hwhole
  refine ⟨hlen,v₂,n₁+n₂,hu₂.trans hu₁,?_,hwhole.toExec,haccuracy,hwhole⟩
  change n₁ ≤ prepareTimeCost d at hn₁
  omega

end RecoveryParameterQueue
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
