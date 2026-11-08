module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedNormalizeOwnedInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedRecoveryMagnitude

/-! Publication for the constructed floor-owned reference family; stability,
packet width and interval geometry are derived from the shared axis facts. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s t p u l : ℕ} [NeZero s] {α gap : ℝ} {P U : Type} {body : P → Pr P T Q A U}

theorem owned_normalize_exec (plan : RecoveryNormalizePlan T) (hA : 4 ≤ A)
    (axis : RecoveryAxisBounds s t p u l α gap) (target L k : ℕ)
    (hnear : t ≤ 2*s) (hL : 2 ≤ L)
    (ha : localityDepth p target*PhaseCellBand.width p u ≤ cut s t L k)
    (hb : cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u ≤ s)
    (hfit : L+2*(localityDepth p target*PhaseCellBand.width p u)+PhaseCellBand.width p u ≤ s)
    (Fs : List (ZMod t → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1) :
    let d := axis.ownedMasterInput target L k hnear hL ha hb
    let q := packedHaloPrecision p l s t u (target+1) 2
      (cut s t L k-localityDepth p target*PhaseCellBand.width p u)
      (cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u)
    let W := packedHaloCommonWidth p l s u (target+1) 2
    let c := cut s t L k
    let ownedRows := rows s t L k
    let active := haloVertices s c (cut s t L (k+1))
    let Zs := (axis.ownedTargets target L k hnear hL ha hb hfit Fs).reverse
    ∀
    (Ds : List (ZMod s → GaussianInt)) (oldTail tail headerTail : List (Fin (A+4)))
    (wl : List (Fin (A+4))) (_ : wl.length = d.B) (v : HS T Q A U) (S : Stacks T A)
    (_ : S.R (plan.scalar .wr) = wl)
    (_ : ∀ i : TblR 25, i ≠ .wr → S.R (plan.scalar i) = [])
    (_ : S.R plan.header = (inverseParameterWords p u l target s t d.a d.b).flatMap
      (fun i => binSyms d.B i.2)++headerTail)
    (_ : (S.R plan.precision).length = p) (_ : (S.R plan.wide).length = W)
    (_ : (S.R plan.rows).length = ownedRows)
    (_ : (S.R plan.replicas).length = Ds.length)
    (_ : ∀ k ∈ [plan.count,plan.work,plan.saved,plan.tmp,plan.sp,plan.sg,plan.cy], S.R k = [])
    (_ : ∀ i, S.R (plan.ports i) = [])
    (_ : S.R plan.inputWidth = [])
    (_ : S.R plan.src = (Ds.map (fun D => cstream A (2*q+8)
      (packedInterval c ownedRows D))).flatten++tail)
    (_ : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
      (packedIntervalRead q (2*q+8) c
        (cstream A (2*q+8) (packedInterval c ownedRows D)++oldTail)) z (1/(2 : ℝ)^target))
      Zs Ds),
    let Gs := Ds.map (fun D i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i))
    Gs.length = Ds.length ∧
    ∃ v' n, v'.user = v.user ∧
      n ≤ RecoveryNormalizePlan.generatedIntervalTimeCost d W ownedRows Ds.length ∧
      Exec body plan.generatedProgram (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R plan.header headerTail) plan.src
          ((Gs.map (fun D => cstream A W (packedInterval c ownedRows D))).flatten++tail))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
        (packedIntervalRead p W c (cstream A W (packedInterval c ownedRows D)++tail)) z
        (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p)))
        (Zs.map (fun z i => ((2 : ℂ)^(inverseNormalizationShift p))⁻¹*z i)) Gs ∧
      ∀ depth, ExecWithin body (fun depthNow z => mnSize z+depthNow ≤ mnSize (Host.mk v S)+depth+13*RecoveryNormalizePlan.generatedIntervalTimeCost d W ownedRows Ds.length)
        depth plan.generatedProgram (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R plan.header headerTail) plan.src
          ((Gs.map (fun D => cstream A W (packedInterval c ownedRows D))).flatten++tail))}) := by
  dsimp only
  intro Ds oldTail tail headerTail wl hwl v S hwidth hscalar hparameters hp hW hrows hN hblank hheaders hinputBlank hsrc hgood
  have hmono := cut_mono s t L (show k ≤ k+1 by omega)
  have hend : cut s t L k+rows s t L k = cut s t L (k+1) := by
    dsimp only [rows]
    omega
  have hinterval : cut s t L k+rows s t L k ≤ s := by rw [hend]; omega
  have hactive : ∀ i ∈ haloVertices s (cut s t L k) (cut s t L (k+1)),
      cut s t L k ≤ i.val ∧ i.val < cut s t L k+rows s t L k := by
    intro i hi
    rw [hend]
    exact (mem_haloVertices _ _ i).mp hi
  have hcover : ∀ i : ZMod s, cut s t L k ≤ i.val →
      i.val < cut s t L k+rows s t L k → i ∈ haloVertices s (cut s t L k) (cut s t L (k+1)) := by
    intro i hi hj
    apply (mem_haloVertices _ _ i).mpr
    rw [hend] at hj
    exact ⟨hi,hj⟩
  exact plan.generated_interval_exec (body := body) hA (axis.ownedMasterInput target L k hnear hL ha hb)
    _ _ _ _ (RecoveryAxisBounds.owned_normalization_width (s := s) (p := p) (u := u) (l := l) target) hinterval
    _ hactive hcover rfl _ (axis.ownedTargets_round_magnitude target L k hnear hL ha hb hfit Fs hF)
    Ds oldTail tail headerTail wl hwl v S hwidth hscalar hparameters hp hW hrows hN hblank hheaders hinputBlank hsrc hgood

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
