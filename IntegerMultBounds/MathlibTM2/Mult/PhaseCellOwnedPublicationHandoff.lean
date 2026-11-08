module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellActualOwnedNormalization
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedRecoveryMagnitude
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryPublicationReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalRecoveryLayout

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
namespace LocalRecoveryLayout
noncomputable section
variable {Q A s t p u l : ℕ} [NeZero s] {α gap : ℝ} {P U : Type} {body : P → Pr P tapes Q A U}

def normalize := RecoveryBanks.normalize recovery recovery_injective
def normalizeQueue := RecoveryBanks.queue recovery recovery_injective

theorem owned_normalize_after_bulk (hA : 4 ≤ A)
    (axis : RecoveryAxisBounds s t p u l α gap) (target L k : ℕ)
    (hnear : t ≤ 2*s) (hL : 2 ≤ L)
    (ha : localityDepth p target*PhaseCellBand.width p u ≤ cut s t L k)
    (hb : cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u ≤ s)
    (hfit : L+2*(localityDepth p target*PhaseCellBand.width p u)+PhaseCellBand.width p u ≤ s)
    (Fs : List (ZMod t → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1) :
    let d := axis.ownedMasterInput target L k hnear hL ha hb
    let r := axis.ownedJob target L k hnear hL ha hb hfit Fs hF
    let q := packedHaloPrecision p l s t u (target+1) 2
      (cut s t L k-localityDepth p target*PhaseCellBand.width p u)
      (cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u)
    let W := packedHaloCommonWidth p l s u (target+1) 2
    let c := cut s t L k
    let ownedRows := rows s t L k
    let active := haloVertices s c (cut s t L (k+1))
    let Zs := (axis.ownedTargets target L k hnear hL ha hb hfit Fs).reverse
    ∀ (Ds : List (ZMod s → GaussianInt)) (_ : Ds.length = Fs.length)
    (wl : List (Fin (A+4))) (_ : wl.length = d.B) (depth : ℕ) (v : HS tapes Q A U) (S F : Stacks tapes A)
    (_ : plan.CroppedReady crop d r Fs.length (localityDepth p target*PhaseCellBand.width p u) ownedRows wl S)
    (_ : ∀ i, F.R (recovery i) = S.R (recovery i)),
    let tail := F.R (crop.reg 12)
    let E : Stacks tapes A := {F with R := (Function.update (Function.update F.R source []) (crop.reg 12)
      ((Ds.map (fun D => cstream A (2*q+8) (packedInterval c ownedRows D))).flatten++tail))}
    List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
      (packedIntervalRead q (2*q+8) c (cstream A (2*q+8) (packedInterval c ownedRows D)++S.R (crop.reg 12)))
      z (1/(2 : ℝ)^target)) Zs Ds →
    let Gs := Ds.map (fun D i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i))
    Gs.length = Ds.length ∧
    ∃ v' n, v'.user = v.user ∧
      n ≤ RecoveryParameterQueue.prepareTimeCost d+RecoveryNormalizePlan.generatedIntervalTimeCost d W ownedRows Ds.length ∧
      Exec body normalizeQueue.normalizeProgram (Host.mk v E) n
        (Host.mk v' {E with R := (Function.update (Function.update E.R normalize.header []) normalize.src
          ((Gs.map (fun D => cstream A W (packedInterval c ownedRows D))).flatten++tail))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
        (packedIntervalRead p W c (cstream A W (packedInterval c ownedRows D)++tail)) z
        (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p)))
        (Zs.map (fun z i => ((2 : ℂ)^(inverseNormalizationShift p))⁻¹*z i)) Gs ∧
      ExecWithin body (fun depthNow z => mnSize z+depthNow ≤ mnSize (Host.mk v E)+depth+(8*(2*(4*d.B+4))+13*RecoveryNormalizePlan.generatedIntervalTimeCost d W ownedRows Ds.length))
        depth normalizeQueue.normalizeProgram (Host.mk v E) n
        (Host.mk v' {E with R := (Function.update (Function.update E.R normalize.header []) normalize.src
          ((Gs.map (fun D => cstream A W (packedInterval c ownedRows D))).flatten++tail))}) := by
  dsimp only
  intro Ds hDs wl hwl depth v S F hready hframe hgood
  let d := axis.ownedMasterInput target L k hnear hL ha hb
  let r := axis.ownedJob target L k hnear hL ha hb hfit Fs hF
  let q := packedHaloPrecision p l s t u (target+1) 2
    (cut s t L k-localityDepth p target*PhaseCellBand.width p u)
    (cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u)
  let output := (Ds.map (fun D => cstream A (2*q+8) (packedInterval (cut s t L k) (rows s t L k) D))).flatten++F.R (crop.reg 12)
  let E : Stacks tapes A := {F with R := Function.update (Function.update F.R source []) (crop.reg 12) output}
  have hready' := RecoveryBanks.publicationReady_after_bulk recovery recovery_injective d r Fs.length
    (localityDepth p target*PhaseCellBand.width p u) (rows s t L k) wl S F hready hframe source
    (fun i => geometry_ne_recovery 108 i) output
  have hsrc : E.R normalize.src = output := by
    change Function.update (Function.update F.R source []) (crop.reg 12) output (crop.reg 12) = output
    exact Function.update_self ..
  exact owned_normalize_exec (body := body) normalize normalizeQueue hA axis target L k hnear hL ha hb hfit Fs hF
    Ds (S.R (crop.reg 12)) (F.R (crop.reg 12)) [] wl hwl depth v E
    hready'.width hready'.scalar hready'.values hready'.queueBlank hready'.header
    hready'.precision hready'.wide hready'.rowCount (by
      have hr := hready'.replicas
      change (E.R normalize.replicas).length = Fs.length at hr
      exact hr.trans hDs.symm)
    hready'.blank hready'.ports hready'.inputWidth hsrc hgood

end
end LocalRecoveryLayout
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
