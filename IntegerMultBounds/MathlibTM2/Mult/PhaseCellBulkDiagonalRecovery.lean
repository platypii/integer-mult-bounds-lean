module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBulkPublishedRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedDiagonalHandoff
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalBatchAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedB0Endpoint

/-! Compose actual bulk publication with the complete shared diagonal stage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
  IntegerMultBounds.NLogN.PhaseCellMatrix
  ComputedRecoveryPlan
noncomputable section
variable {s t p u l Q A : ℕ} [NeZero s] [NeZero t] {α gap : ℝ} {P U : Type} {body : P → Pr P tapes Q A U}

def bulkDiagonalProgram (b : RawRecoveryProgramBounds Q A U) : Pr P tapes Q A U :=
  .seq (bulkPublishedProgram b) (completeDiagonalBatch b.hQ)

theorem bulk_diagonal_exec_ofAxisBounds (b : RawRecoveryProgramBounds Q A U)
    (alpha : ℕ) (hp13 : 13 ≤ p) (halpha : 2 ≤ alpha) (halphap : alpha^2 ≤ p)
    (axis : RecoveryAxisBounds s t p u l (alpha : ℝ) gap)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : J ∘L PhaseCellOperator.exact s t (alpha : ℝ) = 1)
    (target L k : ℕ)
    (hnear : t ≤ 2*s) (hL : 2 ≤ L)
    (ha : localityDepth p target*PhaseCellBand.width p u ≤ cut s t L k)
    (hb : cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u ≤ s)
    (hfit : L+2*(localityDepth p target*PhaseCellBand.width p u)+PhaseCellBand.width p u ≤ s)
    (W V targetOrigin targetSpan : ℕ)
    (Fs : List (ZMod t → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1) :
    let radius := localityDepth p target*PhaseCellBand.width p u
    let d := axis.ownedMasterInput target L k hnear hL ha hb
    let r := axis.ownedJob target L k hnear hL ha hb hfit Fs hF
    ∀
    (_ : r.problem.origin+r.problem.span+2*t*(r.problem.origin+r.problem.span)+3*s < 2^W)
    (_ : ∀ j < r.problem.span, targetOrigin ≤ nearestNatural s t (r.problem.origin+j) ∧
      nearestNatural s t (r.problem.origin+j) < targetOrigin+targetSpan)
    (_ : r.W < 2^V) (_ : targetSpan < 2^V) (_ : targetSpan*r.W < 2^V)
    (_ : V ≤ W) (_ : 4 ≤ A) (_ : 0 < V)
    (wl : List (Fin (A+4))) (_ : wl.length = d.B) (v : HS tapes Q A U) (S : Stacks tapes A)
    (_ : plan.CroppedReady crop d r Fs.length radius (rows s t L k) wl S)
    (_ : LocalSelectionHeaders A W V s t r.problem.origin targetOrigin r.W r.problem.span (embStk geometry S))
    (_ : (S.R (batch 5)).length = targetSpan)
    (tail : List (Fin (A+4)))
    (_ : S.R (batch 2) = (Fs.flatMap fun F => cstream A r.W (cyclicInterval targetOrigin targetSpan F))++tail)
    (_ : S.R (batch 3) = []) (_ : S.R (batch 4) = [])
    (_ : S.R source = []) (_ : S.R (geometry 110) = []) (_ : S.R (plan.work 124) = [])
    (_ : ∀ j ∈ [batch 0,batch 1,scratch 0,scratch 1,scratch 2,scratch 3], S.R j = [])
    (_ : ∀ j, S.L j = []) (Cdiag Cprog depth : ℕ)
    (_ : mnProgPush (descriptorSolverSchedule plan.src plan.saved plan.tmp plan.clock plan.savedClock
      (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A) plan.work plan.src plan.saved plan.count plan.tmp plan.spare
        plan.result b.hR b.hQ)) ≤ Cprog)
    (_ : ∀ f, mnProgPush (body f) ≤ Cprog)
    (_ : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U) diagonalMul diagonalMul_injective
      diagonal_tapes b.hQ (rsbCr diagonalRole .src .df .dst)) ≤ Cdiag),
    ∃ (F : Stacks tapes A) (Gs : List (ZMod s → GaussianInt)), Gs.length = Fs.length ∧
      F.R (batch 2) = S.R (batch 2) ∧ (∀ i, F.R (recovery i) = S.R (recovery i)) ∧ F.L = S.L ∧
    let packet := Gs.flatMap (fun G => cstream A r.W (packedInterval (cut s t L k) (rows s t L k) G))++F.R (crop.reg 12)
    let E : Stacks tapes A := {F with R := Function.update (Function.update F.R source []) (crop.reg 12) packet}
    let output := Gs.reverse.flatMap (fun G => cstream A r.W (packedInterval (cut s t L k)
      (rows s t L k) (diagonalProduct s t alpha p G)))
    let final : Stacks tapes A := {E with R := (Function.update (Function.update E.R diagonalQueue (F.R (crop.reg 12)))
      (diagonalRole .dst) output)}
    ∃ v' steps, v'.user = v.user ∧
      steps ≤ (bulkTargetCoreTime W V targetSpan b d r L k radius Fs.length+
        RecoveryParameterQueue.prepareTimeCost d+RecoveryNormalizePlan.generatedIntervalTimeCost d r.W (rows s t L k) Fs.length)+
        completeDiagonalBatchCost E d.B p r.W u t d.a radius (rows s t L k) Gs.length ∧
      Exec body (bulkDiagonalProgram b) (mk v S) steps (mk v' final) ∧
      List.Forall₂ (fun F D => PhaseCellInterface.ErrorOn (haloVertices s (cut s t L k) (cut s t L (k+1)))
        (packedIntervalRead p r.W (cut s t L k) (cstream A r.W (packedInterval (cut s t L k) (rows s t L k) D)))
        (fun i => ((2 : ℂ)^(inverseNormalizationShift p))⁻¹*
          resampB₀ s t (alpha : ℝ) J (fun i => value p (F i)) i)
        ((8/(2 : ℝ)^p+3*((1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p)))+
          ((32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2)/(2 : ℝ)^(inverseNormalizationShift p)))
        Fs (Gs.reverse.map (diagonalProduct s t alpha p)) ∧
      ExecWithin body (fun j z => mnSize z+j ≤ mnSize (mk v S)+depth+
        ((bulkTargetCoreReserve W V targetSpan b d r L k radius Fs.length Cprog+
          (8*(2*(4*d.B+4))+13*RecoveryNormalizePlan.generatedIntervalTimeCost d r.W (rows s t L k) Fs.length))+
          (16*diagonalPreparationCost E d.B p r.W u t d.a radius (rows s t L k)+
            (2*bulkSelectionCountsCost Gs.length (rows s t L k) r.W+
              (2*(6*((rows s t L k)*r.W)+6)+realWeightWorkspace Cdiag r.W (rows s t L k))))))
        depth (bulkDiagonalProgram b) (mk v S) steps (mk v' final) := by
  dsimp only
  intro hwide hwindow hwV hspanV hvol hVW hA hVpos wl hwl v S hready hheaders hspanRuler tail
    hqueue harchive hacc hdst hline hinput hblank hleft Cdiag Cprog depth hpush hbody hdiagPush
  let radius := localityDepth p target*PhaseCellBand.width p u
  let d := axis.ownedMasterInput target L k hnear hL ha hb
  let r := axis.ownedJob target L k hnear hL ha hb hfit Fs hF
  have hroom : 4*r.W+2 < 2^d.B :=
    axis.ownedJob_packetRoom target L k hnear hL ha hb hfit Fs hF
  let Zs := axis.ownedTargets target L k hnear hL ha hb hfit Fs
  obtain ⟨F,Gs,hGs,hfits,hq,hframe,hLframe,v₁,m₁,hv₁,hm₁,he₁,hdecoded,hvalue,ht₁⟩ :=
    bulk_published_exec_ofAxisBounds (body := body) b axis target L k hnear hL ha hb hfit
      W V targetOrigin targetSpan Fs hF hwide hwindow hwV hspanV hvol hVW hA hVpos wl hwl v S
      hready hheaders hspanRuler tail hqueue harchive hacc hdst hline hinput hblank Cprog depth hpush hbody
  have hstart : d.a+radius = cut s t L k := Nat.sub_add_cancel ha
  have hmono := cut_mono s t L (show k ≤ k+1 by omega)
  have hend : cut s t L k+rows s t L k = cut s t L (k+1) := by dsimp only [rows]; omega
  have howned : cut s t L k+rows s t L k ≤ s := by rw [hend]; omega
  have hwidth : p+3 ≤ r.W := by
    have hh := RecoveryAxisBounds.owned_normalization_width (s := s) (p := p) (u := u) (l := l) target
    change p+3 ≤ packedHaloCommonWidth p l s u (target+1) 2
    omega
  have hsquare : d.u = alpha^2 := diagonalPage_squared_parameter axis
  have hfits' : ∀ G ∈ Gs, ∀ x ∈ packedInterval (d.a+radius) (rows s t L k) G, Fits r.W x := by
    rw [hstart]; exact hfits
  obtain ⟨v₂,m₂,hv₂,hm₂,ht₂⟩ := diagonal_after_publication (body := body) b.hQ b.hA d r Fs.length radius
    (rows s t L k) alpha rfl hp13 halpha hsquare halphap (by rw [hstart]; exact howned)
    (by change p+2 ≤ r.W; omega) hroom wl hwl S F hready hinput hleft hframe hLframe Gs hGs hfits' Cdiag hdiagPush v₁
  let packet := Gs.flatMap (fun G => cstream A r.W (packedInterval (cut s t L k) (rows s t L k) G))++F.R (crop.reg 12)
  let E : Stacks tapes A := {F with R := Function.update (Function.update F.R source []) (crop.reg 12) packet}
  let output := Gs.reverse.flatMap (fun G => cstream A r.W (packedInterval (cut s t L k)
    (rows s t L k) (diagonalProduct s t alpha p G)))
  let final : Stacks tapes A := {E with R := (Function.update (Function.update E.R diagonalQueue (F.R (crop.reg 12)))
    (diagonalRole .dst) output)}
  simp only [hstart] at hm₂ ht₂
  have hnorm := axis.ownedTargets_normalized_norm_le target L k hnear hL ha hb hfit Fs hF
  let normalized := Zs.map (fun z i => ((2 : ℂ)^(inverseNormalizationShift p))⁻¹*z i)
  have hn : ∀ z ∈ normalized, ∀ i ∈ haloVertices s (cut s t L k) (cut s t L (k+1)), ‖z i‖ ≤ (3/2 : ℝ) := by
    intro z hz i hi
    change z ∈ Zs.map (fun z i => ((2 : ℂ)^(inverseNormalizationShift p))⁻¹*z i) at hz
    obtain ⟨z0,hz0,hzeq⟩ := (List.mem_map.mp hz : ∃ z0 : ZMod s → ℂ,
      z0 ∈ Zs ∧ (fun i => ((2 : ℂ)^(inverseNormalizationShift p))⁻¹*z0 i) = z)
    rw [← hzeq]
    apply hnorm z0 hz0 i
    obtain ⟨hl,hr⟩ := (mem_haloVertices _ _ i).mp hi
    apply (mem_haloVertices _ _ i).mpr
    constructor <;> omega
  have hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s (cut s t L k) (cut s t L (k+1)))
      (fun i => value p (D i)) z (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p)))
      normalized.reverse Gs := by simpa only [normalized,List.map_reverse] using hvalue
  have hactive : ∀ i ∈ haloVertices s (cut s t L k) (cut s t L (k+1)),
      cut s t L k ≤ i.val ∧ i.val < cut s t L k+rows s t L k := by
    intro i hi
    rw [hend]
    exact (mem_haloVertices _ _ i).mp hi
  have hnumeric := diagonalBatch_accuracy (t := t) (α := alpha) (w := r.W) (c := cut s t L k)
    (n := rows s t L k) (A := A) (by omega) hp13 hwidth (by omega) halphap howned
    _ hactive normalized Gs hn [] hgood
  have hglobalNumeric := axis.ownedDiagonal_global_accuracy target L k (inverseNormalizationShift p)
    hnear hL ha hb hfit Fs hF r.W (Gs.reverse.map (diagonalProduct s t alpha p)) []
    (8/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p))
    (by simpa only [normalized,List.map_map,Function.comp_def] using hnumeric)
  have he₁' : ExecWithin body (fun j z => mnSize z+j ≤ mnSize (mk v S)+depth+
      (bulkTargetCoreReserve W V targetSpan b d r L k radius Fs.length Cprog+
        (8*(2*(4*d.B+4))+13*RecoveryNormalizePlan.generatedIntervalTimeCost d r.W (rows s t L k) Fs.length)))
      depth (bulkPublishedProgram b) (mk v S) m₁ (mk v₁ E) := by
    simpa only [E,packet,List.flatMap] using ht₁
  have he₂' := ht₂ depth
  have hwhole := mn_seq_within_add he₁' he₂'
  refine ⟨F,Gs,hGs,hq,hframe,hLframe,v₂,m₁+m₂,hv₂.trans hv₁,?_,hwhole.toExec,?_,hwhole⟩
  · exact Nat.add_le_add hm₁ hm₂
  · have herr : (8/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p))+
        (2/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p) =
        8/(2 : ℝ)^p+3*((1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p)) := by ring
    rw [herr] at hglobalNumeric
    exact axis.globalHalfGridTarget_B0_accuracy (inverseNormalizationShift p) J hJ _ Fs hF
      (Gs.reverse.map (diagonalProduct s t alpha p))
      (fun D => packedIntervalRead p r.W (cut s t L k)
        (cstream A r.W (packedInterval (cut s t L k) (rows s t L k) D))) _
      (by simpa only [List.append_nil] using hglobalNumeric)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
