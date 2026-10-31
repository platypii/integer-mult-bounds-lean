module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedHaloReplicaClass
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReleasedReplicaResources

/-! Generated coordinate setup and retirement are shared across replicas.
Only linear origin copying is added to the released numerical class ledger. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem replicaClassReloadCost_le_shared (p l N B L s t u target rhsExp cV : ℕ)
    (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hV : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ cV*executionWidth p l target rhsExp) :
    replicaClassReloadCost p l N B L s t u target rhsExp ≤
      replicaClassReloadCost p l 0 B L s t u target rhsExp+
        (10*cV+19)*N*(B*L*executionWidth p l target rhsExp) :=
  reloadReplicaFactoryInputCost_le_shared _ _ _ _ _ _ _ _ _ _ _ _ _ hB hL
    (by unfold executionWidth; omega) hV

theorem generatedHaloReplicaClassCost_le_shared (p l N V origin span L s t u target rhsExp cV : ℕ)
    (hB : 1 ≤ (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length)
    (hL : 1 ≤ L)
    (hV : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ cV*executionWidth p l target rhsExp) :
    let band := PhaseCellBand.width p u
    let B := (haloLengthGroup s t band origin (origin+span) L).length
    generatedHaloReplicaClassCost p l N V origin span L s t u target rhsExp ≤
      preparedPairedLocalHaloClassCost V s t band origin (origin+span) L+
      releasePairedOriginPagesCost B V+replicaClassReloadCost p l 0 B L s t u target rhsExp+
      releasedAccumulatingGatheredReplicaCost p l N B V span L s t u target rhsExp+
      (10*cV+19)*N*(B*L*executionWidth p l target rhsExp) := by
  dsimp only
  have hc := replicaClassReloadCost_le_shared p l N _ L s t u target rhsExp cV hB hL hV
  unfold generatedHaloReplicaClassCost repeatableGatheredReplicaClassCost
  dsimp only
  omega

noncomputable def generatedHaloReplicaClassLinearWorkspace (hQ : SS.states ≤ Q)
    (R K p l N V origin span L s t u target rhsExp cV : ℕ) :=
  let band := PhaseCellBand.width p u
  let B := (haloLengthGroup s t band origin (origin+span) L).length
  3*preparedPairedLocalHaloClassCost V s t band origin (origin+span) L+
    2*releasePairedOriginPagesCost B V+2*replicaClassReloadCost p l 0 B L s t u target rhsExp+
    releasedReplicaLinearWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp cV+
    2*((10*cV+19)*N*(B*L*executionWidth p l target rhsExp))

theorem generatedHaloReplicaClassWorkspace_le_linear (hQ : SS.states ≤ Q)
    (R K p l N V origin span L s t u target rhsExp cV : ℕ)
    (hB : 1 ≤ (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length)
    (hL : 1 ≤ L)
    (hV : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ cV*executionWidth p l target rhsExp) :
    generatedHaloReplicaClassWorkspace (A := A) (U := U) hQ R K p l N V origin span L s t u target rhsExp ≤
      generatedHaloReplicaClassLinearWorkspace (A := A) (U := U) hQ R K p l N V origin span L s t u target rhsExp cV := by
  have hr := replicaClassReloadCost_le_shared p l N _ L s t u target rhsExp cV hB hL hV
  have hs := releasedAccumulatingGatheredReplicaWorkspace_le_linear (A := A) (U := U) hQ
    R K p l N _ V span L s t u target rhsExp cV hB hL hV
  unfold generatedHaloReplicaClassWorkspace generatedHaloReplicaClassLinearWorkspace
    repeatableGatheredReplicaClassWorkspace
  dsimp only
  omega

theorem generatedHaloReplicaClass_within_linear {T : ℕ} {P : Type}
    {body : P → Pr P T Q A U} (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    {R K p l N V origin span L s t u target rhsExp cV steps depth : ℕ}
    {z z' : Store (HΓ (T := T) A) (HS T Q A U)}
    (he : ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      generatedHaloReplicaClassWorkspace (A := A) (U := U) hQ R K p l N V origin span L s t u target rhsExp)
      depth (generatedHaloReplicaClass plan dst hR hQ) z steps z')
    (hB : 1 ≤ (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length)
    (hL : 1 ≤ L)
    (hV : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ cV*executionWidth p l target rhsExp) :
    ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      generatedHaloReplicaClassLinearWorkspace (A := A) (U := U) hQ R K p l N V origin span L s t u target rhsExp cV)
      depth (generatedHaloReplicaClass plan dst hR hQ) z steps z' := by
  apply he.mono
  intro d state hs
  have hb := generatedHaloReplicaClassWorkspace_le_linear (A := A) (U := U) hQ
    R K p l N V origin span L s t u target rhsExp cV hB hL hV
  omega

end IntegerMultBounds.MathlibTM2.Cost
