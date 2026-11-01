module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedReplicaHaloLoop
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaHaloLoopResources
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellHaloLocalPadding

/-! Separate shared class factories from replicated local traffic, then sum the
actual initialized pass using local halo volume and at most six span scans. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {s Q A : ℕ} {U : Type}

noncomputable def replicaHaloTrafficFactor (hQ : SS.states ≤ Q) (R cV : ℕ) :=
  2114+2*mnProgPush (generateReplicaWeightPage (P₀ := Empty) (Q := Q) (A := A) (U := U))+
    cachedOriginsTrafficFactor (P₀ := Empty) (A := A) (U := U) hQ R cV+2*(10*cV+19)

theorem generatedHaloReplicaLinearWorkspace_le_affine (hQ : SS.states ≤ Q)
    (R K p l N V origin span L s t u target rhsExp cV : ℕ) :
    let w := executionWidth p l target rhsExp
    let B := (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length
    generatedHaloReplicaClassLinearWorkspace (A := A) (U := U) hQ R K p l N V origin span L s t u target rhsExp cV ≤
      generatedHaloReplicaClassLinearWorkspace (A := A) (U := U) hQ R K p l 0 V origin span L s t u target rhsExp cV+
        replicaHaloTrafficFactor (A := A) (U := U) hQ R cV*N*(B*(L+2^l)*w+span*w+1) := by
  dsimp only
  let B := (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length
  let w := executionWidth p l target rhsExp
  have hrow : B*L*w ≤ B*(L+2^l)*w+span*w+1 := by
    have hh := Nat.mul_le_mul_right w (Nat.mul_le_mul_left B (Nat.le_add_right L (2^l)))
    omega
  have ht := Nat.mul_le_mul_left (2*(10*cV+19)*N) hrow
  unfold generatedHaloReplicaClassLinearWorkspace releasedReplicaLinearWorkspace
    generatedPublishedReplicaLinearWorkspace gatheredInteriorLinearWorkspace replicaHaloTrafficFactor
  dsimp only
  dsimp only [B,w] at ht
  nlinarith only [ht]

noncomputable def replicaHaloKeySharedWorkspace (H : ReplicaHaloProblem s) (hQ : SS.states ≤ Q)
    (R K L cV : ℕ) :=
  2*replicaLengthKeyParserCost H.metadataWidth L+
    if H.offsets L = [] then
      3*preparedPairedLocalHaloClassCost H.metadataWidth s H.t H.band H.origin (H.origin+H.span) L+40
    else generatedHaloReplicaClassLinearWorkspace (A := A) (U := U) hQ R K H.p H.l 0 H.metadataWidth
      H.origin H.span L s H.t H.u H.target H.rhsExp cV

theorem replicaHaloCandidateWorkspace_le_affine (H : ReplicaHaloProblem s) (hQ : SS.states ≤ Q)
    (R K L cV : ℕ) (hL : 0 < L) (hV : H.metadataWidth ≤ cV*H.wordWidth) :
    H.keyWorkspace (A := A) (U := U) hQ R K L ≤
      replicaHaloKeySharedWorkspace (A := A) (U := U) H hQ R K L cV+
        replicaHaloTrafficFactor (A := A) (U := U) hQ R cV*H.Fs.length*
          ((haloLengthGroup s H.t H.band H.origin (H.origin+H.span) L).length*(L+2^H.l)*H.wordWidth+H.span*H.wordWidth+1) := by
  apply (replicaHaloCandidateWorkspace_le_linear H hQ R K L cV hL hV).trans
  by_cases hempty : H.offsets L = []
  · simp only [replicaHaloCandidateLinearWorkspace,replicaHaloKeySharedWorkspace,hempty,ite_true]
    exact Nat.le_add_right _ _
  · simp only [replicaHaloCandidateLinearWorkspace,replicaHaloKeySharedWorkspace,replicaHaloKeyLinearWorkspace,hempty,ite_false]
    have hh := generatedHaloReplicaLinearWorkspace_le_affine (A := A) (U := U) hQ
      R K H.p H.l H.Fs.length H.metadataWidth H.origin H.span L s H.t H.u H.target H.rhsExp cV
    simpa only [ReplicaHaloProblem.band,ReplicaHaloProblem.wordWidth,Nat.add_assoc] using
      Nat.add_le_add_left hh (2*replicaLengthKeyParserCost H.metadataWidth L)

theorem replicaHaloCandidateLoopWorkspace_le_affine (H : ReplicaHaloProblem s) (hQ : SS.states ≤ Q)
    (R K cV : ℕ) (keys : List ℕ) (hpositive : ∀ L ∈ keys, 0 < L)
    (hV : H.metadataWidth ≤ cV*H.wordWidth) :
    (keys.map (H.keyWorkspace (A := A) (U := U) hQ R K)).sum ≤
      (keys.map (fun L => replicaHaloKeySharedWorkspace (A := A) (U := U) H hQ R K L cV)).sum+
      (keys.map (fun L => replicaHaloTrafficFactor (A := A) (U := U) hQ R cV*H.Fs.length*
        ((haloLengthGroup s H.t H.band H.origin (H.origin+H.span) L).length*(L+2^H.l)*H.wordWidth+H.span*H.wordWidth+1))).sum := by
  induction keys with
  | nil => simp
  | cons L keys ih =>
    have hh := replicaHaloCandidateWorkspace_le_affine (A := A) (U := U) H hQ R K L cV (hpositive L (by simp)) hV
    have ht := ih (fun J hJ => hpositive J (by simp [hJ]))
    simp only [List.map_cons,List.sum_cons]
    omega

theorem replicaHaloCandidateLoopWorkspace_le_local [NeZero s] (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (R K cV : ℕ) (hgap : H.t-s ≤ s)
    (hl : H.l = haloInverseRingLog s H.t) (hV : H.metadataWidth ≤ cV*H.wordWidth) :
    let keys := haloLengthKeys s H.t H.band H.origin (H.origin+H.span)
    (keys.map (H.keyWorkspace (A := A) (U := U) hQ R K)).sum ≤
      (keys.map (fun L => replicaHaloKeySharedWorkspace (A := A) (U := U) H hQ R K L cV)).sum+
      replicaHaloTrafficFactor (A := A) (U := U) hQ R cV*H.Fs.length*
        (((haloInterior s H.t H.band H.origin (H.origin+H.span)).card+8*H.span+8*(s/(H.t-s)+1))*H.wordWidth+
          6*(H.span*H.wordWidth+1)) := by
  dsimp only
  have hc := replicaHaloCandidateLoopWorkspace_le_affine (A := A) (U := U) H hQ R K cV
    (haloLengthKeys s H.t H.band H.origin (H.origin+H.span))
    (fun L hL => of_decide_eq_true (List.mem_filter.mp hL).2) hV
  have ht := haloLengthKeys_localTraffic_le H.s_lt_t hgap H.band H.origin (H.origin+H.span)
    (replicaHaloTrafficFactor (A := A) (U := U) hQ R cV*H.Fs.length) H.wordWidth (by omega)
  simp only [Nat.add_sub_cancel_left,← hl] at ht
  exact hc.trans (Nat.add_le_add_left ht _)

noncomputable def initializedReplicaHaloWorkspace (H : ReplicaHaloProblem s) (hQ : SS.states ≤ Q)
    (R K : ℕ) :=
  2*allocateZeroLineCost H.Fs.length (H.span*H.wordWidth)+
    (3*placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth+
      ((haloLengthKeys s H.t H.band H.origin (H.origin+H.span)).map
        (H.keyWorkspace (A := A) (U := U) hQ R K)).sum)

noncomputable def initializedReplicaHaloLocalWorkspace (H : ReplicaHaloProblem s) (hQ : SS.states ≤ Q)
    (R K cV : ℕ) :=
  let keys := haloLengthKeys s H.t H.band H.origin (H.origin+H.span)
  2*allocateZeroLineCost H.Fs.length (H.span*H.wordWidth)+
    (3*placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth+
      ((keys.map (fun L => replicaHaloKeySharedWorkspace (A := A) (U := U) H hQ R K L cV)).sum+
        replicaHaloTrafficFactor (A := A) (U := U) hQ R cV*H.Fs.length*
          (((haloInterior s H.t H.band H.origin (H.origin+H.span)).card+8*H.span+8*(s/(H.t-s)+1))*H.wordWidth+
            6*(H.span*H.wordWidth+1))))

theorem initializedReplicaHaloWorkspace_le_local [NeZero s] (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (R K cV : ℕ) (hgap : H.t-s ≤ s)
    (hl : H.l = haloInverseRingLog s H.t) (hV : H.metadataWidth ≤ cV*H.wordWidth) :
    initializedReplicaHaloWorkspace (A := A) (U := U) H hQ R K ≤
      initializedReplicaHaloLocalWorkspace (A := A) (U := U) H hQ R K cV :=
  Nat.add_le_add_left (Nat.add_le_add_left (replicaHaloCandidateLoopWorkspace_le_local H hQ R K cV hgap hl hV) _) _

theorem initializedReplicaHaloLoop_within_local [NeZero s] {T : ℕ} {P : Type}
    {body : P → Pr P T Q A U} (H : ReplicaHaloProblem s)
    (plan : ReplicaInteriorPlacement T) (dst : Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    {R K cV depth steps : ℕ} {z z' : Store (HΓ (T := T) A) (HS T Q A U)}
    (he : ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      (2*allocateZeroLineCost H.Fs.length (H.span*H.wordWidth)+
        (3*placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth+
          ((haloLengthKeys s H.t H.band H.origin (H.origin+H.span)).map
            (H.keyWorkspace (A := A) (U := U) hQ R K)).sum))) depth
      (initializedReplicaHaloLoop plan dst hR hQ) z steps z')
    (hgap : H.t-s ≤ s) (hl : H.l = haloInverseRingLog s H.t)
    (hV : H.metadataWidth ≤ cV*H.wordWidth) :
    ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      initializedReplicaHaloLocalWorkspace (A := A) (U := U) H hQ R K cV) depth
      (initializedReplicaHaloLoop plan dst hR hQ) z steps z' := by
  have hc := replicaHaloCandidateLoopWorkspace_le_local (A := A) (U := U) H hQ R K cV hgap hl hV
  apply he.mono
  intro d state hs
  dsimp only [initializedReplicaHaloLocalWorkspace]
  omega

end IntegerMultBounds.MathlibTM2.Cost
