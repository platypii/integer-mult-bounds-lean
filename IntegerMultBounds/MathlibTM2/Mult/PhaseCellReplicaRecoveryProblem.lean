module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundarySolution
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloRecoveryBoundaryFormat

/-! Recovery RHS rows form another instance of the existing replica interior
problem, at exactly the same word format. One batched second pass can therefore
reuse the first-pass controller and shared weight construction. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s : ℕ} [NeZero s]

def ReplicaHaloProblem.recoveryTarget (H : ReplicaHaloProblem s) (target : ℕ) :=
  boundaryHaloRecoveryTarget H.p (boundaryRecoveryTarget H.p target)
    (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card

def ReplicaHaloProblem.recoveryExponent (H : ReplicaHaloProblem s) :=
  recoveryRhsExponent H.p H.rhsExp (stableInteriorExponent H.p H.rhsExp) (couplingCountExponent H.p H.u)

theorem ReplicaHaloProblem.recovery_sizing (H : ReplicaHaloProblem s) (target : ℕ)
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card) :
    H.precision = executionPrecision H.p H.l (H.recoveryTarget target) H.recoveryExponent ∧
      H.stage = executionStagePrecision H.p H.l (H.recoveryTarget target) H.recoveryExponent ∧
      H.wordWidth = executionWidth H.p H.l (H.recoveryTarget target) H.recoveryExponent := by
  obtain ⟨hq,hstage,hw⟩ := H.boundary_sizing (boundaryRecoveryTarget H.p target) htarget
  obtain ⟨hq',hstage',hw'⟩ := boundaryHaloRecoveryTarget_sizing H.p H.u H.l
    (boundaryRecoveryTarget H.p target) H.rhsExp (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card
  exact ⟨hq.trans hq',hstage.trans hstage',hw.trans hw'⟩

noncomputable def replicaRecoveryRhs (H : ReplicaHaloProblem s) (r : ℕ) (Y : ZMod s → GaussianInt) :=
  guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band H.origin (H.origin+H.span) true Y
    (H.Fs.reverse.getD r (fun _ => 0))

structure ReplicaRecoveryRow (H : ReplicaHaloProblem s) (target r : ℕ)
    (Y : ZMod s → GaussianInt) (x : ZMod s → ℝ) where
  interior : ZMod s → ℝ
  boundaryFits : ∀ i, Fits H.wordWidth (Y i)
  rhsBound : ∀ i, ‖value H.precision (replicaRecoveryRhs H r Y i)‖ ≤ (2 : ℝ)^H.recoveryExponent
  rhsFits : ∀ i, Fits H.wordWidth (replicaRecoveryRhs H r Y i)
  solves : Solves (realMatrix s H.t H.p H.u) (haloInterior s H.t H.band H.origin (H.origin+H.span))
    interior (fun i => (value H.precision (replicaRecoveryRhs H r Y i)).re)
  accept : ∀ D : ZMod s → GaussianInt,
    PhaseCellInterface.ErrorOn (haloInterior s H.t H.band H.origin (H.origin+H.span))
      (fun i => (value H.precision (D i)).re) interior (1/(2 : ℝ)^(H.recoveryTarget target)) →
    PhaseCellInterface.ErrorOn (haloVertices s H.origin (H.origin+H.span))
      (fun i => if i ∈ haloInterior s H.t H.band H.origin (H.origin+H.span)
        then (value H.precision (D i)).re else (value H.precision (Y i)).re) x (1/(2 : ℝ)^target)

theorem replicaRecoveryRow_of_boundary_solution (H : ReplicaHaloProblem s) (target r : ℕ)
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u) (hr : r < H.Fs.length)
    (solution : List GaussianInt) (x : ZMod s → ℝ)
    (hlen : solution.length = (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (hfits : ∀ z ∈ solution, Fits H.wordWidth z)
    (hsolution : ∀ i < (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card,
      ‖value H.precision (solution.getD i 0)-(x (bFoldAt s
        (haloBoundary s H.t H.band H.origin (H.origin+H.span)) i) : ℂ)‖ ≤ 3/(2 : ℝ)^boundaryRecoveryTarget H.p target ∧
      ‖value H.precision (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent H.p H.rhsExp)
    (hx : Solves (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) x
      (fun i => (value H.precision (H.Fs.reverse.getD r (fun _ => 0) i)).re)) :
    Nonempty (ReplicaRecoveryRow H target r
      (boundarySolutionField (haloBoundary s H.t H.band H.origin (H.origin+H.span)) solution) x) := by
  have hα : 0 < |H.α| := by
    have hu : (1 : ℝ) ≤ H.u := by exact_mod_cast H.u_pos
    have he := H.alpha_sq
    exact abs_pos.mpr (by intro hz; rw [hz] at he; norm_num at he; linarith)
  have hnum := haloRecovery_boundary_format_spec H.p H.u H.l target H.rhsExp H.origin (H.origin+H.span)
    hp hwidth hα H.s_lt_t (by simpa only [sq_abs] using H.alpha_sq) H.theta_lower H.gap
    (by simpa only [sq_abs] using H.budget) H.span_fit (H.dominates hp hwidth)
  obtain ⟨hq,_,hw⟩ := H.boundary_sizing (boundaryRecoveryTarget H.p target) htarget
  simp only [ReplicaHaloProblem.band] at hq hw
  dsimp only at hnum
  rw [←hq,←hw] at hnum
  obtain ⟨hbound,hfit,xI,hsolve,haccept⟩ := hnum (H.Fs.reverse.getD r (fun _ => 0)) solution x
    (H.rhs_bound r hr) hsolution hx
  exact ⟨⟨xI,boundarySolutionField_fits H.wordWidth _ solution hlen hfits,hbound,hfit,hsolve,haccept⟩⟩

structure ReplicaRecoveryBatch (H : ReplicaHaloProblem s) (target : ℕ) (X : ℕ → ZMod s → ℝ) where
  boundary : Fin H.Fs.length → ZMod s → GaussianInt
  row : ∀ r : Fin H.Fs.length, ReplicaRecoveryRow H target r.val (boundary r) (X r.val)

namespace ReplicaRecoveryBatch
variable {H : ReplicaHaloProblem s} {target : ℕ} {X : ℕ → ZMod s → ℝ}

noncomputable def inputs (B : ReplicaRecoveryBatch H target X) : List (ZMod s → GaussianInt) :=
  (List.ofFn (fun r : Fin H.Fs.length => replicaRecoveryRhs H r.val (B.boundary r))).reverse

@[simp] theorem inputs_length (B : ReplicaRecoveryBatch H target X) : B.inputs.length = H.Fs.length := by
  simp [inputs]

theorem inputs_read (B : ReplicaRecoveryBatch H target X) (r : ℕ) (hr : r < H.Fs.length) :
    B.inputs.reverse.getD r (fun _ => 0) = replicaRecoveryRhs H r (B.boundary ⟨r,hr⟩) := by
  simp only [inputs,List.reverse_reverse]
  rw [List.getD_eq_getElem _ _ (by simpa),List.getElem_ofFn]

noncomputable def problem (B : ReplicaRecoveryBatch H target X)
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card) : ReplicaHaloProblem s where
  p := H.p
  l := H.l
  t := H.t
  u := H.u
  target := H.recoveryTarget target
  rhsExp := H.recoveryExponent
  origin := H.origin
  span := H.span
  α := H.α
  d := H.d
  Fs := B.inputs
  x := fun r => if hr : r < H.Fs.length then (B.row ⟨r,hr⟩).interior else fun _ => 0
  p_pos := H.p_pos
  s_lt_t := H.s_lt_t
  band_fit := H.band_fit
  u_pos := H.u_pos
  alpha_sq := H.alpha_sq
  theta_pos := H.theta_pos
  gap := H.gap
  budget := H.budget
  span_fit := H.span_fit
  rhs_bound := by
    intro r hr i
    have hr' : r < H.Fs.length := by simpa using hr
    rw [←(H.recovery_sizing target htarget).1,B.inputs_read r hr']
    exact (B.row ⟨r,hr'⟩).rhsBound i
  solves := by
    intro r hr
    have hr' : r < H.Fs.length := by simpa using hr
    rw [dif_pos hr',←(H.recovery_sizing target htarget).1,B.inputs_read r hr']
    exact (B.row ⟨r,hr'⟩).solves

theorem problem_sizing (B : ReplicaRecoveryBatch H target X) htarget :
    (B.problem htarget).precision = H.precision ∧ (B.problem htarget).stage = H.stage ∧
      (B.problem htarget).wordWidth = H.wordWidth ∧ (B.problem htarget).metadataWidth = H.metadataWidth := by
  have hh := H.recovery_sizing target htarget
  have hq : (B.problem htarget).precision = H.precision := hh.1.symm
  have hw : (B.problem htarget).wordWidth = H.wordWidth := hh.2.2.symm
  refine ⟨hq,hh.2.1.symm,hw,?_⟩
  change weightWorkspaceWidth _ (B.problem htarget).precision (B.problem htarget).wordWidth _ _ = _
  rw [hq,hw]
  rfl

noncomputable def recoveredField (B : ReplicaRecoveryBatch H target X) (r : Fin H.Fs.length)
    (D : ZMod s → GaussianInt) : ZMod s → GaussianInt :=
  fun i => if i ∈ haloInterior s H.t H.band H.origin (H.origin+H.span) then D i else B.boundary r i

theorem accept_row (B : ReplicaRecoveryBatch H target X) htarget (r : Fin H.Fs.length)
    (D : ZMod s → GaussianInt) (hD : ReplicaHaloRowSpec (B.problem htarget) r.val D) :
    (∀ i, Fits H.wordWidth (B.recoveredField r D i)) ∧
      PhaseCellInterface.ErrorOn (haloVertices s H.origin (H.origin+H.span))
        (fun i => (value H.precision (B.recoveredField r D i)).re) (X r.val) (1/(2 : ℝ)^target) := by
  obtain ⟨_,hfits,_,herror⟩ := hD
  obtain ⟨hq,_,hw,_⟩ := B.problem_sizing htarget
  rw [hw] at hfits
  rw [hq] at herror
  have he : PhaseCellInterface.ErrorOn (haloInterior s H.t H.band H.origin (H.origin+H.span))
      (fun i => (value H.precision (D i)).re) (B.row r).interior (1/(2 : ℝ)^(H.recoveryTarget target)) := by
    change PhaseCellInterface.ErrorOn _ _ (if hr : r.val < H.Fs.length then (B.row ⟨r.val,hr⟩).interior else fun _ => 0) _ at herror
    rw [dif_pos r.isLt] at herror
    exact herror
  refine ⟨?_,?_⟩
  · intro i
    by_cases hi : i ∈ haloInterior s H.t H.band H.origin (H.origin+H.span)
    · simpa only [recoveredField,if_pos hi] using hfits i
    · simpa only [recoveredField,if_neg hi] using (B.row r).boundaryFits i
  · have hh := (B.row r).accept D he
    simpa only [recoveredField,apply_ite] using hh

end ReplicaRecoveryBatch
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
