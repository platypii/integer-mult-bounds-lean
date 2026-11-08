module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryMasterValues
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoverySolutionOrder
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseMasterInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCommonWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedRecoveryPayload
public import IntegerMultBounds.NLogN.PhaseCellTargetCoreWindow
public import IntegerMultBounds.NLogN.PhaseCellBoundary

/-! Construct the actual local recovery job for J_k from shared axis facts.
The standard constructor derives solutions and precision; no uniform source
core width, reference-solution supplier or execution hypothesis is introduced. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

/-- Analytic facts shared by all local principal windows of an axis. -/
structure RecoveryAxisBounds (s t p u l : ℕ) [NeZero s] (α gap : ℝ) : Prop where
  hp : 2 ≤ p
  hpacket : 8*p ≤ 2^u
  hα : 0 < α
  hst : s < t
  hαu : α^2 = (u : ℝ)
  hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1
  hgap : (1 : ℝ)/4 ≤ gap*((t : ℝ)/s-1)
  hbudget : α^2*gap ≤ p
  hband : PhaseCellBand.width p u ≤ s
  hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1

namespace RecoveryAxisBounds
variable {s t p u l : ℕ} [NeZero s] {α gap : ℝ}
theorem hu (h : RecoveryAxisBounds s t p u l α gap) : 1 ≤ u := by
  by_contra hn
  have hu0 : u = 0 := by omega
  have hp := h.hp
  have hpacket := h.hpacket
  rw [hu0] at hpacket
  norm_num at hpacket
  omega

theorem hdom (h : RecoveryAxisBounds s t p u l α gap) :
    SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))) := by
  let : NeZero t := ⟨Nat.ne_of_gt (lt_trans (NeZero.pos s) h.hst)⟩
  exact matrix_gap s t h.hst h.hα p u h.hp h.hpacket h.hαu h.hθ h.hgap h.hbudget

variable (h : RecoveryAxisBounds s t p u l α gap) (target L k : ℕ)
variable (hnear : t ≤ 2*s) (hL : 2 ≤ L)
variable (ha : localityDepth p target*PhaseCellBand.width p u ≤ cut s t L k)
variable (hb : cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u ≤ s)
variable (hfit : L+2*(localityDepth p target*PhaseCellBand.width p u)+PhaseCellBand.width p u ≤ s)

include h hnear hL ha hb hfit in
/-- The auxiliary bounded field in the factory parameter language is unused by
raw job construction; zero discharges that bound without an extra premise. -/
theorem ownedBounds :
    PackedHaloParameterBounds (s := s) (p := p) (l := l) (t := t) (u := u) (target := target+1) (rhsExp := 2)
      (a := cut s t L k-localityDepth p target*PhaseCellBand.width p u)
      (b := cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u)
      (V := packedHaloWorkspaceWidth p l s t u (target+1) 2
        (cut s t L k-localityDepth p target*PhaseCellBand.width p u)
        (cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u)) α gap (fun _ => 0) :=
  PackedHaloParameterBounds.ofAnalytic (target := target+1) (rhsExp := 2)
    h.hp h.hpacket h.hα h.hst h.hu h.hαu h.hθ h.hgap h.hbudget h.hband
    (owned_window_geometry s t L k _ (lt_trans (NeZero.pos s) h.hst) hnear hL ha hb).2.1 hb
    (owned_window_geometry s t L k _ (lt_trans (NeZero.pos s) h.hst) hnear hL ha hb).2.2 h.hpad
    (owned_window_separated s t L k _ _ (lt_trans (NeZero.pos s) h.hst) h.hst.le ha hfit)
    (C := fun _ => (0 : GaussianInt)) (by
      intro j
      have hz (q : ℕ) : value q (0 : GaussianInt) = 0 := by
        apply Complex.ext <;> simp [value]
      rw [hz]
      norm_num) h.hdom

noncomputable def ownedMasterInput : InverseMasterInput s :=
  InverseMasterInput.ofCuts p u l target t
    (cut s t L k-localityDepth p target*PhaseCellBand.width p u)
    (cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u)
    h.hst (Nat.le_of_lt (owned_window_geometry s t L k _ (lt_trans (NeZero.pos s) h.hst) hnear hL ha hb).2.2) hb h.hband

noncomputable def ownedJob (Fs : List (ZMod t → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1) : RawRecoveryJob s :=
  RawRecoveryJob.ofComplexBounds (h.ownedBounds target L k hnear hL ha hb hfit)
    (selectedRhsFields s Fs) (selectedRhsFields_bounded Fs hF)
    (packedHaloCommonWidth p l s u (target+1) 2)
    (packedHaloCommonWidth_fits p l s t u (target+1) 2 _ _)

variable (Fs : List (ZMod t → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1)

theorem ownedJob_profile :
    let r := h.ownedJob target L k hnear hL ha hb hfit Fs hF
    r.problem.p = p ∧ r.problem.t = t ∧
      r.problem.origin+localityDepth p target*PhaseCellBand.width p u = cut s t L k ∧
      r.problem.span = rows s t L k+2*(localityDepth p target*PhaseCellBand.width p u) ∧
      r.inputFields = complexComponentFields (selectedRhsFields s Fs) ∧ r.target = target+1 ∧
      r.W = packedHaloCommonWidth p l s u (target+1) 2 := by
  refine ⟨rfl,rfl,?_,?_,rfl,rfl,rfl⟩
  · exact Nat.sub_add_cancel ha
  · exact owned_window_span s t L k _ ha

theorem ownedJob_masterValues :
    recoveryMasterValues (h.ownedJob target L k hnear hL ha hb hfit Fs hF).problem =
      (h.ownedMasterInput target L k hnear hL ha hb).masters := by
  exact RawRecoveryJob.ofComplexBounds_masterValues
    (h.ownedBounds target L k hnear hL ha hb hfit) (selectedRhsFields s Fs)
    (selectedRhsFields_bounded Fs hF) _ (packedHaloCommonWidth_fits p l s t u (target+1) 2 _ _)

noncomputable def ownedTargets : List (ZMod s → ℂ) :=
  let bounds := h.ownedBounds target L k hnear hL ha hb hfit
  let q := packedHaloPrecision p l s t u (target+1) 2
    (cut s t L k-localityDepth p target*PhaseCellBand.width p u)
    (cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u)
  let y := fun F : ZMod s → GaussianInt =>
    GeneratedRecoveryJob.solutionMap bounds (fun i => (2 : GaussianInt)^(q-p-1)*F i)
  (selectedRhsFields s Fs).map (componentSolution y)

theorem ownedTargets_length : (h.ownedTargets target L k hnear hL ha hb hfit Fs).length = Fs.length := by
  simp [ownedTargets,selectedRhsFields]

theorem ownedJob_solutionOrder :
    let r := h.ownedJob target L k hnear hL ha hb hfit Fs hF
    (List.finRange r.problem.Fs.length).reverse.map (fun j => r.solution j.val) =
      complexComponentTargets (h.ownedTargets target L k hnear hL ha hb hfit Fs) := by
  exact RawRecoveryJob.ofComplexBounds_solutionOrder (h.ownedBounds target L k hnear hL ha hb hfit)
    (selectedRhsFields s Fs) (selectedRhsFields_bounded Fs hF) _
    (packedHaloCommonWidth_fits p l s t u (target+1) 2 _ _)

end RecoveryAxisBounds
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
