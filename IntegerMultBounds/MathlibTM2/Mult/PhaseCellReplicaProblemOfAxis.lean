module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaHaloProblem
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTargetOwnedRecoveryJob

/-! Instantiate the existing cached replica language from shared axis bounds.
The reference solutions are consequences of diagonal dominance, not inputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

namespace RecoveryAxisBounds
variable {s t p u l : ℕ} [NeZero s] {α d : ℝ}

/-- A single interior inverse supplies all mathematical replica references. -/
noncomputable def replicaProblem (axis : RecoveryAxisBounds s t p u l α d)
    (target rhsExp origin span : ℕ) (hfit : origin+span ≤ s)
    (Fs : List (ZMod s → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ k,
      ‖value (executionPrecision p l target rhsExp) (F k)‖ ≤ (2 : ℝ)^rhsExp) :
    ReplicaHaloProblem s := by
  have hp : (0 : ℝ) < p := by
    exact_mod_cast (show 0 < p by have := axis.hp; omega)
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by positivity
  let I := haloInterior s t (PhaseCellBand.width p u) origin (origin+span)
  have hex (rhs : ZMod s → ℝ) : ∃ x, Solves (realMatrix s t p u) I x rhs :=
    solves_exists _ I _ hμ
      (dominates_mono _ Finset.univ _ _ (Finset.subset_univ _) axis.hdom) rhs
  exact {
    p := p, l := l, t := t, u := u, target := target, rhsExp := rhsExp
    origin := origin, span := span, α := α, d := d, Fs := Fs
    x := fun r => Classical.choose (hex (fun k =>
      (value (executionPrecision p l target rhsExp) (Fs.reverse.getD r (fun _ => 0) k)).re))
    p_pos := by have := axis.hp; omega
    s_lt_t := axis.hst
    band_fit := axis.hband
    u_pos := axis.hu
    alpha_sq := axis.hαu
    theta_pos := lt_of_lt_of_le (by positivity) axis.hθ
    gap := axis.hgap
    budget := axis.hbudget
    span_fit := hfit
    rhs_bound := by
      intro r hr k
      have hr' : r < Fs.reverse.length := by simpa using hr
      rw [List.getD_eq_getElem _ _ hr']
      exact hF _ (List.mem_reverse.mp (List.getElem_mem hr')) k
    solves := by intro r _; exact Classical.choose_spec (hex _) }

end RecoveryAxisBounds
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
