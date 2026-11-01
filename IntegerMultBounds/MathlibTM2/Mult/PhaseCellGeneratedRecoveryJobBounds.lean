module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRecoveryJob
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedParameterBounds

/-! Construct recovery jobs from the existing core-window parameter language.
Diagonal dominance supplies both reference solution families mathematically. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.GeneratedRecoveryJob
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s p u l target rhsExp t a b V : ℕ} [NeZero s] {α gap : ℝ} {C : ZMod s → GaussianInt}

noncomputable def ofBounds
    (h : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α gap C)
    (Fs : List (ZMod s → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ i,
      ‖value (packedHaloPrecision p l s t u target rhsExp a b) (F i)‖ ≤ (2 : ℝ)^rhsExp) :
    GeneratedRecoveryJob s := by
  let haloTarget := boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp
    (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let q := executionPrecision p l haloTarget rhsExp
  let rhs := fun r i => (value q (Fs.reverse.getD r (fun _ => 0) i)).re
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by
    have hp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by have := h.hp; omega)
    positivity
  have hex (S : Finset (ZMod s)) (r : ℕ) : ∃ x, Solves (realMatrix s t p u) S x (rhs r) :=
    solves_exists _ S _ hμ (dominates_mono _ Finset.univ _ _ (Finset.subset_univ _) h.hdom) (rhs r)
  let interior := fun r => Classical.choose (hex (haloInterior s t (PhaseCellBand.width p u) a b) r)
  let solution := fun r => Classical.choose (hex (haloVertices s a b) r)
  have hend : a+(b-a) = b := Nat.add_sub_of_le h.hab
  let H : ReplicaHaloProblem s := {
    p := p
    l := l
    t := t
    u := u
    target := haloTarget
    rhsExp := rhsExp
    origin := a
    span := b-a
    α := α
    d := gap
    Fs := Fs
    x := interior
    p_pos := by have := h.hp; omega
    s_lt_t := h.hst
    band_fit := h.hband
    u_pos := h.hu
    alpha_sq := h.hαu
    theta_pos := by
      have hp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by have := h.hp; omega)
      exact lt_of_lt_of_le (by positivity) h.hθ
    gap := h.hgap
    budget := h.hbudget
    span_fit := by rw [hend]; exact h.hbs
    rhs_bound := by
      intro r hr i
      have hr' : r < Fs.reverse.length := by simpa using hr
      rw [List.getD_eq_getElem _ _ hr']
      exact hF _ (List.mem_reverse.mp (List.getElem_mem hr')) i
    solves := by
      intro r _
      simpa only [hend] using Classical.choose_spec (hex (haloInterior s t (PhaseCellBand.width p u) a b) r) }
  exact {
    problem := H
    target := target
    solution := solution
    span_fit := h.hsep
    origin_lt := h.haLt
    precision_ge := h.hp
    width_fit := h.hwidth
    padding := h.hpad
    solves := by
      intro r _
      simpa only [H,hend,ReplicaHaloProblem.precision] using Classical.choose_spec (hex (haloVertices s a b) r)
    sizing := by dsimp only [H,haloTarget,ReplicaHaloProblem.band]; rw [hend] }

theorem ofBounds_fields
    (h : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α gap C)
    (Fs : List (ZMod s → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ i,
      ‖value (packedHaloPrecision p l s t u target rhsExp a b) (F i)‖ ≤ (2 : ℝ)^rhsExp) :
    let r := ofBounds h Fs hF
    r.problem.p = p ∧ r.problem.l = l ∧ r.problem.t = t ∧ r.problem.u = u ∧
      r.problem.origin = a ∧ r.problem.span = b-a ∧ r.problem.Fs = Fs ∧ r.target = target := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.GeneratedRecoveryJob
