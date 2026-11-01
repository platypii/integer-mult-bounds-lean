module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedReplicaFields
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedReplicaHaloLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStableInteriorBounds

/-! The executed replica accumulator supplies actual fitting ambient fields,
not just decoded-reader accuracy. Real projection has the stable solve bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s]

theorem ReplicaHaloLoopState.packedFields (H : ReplicaHaloProblem s)
    (plan : ReplicaInteriorPlacement T) (dst : Fin T) (buffers : ReplicaLoopBuffers A)
    (F : Stacks T A) (hA : 4 ≤ A)
    (h : ReplicaHaloLoopState H plan dst buffers
      (haloLengthKeys s H.t H.band H.origin (H.origin+H.span)) [] F) :
    ∃ fields : List (ZMod s → GaussianInt), fields.length = H.Fs.length ∧
      F.R dst = (fields.map (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))).flatten++buffers.accumulatorTail ∧
      (∀ D ∈ fields, (∀ i, ‖value H.precision (D i)‖ ≤ (2 : ℝ)^interiorOutputExponent H.p H.l H.target H.rhsExp) ∧
        (∀ i, Fits H.wordWidth (D i))) ∧
      ∀ r : Fin fields.length, PhaseCellInterface.ErrorOn (haloInterior s H.t H.band H.origin (H.origin+H.span))
        (fun i => (value H.precision (fields[r.val] i)).re) (H.x r.val) (1/(2 : ℝ)^H.target) := by
  obtain ⟨rows,hn,hlen,hrange,hdst⟩ := h.rows
  have hw : 0 < H.wordWidth := by unfold ReplicaHaloProblem.wordWidth executionWidth; omega
  obtain ⟨fields,hfields,hrows,hgood⟩ := encodedRows_packedFields hw H.span_fit
    (interiorOutput_width H.p H.l H.target H.rhsExp) rows hlen hrange
  refine ⟨fields,hfields.trans hn,by rw [hdst,hrows],hgood,?_⟩
  intro r i hi
  have hri : r.val < H.Fs.length := by have hh := r.isLt; omega
  have he := ReplicaHaloLoopState.haloInterior_accuracy H plan dst buffers F h ⟨r.val,hri⟩ i hi
  have hi' := (mem_haloVertices H.origin (H.origin+H.span) i).mp (haloInterior_subset s H.t H.band H.origin (H.origin+H.span) hi)
  have hread := packedReplicaFields_read (q := H.precision) hA hw H.span_fit fields
    (fun D hD => (hgood D hD).2) buffers.accumulatorTail r i hi'
  change ‖(packedIntervalRead H.precision H.wordWidth H.origin
    ((F.R dst).drop (r.val*H.span*H.wordWidth)) i).re-H.x r.val i‖ ≤ 1/(2 : ℝ)^H.target at he
  rw [hdst,hrows,hread] at he
  exact he

omit [NeZero s] in
theorem ReplicaHaloProblem.theta_lower (H : ReplicaHaloProblem s) :
    1/(4*(H.p : ℝ)) ≤ (H.t : ℝ)/s-1 := by
  have hp : (0 : ℝ) < H.p := by exact_mod_cast H.p_pos
  have hu : (1 : ℝ) ≤ H.u := by exact_mod_cast H.u_pos
  have hbudget := H.budget
  rw [H.alpha_sq] at hbudget
  have hd : 0 < H.d := by
    have hg := H.gap
    have ht := H.theta_pos
    by_contra hn
    have hz : H.d*((H.t : ℝ)/s-1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) ht.le
    linarith
  have hdp : H.d ≤ H.p := by nlinarith only [hbudget,hu,hd]
  apply (div_le_iff₀ (show (0 : ℝ) < 4*H.p by positivity)).mpr
  have hg := H.gap
  have ht := H.theta_pos
  nlinarith only [hg,ht,hdp]

theorem ReplicaHaloProblem.dominates (H : ReplicaHaloProblem s)
    (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u) :
    SchurDominance.DominatesOn (realMatrix s H.t H.p H.u) Finset.univ (1/(8*(H.p : ℝ))) := by
  let : NeZero H.t := ⟨by have hh := H.s_lt_t; omega⟩
  have hα : H.α ≠ 0 := by
    intro hz
    have hh := H.alpha_sq
    rw [hz] at hh
    have hu : (0 : ℝ) < H.u := by exact_mod_cast H.u_pos
    norm_num at hh
    linarith
  have hαu : |H.α|^2 = (H.u : ℝ) := by rw [sq_abs]; exact H.alpha_sq
  exact matrix_gap s H.t H.s_lt_t (abs_pos.mpr hα) H.p H.u hp hwidth hαu H.theta_lower H.gap (by simpa only [sq_abs] using H.budget)

theorem ReplicaHaloProblem.realFields_stable (H : ReplicaHaloProblem s)
    (hdom : SchurDominance.DominatesOn (realMatrix s H.t H.p H.u) Finset.univ (1/(8*(H.p : ℝ))))
    (fields : List (ZMod s → GaussianInt)) (hlen : fields.length = H.Fs.length)
    (haccuracy : ∀ r : Fin fields.length,
      PhaseCellInterface.ErrorOn (haloInterior s H.t H.band H.origin (H.origin+H.span))
        (fun i => (value H.precision (fields[r.val] i)).re) (H.x r.val) (1/(2 : ℝ)^H.target)) :
    ∀ r : Fin fields.length, ∀ i ∈ haloInterior s H.t H.band H.origin (H.origin+H.span),
      ‖value H.precision (realPartWord (fields[r.val] i))‖ ≤ (2 : ℝ)^stableInteriorExponent H.p H.rhsExp := by
  intro r
  have hr : r.val < H.Fs.length := by rw [← hlen]; exact r.isLt
  exact stableInterior_norm H.p_pos (haloInterior s H.t H.band H.origin (H.origin+H.span)) hdom
    (H.Fs.reverse.getD r.val (fun _ => 0)) fields[r.val] (H.rhs_bound r.val hr) (H.x r.val)
    (H.solves r.val hr) (haccuracy r)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
