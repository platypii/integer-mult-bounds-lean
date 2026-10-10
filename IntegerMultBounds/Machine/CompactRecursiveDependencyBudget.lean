import IntegerMultBounds.Machine.CompactFramedScalarGrid
import IntegerMultBounds.Machine.CompactRecursiveGridBudget
import IntegerMultBounds.Networks.ComplexRecursiveCallSchema
import IntegerMultBounds.Networks.GaussianFrameInverseGrid

/-! Dependency accounting for the actual finite complex25 call schema.
Paths choose actual call occurrences, including all preceding sibling sites.
This is a mathematical stack invariant; connecting it to the physical
recursive controller's returned precision remains a separate obligation. -/
namespace IntegerMultBounds.Machine.CompactRecursiveDependencyBudget
noncomputable section
open CompactComplexRecursiveGeometry Networks Networks.GaussianPrecision
attribute [local instance] Classical.propDecidable
attribute [local irreducible] ComplexRank25.program GlobalGrouped.program
  GlobalGrouped.stage GlobalGrouped.partialStage GlobalGrouped.invocationGroups
  GlobalGrouped.localGroups ComplexRecursiveCallSchema.calls

def siteDimensions : List ℕ := List.ofFn (fun site : ComplexRecursiveCallSchema.Occurrence =>
  ComplexPhaseRowSchedule.dimension (ComplexRecursiveCallSchema.edge site))

/-- Number of actual coordinates preceding this occurrence in the fixed
site-major residual-coordinate schedule. Equal labels retain their sites. -/
def precedingCalls (call : ComplexRecursiveCallSchema.Call) : ℕ :=
  (siteDimensions.take call.site.val).sum+call.coordinate.val

theorem siteDimensions_sum : siteDimensions.sum=ComplexRecursiveCallSchema.calls.length := by
  rw [ComplexRecursiveCallSchema.calls_length]
  exact List.sum_ofFn

private theorem ordinal_bound {n : ℕ} (dims : Fin n → ℕ) (site : Fin n)
    (coordinate : Fin (dims site)) :
    ((List.ofFn dims).take site.val).sum+coordinate.val < (List.ofFn dims).sum := by
  have hi : site.val<(List.ofFn dims).length := by simpa only [List.length_ofFn] using site.isLt
  have ht := List.take_succ_eq_append_getElem hi
  have hsum := List.sum_take_add_sum_drop (List.ofFn dims) (site.val+1)
  have hle : ((List.ofFn dims).take (site.val+1)).sum≤(List.ofFn dims).sum := by omega
  rw [ht,List.sum_append,List.sum_singleton] at hle
  have hg : ((List.ofFn dims)[site.val]'hi)=dims site := by simp only [List.getElem_ofFn]
  rw [hg] at hle
  have hc := coordinate.isLt
  omega

theorem precedingCalls_lt (call : ComplexRecursiveCallSchema.Call) :
    precedingCalls call < ComplexRecursiveCallSchema.calls.length := by
  have h := ordinal_bound (fun site : ComplexRecursiveCallSchema.Occurrence =>
    ComplexPhaseRowSchedule.dimension (ComplexRecursiveCallSchema.edge site)) call.site call.coordinate
  change precedingCalls call < siteDimensions.sum at h
  rw [siteDimensions_sum] at h
  exact h

def callCapacity : ℕ := 916333630984500000

theorem calls_le_capacity : ComplexRecursiveCallSchema.calls.length≤callCapacity := by
  rw [ComplexRecursiveCallSchema.calls_rankSum]
  exact ComplexRank25.rank_budget

/-- Scalar dependency levels, enclosing frame volumes and already returned
sibling volumes along a path in the real residual-coordinate call schema. -/
inductive Path (active : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → Prop
  | root (i : Fin (exponents active).length) :
      Path active (pieceLeft active i) (pieceExponent active i) 0 0 0
  | child {left k levels frames returned : ℕ}
      (prior : Path active left (k+1) levels frames returned)
      (call : ComplexRecursiveCallSchema.Call) :
      Path active (left+call.slot.val*arity^k) k (levels+1)
        (frames+arity^(k+1)) (returned+precedingCalls call*arity^k)

theorem Path.visit {active left k levels frames returned : ℕ}
    (path : Path active left k levels frames returned) : Visit active left k := by
  induction path with
  | root i => exact Visit.root i
  | child prior call ih => exact Visit.child ih call.slot

/-- Exact shrinking-width potential; it charges ancestor volume rather than
counting all descendants of completed siblings. -/
theorem Path.potential {active left k levels frames returned : ℕ}
    (path : Path active left k levels frames returned) :
    frames*(arity-1)+arity*arity^k ≤ arity*active := by
  induction path with
  | root i =>
    have h := piece_fits active i
    simp only [Nat.zero_mul,Nat.zero_add]
    exact Nat.mul_le_mul_left arity (by omega)
  | @child left k levels frames returned prior call ih =>
    have he : (frames+arity^(k+1))*(arity-1)+arity*arity^k =
        frames*(arity-1)+arity*arity^(k+1) := by
      rw [pow_succ]
      norm_num [arity]
      ring
    rw [he]
    exact ih

theorem Path.frames_le {active left k levels frames returned : ℕ}
    (path : Path active left k levels frames returned) : frames≤2*active := by
  have h := path.potential
  have hA : 0<arity := by decide
  have ha : arity≤2*(arity-1) := by decide
  have hm := Nat.mul_le_mul_right frames ha
  have hs : frames*(arity-1)≤arity*active := by omega
  have he : arity*frames≤arity*(2*active) := by
    calc
      _ ≤ 2*(arity-1)*frames := hm
      _ = 2*(frames*(arity-1)) := by ring
      _ ≤ 2*(arity*active) := Nat.mul_le_mul_left 2 hs
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left he hA

theorem Path.levels_le {active left k levels frames returned : ℕ}
    (path : Path active left k levels frames returned) : levels+arity^k≤active := by
  induction path with
  | root i => simpa using (show arity^(pieceExponent active i)≤active from by
      have := piece_fits active i; omega)
  | @child left k levels frames returned prior call ih =>
    have hp : 0<arity^k := pow_pos (by decide) _
    have hA : 2≤arity := by decide
    have hm := Nat.mul_le_mul_right (arity^k) hA
    rw [pow_succ] at ih
    nlinarith

theorem Path.returned_le {active left k levels frames returned : ℕ}
    (path : Path active left k levels frames returned) :
    returned≤callCapacity*frames := by
  induction path with
  | root i => simp
  | @child left k levels frames returned prior call ih =>
    have hc := (Nat.le_of_lt (precedingCalls_lt call)).trans calls_le_capacity
    have hw : arity^k≤arity^(k+1) := by
      rw [pow_succ]
      exact Nat.le_mul_of_pos_right _ (by decide : 0<arity)
    have hmul := Nat.mul_le_mul hc hw
    rw [Nat.mul_add]
    omega

/-- Every precision contribution has a coefficient fixed by the real finite
network, derived from original active geometry without a supplied depth cap. -/
theorem Path.volume_bound {active left k levels frames returned : ℕ}
    (path : Path active left k levels frames returned) :
    frames+2*returned ≤ (2+4*callCapacity)*active := by
  have hf := path.frames_le
  have hr := path.returned_le
  have hm := Nat.mul_le_mul_left callCapacity hf
  nlinarith

def volumeCoefficient := 2+4*callCapacity

/-- The signed width budget is derived from the actual occurrence path and
its active-axis geometry, rather than hypotheses bounding abstract counters. -/
theorem Path.guard {active left k levels frames returned : ℕ}
    (path : Path active left k levels frames returned) (p C : ℕ) :
    CompactRecursiveGridBudget.bound p C levels (frames+2*returned) <
      2^(p+(Nat.clog 2 (C+1)+2*volumeCoefficient)*active+1) := by
  have hl : levels≤active := by have := path.levels_le; omega
  have hv : frames+2*returned≤volumeCoefficient*active := path.volume_bound
  have hm := Nat.mul_le_mul_right (Nat.clog 2 (C+1)) hl
  have hw : CompactRecursiveGridBudget.halfWidth p C levels (frames+2*returned) ≤
      p+(Nat.clog 2 (C+1)+2*volumeCoefficient)*active+1 := by
    unfold CompactRecursiveGridBudget.halfWidth
    nlinarith
  exact (CompactRecursiveGridBudget.strict p C levels (frames+2*returned)).trans_le
    (Nat.pow_le_pow_right (by decide : 0<2) hw)

theorem prefix_rows_le (g : ℕ) :
    (CompactFramedScalarGrid.rows g).length≤ComplexFramedExecution.rows.length := by
  have h := congrArg List.length (CompactFramedScalarGrid.rows_split g)
  simp only [List.length_append] at h
  omega

/-- Paid precision increments along live dependencies have a linear active
width budget even after all preceding completed siblings are charged. -/
theorem Path.precision_bound {active left k levels frames returned : ℕ}
    (path : Path active left k levels frames returned) (n scalarRows : ℕ) :
    n+levels*scalarRows+frames+2*returned ≤ n+(scalarRows+volumeCoefficient)*active := by
  have hl : levels≤active := by have := path.levels_le; omega
  have hv : frames+2*returned≤volumeCoefficient*active := path.volume_bound
  have hm := Nat.mul_le_mul_right scalarRows hl
  nlinarith

theorem Path.actual_precision_bound {active left k levels frames returned : ℕ}
    (path : Path active left k levels frames returned) (n : ℕ) :
    n+levels*ComplexFramedExecution.rows.length+frames+2*returned ≤
      n+(ComplexFramedExecution.rows.length+volumeCoefficient)*active :=
  path.precision_bound n ComplexFramedExecution.rows.length

/-- Decode the actual source role frames from normalized stored dyadic
coefficients. This supplies the initial logical grid to scalar-prefix proofs. -/
theorem normalized_root_decode (columns p : ℕ)
    (a b : ComplexFramedExecution.Wire → BinaryColumns.Address (25^3) columns → ℤ)
    (hn : ∀ i ω,‖ButterflySigned.complexValue (a i ω) (b i ω) p‖≤1)
    (i : ComplexFramedExecution.Wire) (ω : BinaryColumns.Address (25^3) columns) :
    BoundedGrid (p+columns*(25^3)) (2^p*4^(columns*(25^3)))
      (FramedCircuit.decode
        (GroupedModuleFrames.profile (ComplexFramedExecution.frameOf columns)
          CompactFramedScalarGrid.initialLabels)
        (fun i ω => ButterflySigned.complexValue (a i ω) (b i ω) p) i ω) := by
  exact bounded_rational_label_frame_inverse ComplexPhaseBudget.coordinateSymm _ _
    (fun ω => CompactComplexScalarGrid.normalized_grid _ _ p (hn i ω)) ω

/-- A completed actual array network has a fresh endpoint grid budget. Its
internal scalar-prefix growth is absent from the returned semantic value. -/
theorem network_return_grid (columns n M : ℕ)
    (stored : ComplexFramedExecution.Wire → BinaryColumns.Arrays (25^3) columns)
    (hs : ∀ i ω,BoundedGrid n M (stored i ω)) (i : ComplexFramedExecution.Wire)
    (ω : BinaryColumns.Address (25^3) columns) :
    BoundedGrid (n+2*(columns*(25^3))) (M*4^(2*(columns*(25^3))))
      (FramedCircuit.run (ComplexFramedExecution.network columns) stored i ω) := by
  rw [ComplexFramedExecution.network_run]
  have hi := bounded_rational_label_frame_inverse ComplexPhaseBudget.coordinateSymm
    (LabelTransport.label (TensorCoordinates.coordinates 25)
      (GlobalLabels.source ComplexRank25.vector (ComplexFramedExecution.route i)))
    (stored (ComplexFramedExecution.route i)) (hs _)
  have hsign : ∀ ω,BoundedGrid (n+columns*(25^3)) (M*4^(columns*(25^3)))
      (ComplexFramedExecution.sign i •
        (ComplexFramedExecution.frameOf columns
          (GlobalLabels.source ComplexRank25.vector (ComplexFramedExecution.route i))).symm
          (stored (ComplexFramedExecution.route i)) ω) := by
    rcases i with b | b | s
    · intro ω
      simpa only [ComplexFramedExecution.sign,ComplexFramedExecution.frameOf,neg_smul,one_smul,Pi.neg_apply] using bounded_neg (hi ω)
    · intro ω
      simpa only [ComplexFramedExecution.sign,ComplexFramedExecution.frameOf,one_smul] using hi ω
    · intro ω
      simpa only [ComplexFramedExecution.sign,ComplexFramedExecution.frameOf,one_smul] using hi ω
  have ho := bounded_rational_label_frame ComplexPhaseBudget.coordinateSymm
    (LabelTransport.label (TensorCoordinates.coordinates 25)
      (GlobalLabels.sink (Labels.binary 25) ComplexRank25.vector i))
    (ComplexFramedExecution.sign i •
      (ComplexFramedExecution.frameOf columns
        (GlobalLabels.source ComplexRank25.vector (ComplexFramedExecution.route i))).symm
        (stored (ComplexFramedExecution.route i))) (by
      intro x
      rcases i with b | b | s
      · simpa only [ComplexFramedExecution.sign,neg_smul,one_smul,Pi.neg_apply] using hsign x
      · simpa only [ComplexFramedExecution.sign,one_smul] using hsign x
      · simpa only [ComplexFramedExecution.sign,one_smul] using hsign x) ω
  simpa only [ComplexFramedExecution.frameOf,Pi.smul_apply,two_mul,pow_add,Nat.add_assoc,Nat.mul_assoc] using ho

end
end IntegerMultBounds.Machine.CompactRecursiveDependencyBudget
