import IntegerMultBounds.Networks.ComplexPhaseBudget
import IntegerMultBounds.Networks.BinaryColumnFrame
import IntegerMultBounds.Networks.GroupedModuleFrames
import IntegerMultBounds.Networks.FramedFactorExecution

/-! Actual framed execution of the size-25 complex network on complex arrays.
Rational gates retain their original graph and coefficients. The theorem
identifies the whole physical run with the signed bank exchange conjugated
by its actual endpoint frames, including every scratch wire. -/

namespace IntegerMultBounds.Networks.ComplexFramedExecution

open ComplexRank25 ComplexPhaseBudget

abbrev Wire := Wires.ComplexRole 25

/-- The actual signed exchange sends each output bank to the other input bank. -/
def route : Wire → Wire
  | Sum.inl b => Sum.inr (Sum.inl b)
  | Sum.inr (Sum.inl b) => Sum.inl b
  | Sum.inr (Sum.inr s) => Sum.inr (Sum.inr s)

def sign : Wire → ℚ
  | Sum.inl _ => -1
  | _ => 1

noncomputable def rows := GroupedCircuit.compileGroups (program.map GroupedFrames.Vertex.group)

/-- The exact existing rational scalar program, in routed form. -/
theorem scalar_route (x : Wire → ℚ) : Circuit.run rows x = fun i => sign i * x (route i) := by
  have he := GlobalGrouped.complexProgram_run triples pairs
    (fun b => x (Sum.inl b)) (fun b => x (Sum.inr (Sum.inl b)))
    (fun s => x (Sum.inr (Sum.inr s)))
  have hx : GlobalCircuit.contents (fun b => x (Sum.inl b))
      (fun b => x (Sum.inr (Sum.inl b))) (fun s => x (Sum.inr (Sum.inr s))) = x := by
    funext i
    rcases i with b | b | s <;> rfl
  rw [hx] at he
  unfold rows
  rw [program_groups, GroupedCircuit.compileGroups_run, he]
  funext i
  rcases i with b | b | s <;> simp [GlobalCircuit.contents, sign, route]

/-- The same actual complex column frame viewed as a rational-linear frame. -/
noncomputable def frameOf (k : ℕ) (U : Label) :
    FramedCircuit.Frame ℚ (BinaryColumns.Arrays (25 ^ 3) k) :=
  BinaryColumnFrame.rationalLabelFrame coordinateSymm k
    (LabelTransport.label (TensorCoordinates.coordinates 25) U)

/-- The complete physical grouped schedule and terminal edge instructions. -/
noncomputable def network (k : ℕ) :=
  GroupedModuleFrames.network (frameOf k) wires (GlobalLabels.source vector)
    (GlobalLabels.sink (Labels.binary 25) vector) program

/-- Full physical execution on arbitrary complex arrays, including dirty
scratch, has exactly the specified endpoint-frame signed exchange. -/
theorem network_run (k : ℕ) (stored : Wire → BinaryColumns.Arrays (25 ^ 3) k) :
    FramedCircuit.run (network k) stored = fun i =>
      frameOf k (GlobalLabels.sink (Labels.binary 25) vector i)
        (sign i • (frameOf k (GlobalLabels.source vector (route i))).symm (stored (route i))) := by
  apply GroupedModuleFrames.network_signed_route (frameOf k) wires wires_complete
    (GlobalLabels.source vector) (GlobalLabels.sink (Labels.binary 25) vector) program route sign
  intro x
  have hs := scalar_route x
  rwa [rows, GroupedCircuit.compileGroups_run] at hs

abbrev Directions := List (List (ZMod 4 × BinaryWalsh.Address (25 ^ 3)))

noncomputable def factorMaps (k : ℕ) (directions : Directions) :
    List (List (BinaryColumns.Arrays (25 ^ 3) k →ₗ[ℚ] BinaryColumns.Arrays (25 ^ 3) k)) :=
  directions.map (fun gs => gs.map (fun g => (BinaryColumns.vectorFactor k g).restrictScalars ℚ))

private theorem restrict_prod {k : ℕ} (fs : List (BinaryColumns.Operator (25 ^ 3) k)) :
    (fs.map (fun f => f.restrictScalars ℚ)).prod = fs.prod.restrictScalars ℚ := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    rfl

/-- The numerical edge-factor family certifies the precise edge instructions
of the physical compiler, after restricting the identical operators to rationals. -/
theorem factor_certificate (k : ℕ) (directions : Directions) (hd : Realizes directions) :
    List.Forall₂ (fun op fs => fs.prod = op)
      (FramedFactorExecution.edgeOperators (network k)) (factorMaps k directions) := by
  apply FramedFactorExecution.certificate_of_edgePairs
  rw [network, GroupedModuleFrames.edgePairs_network]
  rw [factorMaps, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  apply List.Forall₂.imp _ hd
  intro p gs hg
  change (gs.map (fun g => (BinaryColumns.vectorFactor k g).restrictScalars ℚ)).prod =
    (BinaryRankFactors.edgeOperator coordinateSymm k
      (LabelTransport.label (TensorCoordinates.coordinates 25) p.1)
      (LabelTransport.label (TensorCoordinates.coordinates 25) p.2)).restrictScalars ℚ
  rw [hg.2 k]
  simpa only [List.map_map, Function.comp_def] using restrict_prod (gs.map (BinaryColumns.vectorFactor k))

/-- Executable finite instructions place each factor on the original wire,
retaining all scalar gates in their original order. These are array operations. -/
noncomputable def lowered (k : ℕ) (directions : Directions) :=
  FramedFactorExecution.lower (network k) (factorMaps k directions)

theorem lowered_run (k : ℕ) (directions : Directions) (hd : Realizes directions)
    (stored : Wire → BinaryColumns.Arrays (25 ^ 3) k) :
    FramedFactorExecution.run (lowered k directions) stored = fun i =>
      frameOf k (GlobalLabels.sink (Labels.binary 25) vector i)
        (sign i • (frameOf k (GlobalLabels.source vector (route i))).symm (stored (route i))) := by
  rw [lowered, FramedFactorExecution.run_lower _ _ (factor_certificate k directions hd), network_run]

theorem lowered_count (k : ℕ) (directions : Directions) (hd : Realizes directions) :
    FramedFactorExecution.linearCount (lowered k directions) = (directions.map List.length).sum := by
  rw [lowered, FramedFactorExecution.linearCount_lower _ _ (factor_certificate k directions hd)]
  simp only [factorMaps, List.map_map, Function.comp_def, List.length_map]

/-- The scalar gate list is literally unchanged and independent of column count. -/
theorem lowered_gates (k : ℕ) (directions : Directions) :
    FramedFactorExecution.gates (lowered k directions) = rows := by
  rw [lowered, FramedFactorExecution.gates_lower, network,
    FramedFactorExecution.originalGates_network]
  rfl

/-- Total array-instruction count includes every original scalar gate. -/
theorem lowered_length (k : ℕ) (directions : Directions) (hd : Realizes directions) :
    (lowered k directions).length = (directions.map List.length).sum + rows.length := by
  rw [FramedFactorExecution.length_eq, lowered_count k directions hd, lowered_gates]

/-- One fixed finite kernel family gives the entire physical array schedule
for every column count, with actual executed factor count equal to its rank. -/
theorem exists_uniform_execution :
    ∃ directions : Directions, Realizes directions ∧
      ∀ k, FramedFactorExecution.linearCount (lowered k directions) = rankSum ∧
        ∀ stored : Wire → BinaryColumns.Arrays (25 ^ 3) k,
          FramedFactorExecution.run (lowered k directions) stored = fun i =>
            frameOf k (GlobalLabels.sink (Labels.binary 25) vector i)
              (sign i • (frameOf k (GlobalLabels.source vector (route i))).symm (stored (route i))) := by
  obtain ⟨directions, hd, hlen⟩ := exists_uniform_factors
  exact ⟨directions, hd, fun k => ⟨(lowered_count k directions hd).trans hlen, lowered_run k directions hd⟩⟩

/-- The executed physical array-factor schedule meets the numerical budget
uniformly in column count. This counts array instructions, not tape steps. -/
theorem exists_uniform_execution_budget :
    ∃ directions : Directions, Realizes directions ∧
      ∀ k, FramedFactorExecution.linearCount (lowered k directions) ≤ 916333630984500000 ∧
        (FramedFactorExecution.linearCount (lowered k directions) : ℝ) / 58645352620000 <
          (15625 : ℝ) ^ Parameters.sigma ∧
        ∀ stored : Wire → BinaryColumns.Arrays (25 ^ 3) k,
          FramedFactorExecution.run (lowered k directions) stored = fun i =>
            frameOf k (GlobalLabels.sink (Labels.binary 25) vector i)
              (sign i • (frameOf k (GlobalLabels.source vector (route i))).symm (stored (route i))) := by
  obtain ⟨directions, hd, he⟩ := exists_uniform_execution
  refine ⟨directions, hd, fun k => ?_⟩
  obtain ⟨hc, hr⟩ := he k
  exact ⟨hc ▸ rank_budget, hc ▸ branching_bound, hr⟩

end IntegerMultBounds.Networks.ComplexFramedExecution
