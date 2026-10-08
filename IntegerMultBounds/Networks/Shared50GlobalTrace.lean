import IntegerMultBounds.Networks.Shared50GlobalCircuit
import IntegerMultBounds.Networks.Shared50ReuseLabels

/-! Concrete boundary profiles for the actual padded two-bank schedule.
Unused outer-stage scratch retains its stage-one tail through the middle stage.
The stage-three attachment uses the proved neighbor-permutation inclusion on
the exact reused physical roles. These are endpoint and boundary-trace facts;
local invocation traces and their scalar incidence connection remain separate. -/

namespace IntegerMultBounds.Networks.Shared50GlobalTrace

noncomputable section
open scoped TensorProduct
open Module MotifLabels
open Shared50GlobalBudget (Triple Address Side Control Invocation Scratch World Ambient)
open Shared50ReuseLabels (D vector pi factor_symm factor_nondegenerate vector_norm cubeForm cube_symm cube_nondegenerate)

abbrev Label := Submodule ℚ Ambient
abbrev Profile := World → Label
abbrev source : Profile := Shared50GlobalBudget.source
abbrev sink : Profile := Shared50GlobalBudget.sink

abbrev firstGeometry := StageLabels.firstGeometry D factor_symm factor_nondegenerate
abbrev secondGeometry (q : Triple × Triple) :=
  StageLabels.secondGeometry D factor_symm factor_nondegenerate (vector q.1) (vector_norm q.1)
abbrev thirdGeometry (q : Triple × Triple) :=
  StageLabels.thirdGeometry D factor_symm factor_nondegenerate
    (vector q.1) (vector q.2) (vector_norm q.1) (vector_norm q.2)

abbrev xInput := GlobalLabels.xInput D factor_symm factor_nondegenerate vector vector_norm
abbrev yInput := GlobalLabels.yInput D factor_symm factor_nondegenerate vector vector_norm
abbrev xOutput := GlobalLabels.xOutput D factor_symm factor_nondegenerate vector vector_norm
abbrev yOutput := GlobalLabels.yOutput D factor_symm factor_nondegenerate vector vector_norm

/-- The next outer invocation attached to the old auxiliary key. -/
def thirdKey (q : Triple × Triple) : Triple × Triple := (q.2, pi q.1)

def common (j : Fin 3) (q : Triple × Triple) : Label :=
  if j = 0 then GlobalLabels.firstLabel vector q firstGeometry.common
  else if j = 1 then GlobalLabels.secondLabel vector q (secondGeometry q).common
  else GlobalLabels.thirdLabel q (thirdGeometry q).common

def full (j : Fin 3) (q : Triple × Triple) : Label :=
  if j = 0 then GlobalLabels.firstLabel vector q firstGeometry.full
  else if j = 1 then GlobalLabels.secondLabel vector q (secondGeometry q).full
  else GlobalLabels.thirdLabel q (thirdGeometry q).full

/-- Initial and final auxiliary profiles retain the other bank verbatim. -/
def scratchInput (j : Fin 3) (k : Invocation) : Label :=
  if j = 0 then if k.1 = 0 then common 0 k.2 else ⊥
  else if j = 1 then if k.1 = 0 then full 0 k.2 else common 1 k.2
  else if k.1 = 0 then common 2 (thirdKey k.2) else full 1 k.2

def scratchOutput (j : Fin 3) (k : Invocation) : Label :=
  if j = 0 then if k.1 = 0 then full 0 k.2 else ⊥
  else if j = 1 then if k.1 = 0 then full 0 k.2 else full 1 k.2
  else if k.1 = 0 then full 2 (thirdKey k.2) else full 1 k.2

def input (j : Fin 3) : Profile :=
  Sum.elim (xInput j) (Sum.elim (yInput j) (fun s => scratchInput j s.1))

def output (j : Fin 3) : Profile :=
  Sum.elim (xOutput j) (Sum.elim (yOutput j) (fun s => scratchOutput j s.1))

/-- The join uses precisely the physical key used by the actual scalar list. -/
theorem thirdKey_reuses (q : Triple × Triple) :
    Shared50GlobalCircuit.scratchKey 2 (thirdKey q) = Shared50GlobalCircuit.scratchKey 0 q :=
  Shared50GlobalCircuit.scratchKey_reuse q.1 q.2

theorem reused_boundary (q : Triple × Triple) : full 0 q ≤ common 2 (thirdKey q) := by
  change GlobalLabels.firstLabel vector q firstGeometry.full ≤
    GlobalLabels.thirdLabel (thirdKey q) (thirdGeometry (thirdKey q)).common
  dsimp only [thirdKey, thirdGeometry]
  rw [Shared50ReuseLabels.tail_boundary, Shared50ReuseLabels.head_boundary]
  exact Shared50ReuseLabels.tail_le_head q.1 q.2

/-- All four physical attachment boundaries are increasing. -/
theorem source_le_input (i : World) : source i ≤ input 0 i := by
  rcases i with b | b | scratch
  · exact le_of_eq (GlobalLabels.x_source (A := Side) (C := Control)
      D factor_symm factor_nondegenerate vector vector_norm b).symm
  · exact le_of_eq (GlobalLabels.y_source (A := Side) (C := Control)
      D factor_symm factor_nondegenerate vector vector_norm b).symm
  · exact bot_le

theorem first_le_second (i : World) : output 0 i ≤ input 1 i := by
  rcases i with b | b | ⟨⟨bank,q⟩,r⟩
  · exact le_of_eq (GlobalLabels.x_one_two D factor_symm factor_nondegenerate vector vector_norm b)
  · exact le_of_eq (GlobalLabels.y_one_two D factor_symm factor_nondegenerate vector vector_norm b)
  · fin_cases bank <;> simp [output,input,scratchInput,scratchOutput]

theorem second_le_third (i : World) : output 1 i ≤ input 2 i := by
  rcases i with b | b | ⟨⟨bank,q⟩,r⟩
  · exact le_of_eq (GlobalLabels.x_two_three D factor_symm factor_nondegenerate vector vector_norm b)
  · exact le_of_eq (GlobalLabels.y_two_three D factor_symm factor_nondegenerate vector vector_norm b)
  · fin_cases bank
    · exact reused_boundary q
    · exact le_rfl

theorem output_le_sink (i : World) : output 2 i ≤ sink i := by
  rcases i with b | b | scratch
  · exact le_of_eq (GlobalLabels.x_sink (A := Side) (C := Control)
      D factor_symm factor_nondegenerate vector vector_norm b)
  · exact le_of_eq (GlobalLabels.y_sink (A := Side) (C := Control)
      D factor_symm factor_nondegenerate vector vector_norm b)
  · exact le_top

theorem common_nondegenerate (j : Fin 3) (q : Triple × Triple) :
    (cubeForm.restrict (common j q)).Nondegenerate := by
  fin_cases j
  · exact GlobalLabels.firstLabel_nondegenerate D vector vector_norm q _ firstGeometry.common_nondegenerate
  · exact GlobalLabels.secondLabel_nondegenerate D vector vector_norm q _ (secondGeometry q).common_nondegenerate
  · exact GlobalLabels.thirdLabel_nondegenerate D q _ (thirdGeometry q).common_nondegenerate

theorem full_nondegenerate (j : Fin 3) (q : Triple × Triple) :
    (cubeForm.restrict (full j q)).Nondegenerate := by
  fin_cases j
  · exact GlobalLabels.firstLabel_nondegenerate D vector vector_norm q _ firstGeometry.full_nondegenerate
  · exact GlobalLabels.secondLabel_nondegenerate D vector vector_norm q _ (secondGeometry q).full_nondegenerate
  · exact GlobalLabels.thirdLabel_nondegenerate D q _ (thirdGeometry q).full_nondegenerate

theorem xInput_nondegenerate (j : Fin 3) (b : Address) :
    (cubeForm.restrict (xInput j b)).Nondegenerate := by
  fin_cases j
  · exact GlobalLabels.firstLabel_nondegenerate D vector vector_norm (b.2.1,b.2.2) _
      (firstGeometry.xIn_nondegenerate (vector b.1) (vector_norm b.1))
  · exact GlobalLabels.secondLabel_nondegenerate D vector vector_norm (b.1,b.2.2) _
      ((secondGeometry (b.1,b.2.2)).xIn_nondegenerate (vector b.2.1) (vector_norm b.2.1))
  · exact GlobalLabels.thirdLabel_nondegenerate D (b.1,b.2.1) _
      ((thirdGeometry (b.1,b.2.1)).xIn_nondegenerate (vector b.2.2) (vector_norm b.2.2))

theorem yInput_nondegenerate (j : Fin 3) (b : Address) :
    (cubeForm.restrict (yInput j b)).Nondegenerate := by
  fin_cases j
  · exact GlobalLabels.firstLabel_nondegenerate D vector vector_norm (b.2.1,b.2.2) _
      (firstGeometry.yIn_nondegenerate (vector b.1) (vector_norm b.1))
  · exact GlobalLabels.secondLabel_nondegenerate D vector vector_norm (b.1,b.2.2) _
      ((secondGeometry (b.1,b.2.2)).yIn_nondegenerate (vector b.2.1) (vector_norm b.2.1))
  · exact GlobalLabels.thirdLabel_nondegenerate D (b.1,b.2.1) _
      ((thirdGeometry (b.1,b.2.1)).yIn_nondegenerate (vector b.2.2) (vector_norm b.2.2))

theorem xOutput_nondegenerate (j : Fin 3) (b : Address) :
    (cubeForm.restrict (xOutput j b)).Nondegenerate := by
  fin_cases j
  · exact GlobalLabels.firstLabel_nondegenerate D vector vector_norm (b.2.1,b.2.2) _
      (firstGeometry.full_nondegenerate)
  · exact GlobalLabels.secondLabel_nondegenerate D vector vector_norm (b.1,b.2.2) _
      ((secondGeometry (b.1,b.2.2)).full_nondegenerate)
  · exact GlobalLabels.thirdLabel_nondegenerate D (b.1,b.2.1) _
      ((thirdGeometry (b.1,b.2.1)).full_nondegenerate)

theorem yOutput_nondegenerate (j : Fin 3) (b : Address) :
    (cubeForm.restrict (yOutput j b)).Nondegenerate := by
  fin_cases j
  · exact GlobalLabels.firstLabel_nondegenerate D vector vector_norm (b.2.1,b.2.2) _
      (firstGeometry.yOut_nondegenerate (vector b.1) (vector_norm b.1))
  · exact GlobalLabels.secondLabel_nondegenerate D vector vector_norm (b.1,b.2.2) _
      ((secondGeometry (b.1,b.2.2)).yOut_nondegenerate (vector b.2.1) (vector_norm b.2.1))
  · exact GlobalLabels.thirdLabel_nondegenerate D (b.1,b.2.1) _
      ((thirdGeometry (b.1,b.2.1)).yOut_nondegenerate (vector b.2.2) (vector_norm b.2.2))

private theorem ite_nondegenerate (p : Prop) [Decidable p] (U V : Label)
    (hU : (cubeForm.restrict U).Nondegenerate) (hV : (cubeForm.restrict V).Nondegenerate) :
    (cubeForm.restrict (if p then U else V)).Nondegenerate := by
  by_cases hp : p
  · rw [ite_eq_left hp]
    exact hU
  · rw [ite_eq_right hp]
    exact hV

theorem scratchInput_nondegenerate (j : Fin 3) (k : Invocation) :
    (cubeForm.restrict (scratchInput j k)).Nondegenerate := by
  unfold scratchInput
  apply ite_nondegenerate
  · exact ite_nondegenerate _ _ _ (common_nondegenerate 0 k.2) (MotifLabels.bot_nondegenerate cubeForm)
  · apply ite_nondegenerate
    · exact ite_nondegenerate _ _ _ (full_nondegenerate 0 k.2) (common_nondegenerate 1 k.2)
    · exact ite_nondegenerate _ _ _ (common_nondegenerate 2 (thirdKey k.2)) (full_nondegenerate 1 k.2)

theorem scratchOutput_nondegenerate (j : Fin 3) (k : Invocation) :
    (cubeForm.restrict (scratchOutput j k)).Nondegenerate := by
  unfold scratchOutput
  apply ite_nondegenerate
  · exact ite_nondegenerate _ _ _ (full_nondegenerate 0 k.2) (MotifLabels.bot_nondegenerate cubeForm)
  · apply ite_nondegenerate
    · exact ite_nondegenerate _ _ _ (full_nondegenerate 0 k.2) (full_nondegenerate 1 k.2)
    · exact ite_nondegenerate _ _ _ (full_nondegenerate 2 (thirdKey k.2)) (full_nondegenerate 1 k.2)

theorem input_nondegenerate (j : Fin 3) (i : World) : (cubeForm.restrict (input j i)).Nondegenerate := by
  rcases i with b | b | scratch
  · exact xInput_nondegenerate j b
  · exact yInput_nondegenerate j b
  · exact scratchInput_nondegenerate j scratch.1

theorem output_nondegenerate (j : Fin 3) (i : World) : (cubeForm.restrict (output j i)).Nondegenerate := by
  rcases i with b | b | scratch
  · exact xOutput_nondegenerate j b
  · exact yOutput_nondegenerate j b
  · exact scratchOutput_nondegenerate j scratch.1

theorem source_nondegenerate (i : World) : (cubeForm.restrict (source i)).Nondegenerate := by
  rcases i with b | b | scratch
  · have he : xInput 0 b = source (Sum.inl b) :=
      GlobalLabels.x_source (A := Side) (C := Control)
        D factor_symm factor_nondegenerate vector vector_norm b
    rw [← he]
    exact xInput_nondegenerate 0 b
  · exact MotifLabels.bot_nondegenerate _
  · exact MotifLabels.bot_nondegenerate _

theorem sink_nondegenerate (i : World) : (cubeForm.restrict (sink i)).Nondegenerate := by
  rcases i with b | b | scratch
  · exact MotifLabels.top_nondegenerate _ cube_nondegenerate
  · have he : yOutput 2 b = sink (Sum.inr (Sum.inl b)) :=
      GlobalLabels.y_sink (A := Side) (C := Control)
        D factor_symm factor_nondegenerate vector vector_norm b
    rw [← he]
    exact yOutput_nondegenerate 2 b
  · exact MotifLabels.top_nondegenerate _ cube_nondegenerate

/-- Before and after profiles for the four global attachment boundaries. -/
def boundaryBefore : Fin 4 → Profile
  | 0 => source
  | 1 => output 0
  | 2 => output 1
  | 3 => output 2

def boundaryAfter : Fin 4 → Profile
  | 0 => input 0
  | 1 => input 1
  | 2 => input 2
  | 3 => sink

theorem boundary_increasing (j : Fin 4) (i : World) : boundaryBefore j i ≤ boundaryAfter j i := by
  fin_cases j
  · exact source_le_input i
  · exact first_le_second i
  · exact second_le_third i
  · exact output_le_sink i

theorem boundaryBefore_nondegenerate (j : Fin 4) (i : World) :
    (cubeForm.restrict (boundaryBefore j i)).Nondegenerate := by
  fin_cases j
  · exact source_nondegenerate i
  · exact output_nondegenerate 0 i
  · exact output_nondegenerate 1 i
  · exact output_nondegenerate 2 i

theorem boundaryAfter_nondegenerate (j : Fin 4) (i : World) :
    (cubeForm.restrict (boundaryAfter j i)).Nondegenerate := by
  fin_cases j
  · exact input_nondegenerate 0 i
  · exact input_nondegenerate 1 i
  · exact input_nondegenerate 2 i
  · exact sink_nondegenerate i

/-- A fixed complete enumeration of the actual two-bank physical world. -/
def wires : List World := Finset.univ.toList

@[simp] theorem mem_wires (i : World) : i ∈ wires := by simp [wires]

/-- Label attachments at a boundary; these are not scalar arithmetic gates. -/
def boundaryUpdates (j : Fin 4) : List (World × Label) :=
  wires.map (fun i => (i,boundaryAfter j i))

theorem boundary_finish (j : Fin 4) :
    RankTrace.finish (boundaryBefore j) (boundaryUpdates j) = boundaryAfter j := by
  funext i
  simp only [boundaryUpdates,RankTrace.finish_align,mem_wires,ite_true]

theorem boundary_edges_increasing (j : Fin 4) :
    ∀ p ∈ RankTrace.edges (boundaryBefore j) (boundaryUpdates j), p.1 ≤ p.2 :=
  LabeledMotif.edges_endpoints_rel (fun U V : Label => U ≤ V) (fun _ => le_rfl)
    (boundaryBefore j) (boundaryAfter j) wires (fun i _ => boundary_increasing j i)

theorem boundary_edges_nondegenerate (j : Fin 4) :
    ∀ p ∈ RankTrace.edges (boundaryBefore j) (boundaryUpdates j),
      (cubeForm.restrict p.1).Nondegenerate ∧ (cubeForm.restrict p.2).Nondegenerate := by
  apply ProjectionTrace.edges_predicate (fun U : Label => (cubeForm.restrict U).Nondegenerate)
    (boundaryBefore j) (boundaryUpdates j)
  · exact boundaryBefore_nondegenerate j
  · intro p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact boundaryAfter_nondegenerate j i

/-- Exact zero downward loss for all four physical attachment histories. -/
theorem boundary_loss_zero (j : Fin 4) :
    RankTrace.loss (fun U : Label => finrank ℚ U) (boundaryBefore j) (boundaryUpdates j) = 0 := by
  unfold RankTrace.loss
  apply List.sum_eq_zero
  intro d hd
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hd
  exact Nat.sub_eq_zero_of_le (Submodule.finrank_mono (boundary_edges_increasing j p hp))

end
end IntegerMultBounds.Networks.Shared50GlobalTrace
