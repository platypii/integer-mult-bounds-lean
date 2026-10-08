import IntegerMultBounds.Machine.ScalingPreparedExecution
import IntegerMultBounds.Machine.ScalingStream

/-! One descriptor-synthesis setup followed by a counted family of complete
scaling executions. The canonical Q/B counts and family count are supplied;
piece descriptors and every mutable work sentinel are built physically once. -/

namespace IntegerMultBounds.Machine.ScalingPreparedStream

open CountedCopyReuse (empty binary)
open ScalingPreparedExecution (ExecutionTapes executionPlacement spare)

abbrev PreparedTapes (c : ℕ) := ScalingPreparedExecution.TapeCount c
abbrev TapeCount (c : ℕ) := PreparedTapes c+2

private def placementTo {c : ℕ} : Fin (ExecutionTapes c+2+1) → Fin (TapeCount c) :=
  Fin.addCases
    (Fin.addCases
      (fun i => Fin.castAdd 2 (executionPlacement c (Fin.castAdd 1 i)))
      (fun i => Fin.natAdd (PreparedTapes c) i))
    (fun i => Fin.castAdd 2 (executionPlacement c (Fin.natAdd (ExecutionTapes c) i)))

private def placementInverse {c : ℕ} : Fin (TapeCount c) → Fin (ExecutionTapes c+2+1) :=
  Fin.addCases
    (fun i => Fin.addCases
      (fun j => Fin.castAdd 1 (Fin.castAdd 2 j))
      (fun j => Fin.natAdd (ExecutionTapes c+2) j) ((executionPlacement c).symm i))
    (fun i => Fin.castAdd 1 (Fin.natAdd (ExecutionTapes c) i))

/-- Reuse the one-fiber execution placement and select the extra family clock. -/
def placement (c : ℕ) : Fin (ExecutionTapes c+2+1) ≃ Fin (TapeCount c) where
  toFun := placementTo
  invFun := placementInverse
  left_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;>
        simp only [placementTo,placementInverse,Fin.addCases_left,Fin.addCases_right,Equiv.symm_apply_apply]
    | right i => simp only [placementTo,placementInverse,Fin.addCases_left,Equiv.symm_apply_apply,Fin.addCases_right]
  right_inv := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      obtain ⟨j,rfl⟩ := (executionPlacement c).surjective i
      induction j using Fin.addCases <;>
        simp only [placementTo,placementInverse,Fin.addCases_left,Fin.addCases_right,Equiv.symm_apply_apply]
    | right i => simp only [placementTo,placementInverse,Fin.addCases_left,Fin.addCases_right]

/-- Grouping change is a fixed relabeling of the same tape bank. -/
theorem regroup {c : ℕ} (v : Tapes (ExecutionTapes c) 0) (frame : Tapes 1 0) (outer : Tapes 2 0) :
    (Placement.combine (executionPlacement c) v frame).append outer =
      Placement.combine (placement c) (v.append outer) frame := by
  unfold Placement.combine Tapes.reindex Tapes.append placement
  congr 1 <;> funext i <;> induction i using Fin.addCases with
  | left i =>
    obtain ⟨j,rfl⟩ := (executionPlacement c).surjective i
    induction j using Fin.addCases <;>
      simp only [Equiv.coe_fn_symm_mk,placementInverse,Fin.addCases_left,Fin.addCases_right,Equiv.symm_apply_apply]
  | right i => simp only [Equiv.coe_fn_symm_mk,placementInverse,Fin.addCases_left,Fin.addCases_right]

/-- Install the fresh outer-loop sentinel, preserving its immutable descriptor. -/
def outerMarkerProgram : Program 2 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols => if state = 0 then
    some (1,fun i => if i = 0 then (separator,Move.right) else (symbols i,Move.stay)) else none

private theorem outerMarker_hoare (ns : List Bool) :
    HoareTime outerMarkerProgram
      (fun v => v = CountedLoopReuse.controls (fun _ => blank) (binary ns) 0 1)
      (fun v => v = CountedLoopReuse.controls empty (binary ns) 1 1) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(CountedLoopReuse.controls empty (binary ns) 1 1).head,
    (CountedLoopReuse.controls empty (binary ns) 1 1).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,outerMarkerProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp [CountedLoopReuse.controls,Move.offset]
    · funext i z
      fin_cases i <;> simp [CountedLoopReuse.controls,empty]
      intro h; subst z; rfl
  · simp [step,outerMarkerProgram]

private theorem active_tail {s t : ℕ} (v : Tapes s 0) (w : Tapes t 0) :
    Placement.active (finAddFlip : Fin (t+s) ≃ Fin (s+t)) (v.append w) = w := by
  cases w
  simp [Placement.active,Tapes.append,finAddFlip_apply_castAdd]

private theorem extra_tail {s t : ℕ} (v : Tapes s 0) (w : Tapes t 0) :
    Placement.extra (finAddFlip : Fin (t+s) ≃ Fin (s+t)) (v.append w) = v := by
  cases v
  simp [Placement.extra,Tapes.append,finAddFlip_apply_natAdd]

private theorem replace_tail {s t : ℕ} (v : Tapes s 0) (w w' : Tapes t 0) :
    Placement.replace (finAddFlip : Fin (t+s) ≃ Fin (s+t)) (v.append w) w' = v.append w' := by
  rw [Placement.replace,extra_tail]
  simpa only [active_tail,extra_tail] using
    Placement.view (finAddFlip : Fin (t+s) ≃ Fin (s+t)) (v.append w')

/-- Unprepared descriptor/work cells and all source fibers on their literal tape. -/
def input {c : ℕ} (Q n : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ) (dest : ℤ → Fin 4) (q : ℤ)
    (bs qs ns : List Bool) (modulus current : Tapes c 0) (payload : ℕ → ℕ → List (Fin 4)) :
    Tapes (TapeCount c) 0 :=
  CountedLoopReuse.bank
    (ScalingPreparedExecution.input Q (putWord source p (ScalingStream.fibers Q n payload).flatten) p
      background origins dest q bs qs modulus current (fun _ => []))
    (fun _ => blank) (binary ns) 0 1

/-- The final bank retains derived descriptors and the spare, restores all
payload buffers and mutable clocks, and advances to the end of the fiber family. -/
def output {c : ℕ} (hc : 0 < c) (Q B n : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ) (dest : ℤ → Fin 4) (q : ℤ)
    (bs qs ns : List Bool) (modulus current : Tapes c 0) (payload : ℕ → ℕ → List (Fin 4)) :
    Tapes (TapeCount c) 0 :=
  Placement.combine (placement c)
    (CountedLoopReuse.bank
      (ScalingStream.state hc Q B n source p background origins dest q
        (ScalingDescriptorData.descriptors hc Q B Q) bs qs
        (OneHot.bank modulus (OneHot.residue hc Q)) (OneHot.bank current (OneHot.residue hc Q)) payload n)
      empty (binary ns) 1 1) spare

private theorem initial_state {c : ℕ} (hc : 0 < c) (Q B n : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ) (dest : ℤ → Fin 4) (q : ℤ)
    (bs qs : List Bool) (modulus current : Tapes c 0) (payload : ℕ → ℕ → List (Fin 4)) :
    ScalingExecutionReuse.input Q (putWord source p (ScalingStream.fibers Q n payload).flatten) p
      background origins dest q (ScalingDescriptorData.descriptors hc Q B Q) bs qs modulus current (fun _ => []) =
    ScalingStream.state hc Q B n source p background origins dest q
      (ScalingDescriptorData.descriptors hc Q B Q) bs qs modulus current payload 0 := by
  simp [ScalingExecutionReuse.input,ScalingExecution.inputWord,ScalingStream.state,ScalingStream.outputPrefix,
    ScalingStream.residueState,putWord]

abbrev PreparationStates (c : ℕ) := ScalingPreparedExecution.SynthesisStates c+2+2
abbrev StreamStates (c : ℕ) := 7+(ScalingPreparedExecution.ExecutionStates c+5)+4

def prepareProgram {c : ℕ} (hc : 0 < c) : Program (TapeCount c) (PreparationStates c) 0 :=
  seq (extend (ScalingPreparedExecution.prepareProgram hc) 2)
    (Placement.placed outerMarkerProgram (finAddFlip : Fin (2+PreparedTapes c) ≃ Fin (TapeCount c)))

def program {c : ℕ} (hc : 0 < c) : Program (TapeCount c) (PreparationStates c+StreamStates c) 0 :=
  seq (prepareProgram hc) (Placement.placed (ScalingStream.program hc) (placement c))

/-- Prepare one shared descriptor bank for the entire counted fiber family. -/
theorem prepare_hoare {c : ℕ} (hc : 0 < c) (Q B n : ℕ) (hB : 0 < B)
    (source : ℤ → Fin 4) (p : ℤ) (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (bs qs ns : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (modulus current : Tapes c 0) (payload : ℕ → ℕ → List (Fin 4)) :
    HoareTime (prepareProgram hc)
      (fun v => v = input Q n source p background origins dest q bs qs ns modulus current payload)
      (fun v => v = Placement.combine (placement c)
        (CountedLoopReuse.bank
          (ScalingStream.state hc Q B n source p background origins dest q
            (ScalingDescriptorData.descriptors hc Q B Q) bs qs
            (OneHot.bank modulus (OneHot.residue hc Q)) (OneHot.bank current (OneHot.residue hc Q)) payload 0)
          empty (binary ns) 1 1) spare)
      (70*(Q*B)+55) := by
  let m := OneHot.bank modulus (OneHot.residue hc Q)
  let z := OneHot.bank current (OneHot.residue hc Q)
  let src := putWord source p (ScalingStream.fibers Q n payload).flatten
  let before := ScalingExecutionReuse.input Q src p background origins dest q
    (ScalingDescriptorData.descriptors hc Q B Q) bs qs m z (fun _ => [])
  let ready := Placement.combine (executionPlacement c) before spare
  let raw := CountedLoopReuse.controls (fun _ => blank) (binary ns) 0 1
  have hp := (ScalingPreparedExecution.prepare_hoare hc Q B hB src p background origins dest q
    bs qs hb hq cb cq modulus current (fun _ => [])).extend raw
  have hp' : HoareTime (extend (ScalingPreparedExecution.prepareProgram hc) 2)
      (fun v => v = input Q n source p background origins dest q bs qs ns modulus current payload)
      (fun v => v = ready.append raw) (70*(Q*B)+53) := by
    apply hp.consequence _ _ le_rfl
    · intro v hv; exact ⟨_,rfl,hv⟩
    · rintro v ⟨w,rfl,hv⟩; exact hv
  have hm := Placement.hoare_at (outerMarker_hoare ns)
    (finAddFlip : Fin (2+PreparedTapes c) ≃ Fin (TapeCount c)) (ready.append raw) (active_tail _ _)
  have hm' : HoareTime
      (Placement.placed outerMarkerProgram (finAddFlip : Fin (2+PreparedTapes c) ≃ Fin (TapeCount c)))
      (fun v => v = ready.append raw)
      (fun v => v = ready.append (CountedLoopReuse.controls empty (binary ns) 1 1)) 1 := by
    apply hm.consequence (fun _ hv => hv) _ le_rfl
    rintro v ⟨w,rfl,rfl⟩
    exact replace_tail _ _ _
  have h := hp'.seq hm'
  dsimp only [ready,before,src] at h
  rw [regroup,initial_state] at h
  exact h.consequence (fun _ hv => hv) (fun _ hv => hv) (by omega)

/-- A single physical preparation followed by n actual scaling executions.
Q/B and n descriptors are the only prepared numeric data. Setup remains
explicit in the bound, including for the zero-fiber case. -/
theorem scale_hoare {Q c B n : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q) (hB : 0 < B)
    (source : ℤ → Fin 4) (p : ℤ) (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (bs qs ns : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (hn : Counter.value ns = n)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) (modulus current : Tapes c 0)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B)
    (hblank : ∀ j z, origins j ≤ z → z < origins j+
      ((ScalingSplit.offset Q c B (j.val+1)-ScalingSplit.offset Q c B j.val : ℕ) : ℤ) → background j z = blank) :
    HoareTime (program hc)
      (fun v => v = input Q n source p background origins dest q bs qs ns modulus current payload)
      (fun v => v = output hc Q B n source p background origins dest q bs qs ns modulus current payload)
      ((192+120*c)*(ScalingStream.fibers Q n payload).flatten.length+70*(Q*B)+79) := by
  have hp : ∀ j, Counter.value (ScalingDescriptorData.descriptors hc Q B Q j) =
      ScalingSplit.offset Q c B (j.val+1)-ScalingSplit.offset Q c B j.val := by
    intro j
    rw [ScalingDescriptorData.complete_value hQ hc hcop]
    simp only [ScalingSplit.offset,Nat.sub_mul]
  have cp := ScalingDescriptorData.descriptors_canonical hc Q B Q
  let m := OneHot.bank modulus (OneHot.residue hc Q)
  let z := OneHot.bank current (OneHot.residue hc Q)
  let ds := ScalingDescriptorData.descriptors hc Q B Q
  let before := CountedLoopReuse.bank
    (ScalingStream.state hc Q B n source p background origins dest q ds bs qs m z payload 0) empty (binary ns) 1 1
  have he := Placement.hoare_at
    (ScalingStream.scale_hoare_linear hQ hc hcop hB source p background origins dest q ds bs qs ns
      hb hq hn cb cq cn hp cp m z payload hwidth hblank)
    (placement c) (Placement.combine (placement c) before spare) (Placement.active_combine _ _ _)
  have he' : HoareTime (Placement.placed (ScalingStream.program hc) (placement c))
      (fun v => v = Placement.combine (placement c) before spare)
      (fun v => v = output hc Q B n source p background origins dest q bs qs ns modulus current payload)
      ((192+120*c)*(ScalingStream.fibers Q n payload).flatten.length+23) := by
    apply he.consequence (fun _ hv => hv) _ le_rfl
    rintro v ⟨w,rfl,rfl⟩
    simp only [Placement.replace,Placement.extra_combine]
    rfl
  have h := (prepare_hoare hc Q B n hB source p background origins dest q bs qs ns hb hq cb cq
    modulus current payload).seq he'
  exact h.consequence (fun _ hv => hv) (fun _ hv => hv) (by omega)

/-- For a nonempty fiber family, the once-only preparation is absorbed by
physical payload volume; the coefficient depends only on the fixed multiplier. -/
theorem scale_hoare_linear {Q c B n : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (hB : 0 < B) (hnpos : 0 < n)
    (source : ℤ → Fin 4) (p : ℤ) (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (bs qs ns : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (hn : Counter.value ns = n)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) (modulus current : Tapes c 0)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B)
    (hblank : ∀ j z, origins j ≤ z → z < origins j+
      ((ScalingSplit.offset Q c B (j.val+1)-ScalingSplit.offset Q c B j.val : ℕ) : ℤ) → background j z = blank) :
    HoareTime (program hc)
      (fun v => v = input Q n source p background origins dest q bs qs ns modulus current payload)
      (fun v => v = output hc Q B n source p background origins dest q bs qs ns modulus current payload)
      ((262+120*c)*(ScalingStream.fibers Q n payload).flatten.length+79) := by
  apply (scale_hoare hQ hc hcop hB source p background origins dest q bs qs ns hb hq hn cb cq cn
    modulus current payload hwidth hblank).consequence (fun _ hv => hv) (fun _ hv => hv)
  rw [ScalingStream.source_length Q B n payload hwidth]
  have hvol : Q*B ≤ n*(Q*B) := by
    calc Q*B = 1*(Q*B) := by omega
         _ ≤ n*(Q*B) := Nat.mul_le_mul_right _ (by omega : 1 ≤ n)
  nlinarith

/-- The sole framed spare remains physically unchanged throughout the family. -/
theorem output_spare {c : ℕ} (hc : 0 < c) (Q B n : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ) (dest : ℤ → Fin 4) (q : ℤ)
    (bs qs ns : List Bool) (modulus current : Tapes c 0) (payload : ℕ → ℕ → List (Fin 4)) :
    Placement.extra (placement c)
      (output hc Q B n source p background origins dest q bs qs ns modulus current payload) = spare :=
  Placement.extra_combine _ _ _

theorem tapeCount_eq (c : ℕ) : TapeCount c = 13+4*c := by
  dsimp [TapeCount,PreparedTapes]
  rw [ScalingPreparedExecution.tapeCount_eq]
  omega

theorem stateCount_eq (c : ℕ) : PreparationStates c+StreamStates c = 117*c+103 := by
  simp only [PreparationStates,StreamStates,ScalingPreparedExecution.SynthesisStates,
    ScalingPreparedExecution.ExecutionStates,ScalingSplit.states_eq,ScalingBuffersReset.states_eq]
  omega

end IntegerMultBounds.Machine.ScalingPreparedStream
