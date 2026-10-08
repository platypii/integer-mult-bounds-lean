import IntegerMultBounds.Machine.ScalingDescriptors
import IntegerMultBounds.Machine.ScalingExecutionReuse

/-! Physical descriptor preparation followed by complete reusable scaling.
Only binary Q/B are supplied: piece counts, control sentinels and residue cells
are constructed by actual finite programs. Derived descriptors are retained. -/

namespace IntegerMultBounds.Machine.ScalingPreparedExecution

open CountedCopyReuse (empty binary)
open ScalingExecution (SplitTapes AuxTapes)

abbrev SynthesisTapes (c : ℕ) := 1+c+2+c+c+2
abbrev FrameTapes (c : ℕ) := 4+c+2
abbrev ExecutionTapes (c : ℕ) := ScalingExecution.TapeCount c
abbrev TapeCount (c : ℕ) := SynthesisTapes c+FrameTapes c

def spare : Tapes 1 0 := ⟨fun _ => 1,fun _ _ => blank⟩

private def activeTo {c : ℕ} : Fin (SynthesisTapes c) → Fin (ExecutionTapes c+1) :=
  Fin.addCases (Fin.addCases (Fin.addCases
    (Fin.addCases (Fin.addCases
      (fun i => Fin.natAdd (ExecutionTapes c) i)
      (fun i => Fin.castAdd 1 (Fin.castAdd (AuxTapes c) (Fin.natAdd 4 (Fin.natAdd c i)))))
      (fun i => Fin.castAdd 1 (Fin.natAdd (SplitTapes c)
        (Fin.castAdd 2 (Fin.castAdd c (Fin.castAdd c (Fin.natAdd 2 i)))))))
    (fun i => Fin.castAdd 1 (Fin.natAdd (SplitTapes c)
      (Fin.castAdd 2 (Fin.castAdd c (Fin.natAdd 4 i))))))
    (fun i => Fin.castAdd 1 (Fin.natAdd (SplitTapes c) (Fin.castAdd 2 (Fin.natAdd (4+c) i)))))
    (fun i => Fin.castAdd 1 (Fin.natAdd (SplitTapes c) (Fin.natAdd (4+c+c) i)))

private def frameTo {c : ℕ} : Fin (FrameTapes c) → Fin (ExecutionTapes c+1) :=
  Fin.addCases (Fin.addCases
    (fun i => Fin.castAdd 1 (Fin.castAdd (AuxTapes c) (Fin.castAdd (c+c) i)))
    (fun i => Fin.castAdd 1 (Fin.castAdd (AuxTapes c) (Fin.natAdd 4 (Fin.castAdd c i)))))
    (fun i => Fin.castAdd 1 (Fin.natAdd (SplitTapes c)
      (Fin.castAdd 2 (Fin.castAdd c (Fin.castAdd c (Fin.castAdd 2 i))))))

private def inverse {c : ℕ} : Fin (ExecutionTapes c+1) → Fin (TapeCount c) := by
  refine Fin.addCases ?_ ?_
  · refine Fin.addCases ?_ ?_
    · refine Fin.addCases ?_ ?_
      · intro i
        exact Fin.natAdd (SynthesisTapes c) (Fin.castAdd 2 (Fin.castAdd c i))
      · refine Fin.addCases ?_ ?_
        · intro i
          exact Fin.natAdd (SynthesisTapes c) (Fin.castAdd 2 (Fin.natAdd 4 i))
        · intro i
          exact Fin.castAdd (FrameTapes c)
            (Fin.castAdd 2 (Fin.castAdd c (Fin.castAdd c (Fin.castAdd 2 (Fin.natAdd 1 i)))))
    · refine Fin.addCases ?_ ?_
      · refine Fin.addCases ?_ ?_
        · refine Fin.addCases ?_ ?_
          · refine Fin.addCases (m := 2) (n := 2) ?_ ?_
            · intro i
              exact Fin.natAdd (SynthesisTapes c) (Fin.natAdd (4+c) i)
            · intro i
              exact Fin.castAdd (FrameTapes c)
                (Fin.castAdd 2 (Fin.castAdd c (Fin.castAdd c (Fin.natAdd (1+c) i))))
          · intro i
            exact Fin.castAdd (FrameTapes c) (Fin.castAdd 2 (Fin.castAdd c (Fin.natAdd (1+c+2) i)))
        · intro i
          exact Fin.castAdd (FrameTapes c) (Fin.castAdd 2 (Fin.natAdd (1+c+2+c) i))
      · intro i
        exact Fin.castAdd (FrameTapes c) (Fin.natAdd (1+c+2+c+c) i)
  · intro i
    exact Fin.castAdd (FrameTapes c)
      (Fin.castAdd 2 (Fin.castAdd c (Fin.castAdd c (Fin.castAdd 2 (Fin.castAdd c i)))))

/-- Static wiring shares Q/B, all synthesized piece counts, residue controls
and reusable clocks between synthesis and the scaling executor. -/
def synthesisPlacement (c : ℕ) : Fin (TapeCount c) ≃ Fin (ExecutionTapes c+1) where
  toFun := Fin.addCases activeTo frameTo
  invFun := inverse
  left_inv := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i =>
          induction i using Fin.addCases with
          | left i =>
            induction i using Fin.addCases with
            | left i => induction i using Fin.addCases <;>
                simp only [activeTo,inverse,Fin.addCases_left,Fin.addCases_right]
            | right i => simp only [activeTo,inverse,Fin.addCases_left,Fin.addCases_right]
          | right i => simp only [activeTo,inverse,Fin.addCases_left,Fin.addCases_right]
        | right i => simp only [activeTo,inverse,Fin.addCases_left,Fin.addCases_right]
      | right i => simp only [activeTo,inverse,Fin.addCases_left,Fin.addCases_right]
    | right i =>
      induction i using Fin.addCases with
      | left i => induction i using Fin.addCases <;>
          simp only [frameTo,inverse,Fin.addCases_left,Fin.addCases_right]
      | right i => simp only [frameTo,inverse,Fin.addCases_left,Fin.addCases_right]
  right_inv := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i => simp only [inverse,frameTo,Fin.addCases_left,Fin.addCases_right]
        | right i => induction i using Fin.addCases <;>
            simp only [inverse,activeTo,frameTo,Fin.addCases_left,Fin.addCases_right]
      | right i =>
        induction i using Fin.addCases with
        | left i =>
          induction i using Fin.addCases with
          | left i =>
            induction i using Fin.addCases with
            | left i => induction i using (Fin.addCases (m := 2) (n := 2)) <;>
                simp only [inverse,activeTo,frameTo,Fin.addCases_left,Fin.addCases_right]
            | right i => simp only [inverse,activeTo,Fin.addCases_left,Fin.addCases_right]
          | right i => simp only [inverse,activeTo,Fin.addCases_left,Fin.addCases_right]
        | right i => simp only [inverse,activeTo,Fin.addCases_left,Fin.addCases_right]
    | right i => simp only [inverse,activeTo,Fin.addCases_left,Fin.addCases_right]

/-- The physical executor uses the inverse wiring; its sole frame is a spare. -/
def executionPlacement (c : ℕ) : Fin (ExecutionTapes c+1) ≃ Fin (TapeCount c) :=
  (synthesisPlacement c).symm

private def join {c : ℕ} (a : Tapes 4 0) (buffers ds : Tapes c 0)
    (left right : Tapes 2 0) (modulus current : Tapes c 0) (outer : Tapes 2 0) (s : Tapes 1 0) :
    Tapes (ExecutionTapes c+1) 0 :=
  (ScalingExecution.join a buffers ds (left.append right) modulus current outer).append s

private theorem active_join {c : ℕ} (a : Tapes 4 0) (buffers ds : Tapes c 0)
    (left right : Tapes 2 0) (modulus current : Tapes c 0) (outer : Tapes 2 0) (s : Tapes 1 0) :
    Placement.active (synthesisPlacement c) (join a buffers ds left right modulus current outer s) =
      ((((s.append ds).append right).append modulus).append current).append outer := by
  unfold Placement.active synthesisPlacement join ScalingExecution.join Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i => induction i using Fin.addCases <;>
            simp only [Equiv.coe_fn_mk,activeTo,Fin.addCases_left,Fin.addCases_right]
        | right i => simp only [Equiv.coe_fn_mk,activeTo,Fin.addCases_left,Fin.addCases_right]
      | right i => simp only [Equiv.coe_fn_mk,activeTo,Fin.addCases_left,Fin.addCases_right]
    | right i => simp only [Equiv.coe_fn_mk,activeTo,Fin.addCases_left,Fin.addCases_right]
  | right i => simp only [Equiv.coe_fn_mk,activeTo,Fin.addCases_left,Fin.addCases_right]

private theorem extra_join {c : ℕ} (a : Tapes 4 0) (buffers ds : Tapes c 0)
    (left right : Tapes 2 0) (modulus current : Tapes c 0) (outer : Tapes 2 0) (s : Tapes 1 0) :
    Placement.extra (synthesisPlacement c) (join a buffers ds left right modulus current outer s) =
      (a.append buffers).append left := by
  unfold Placement.extra synthesisPlacement join ScalingExecution.join Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases with
  | left i => induction i using Fin.addCases <;>
      simp only [Equiv.coe_fn_mk,frameTo,Fin.addCases_left,Fin.addCases_right]
  | right i => simp only [Equiv.coe_fn_mk,frameTo,Fin.addCases_left,Fin.addCases_right]

/-- Complete-bank handoff by a fixed permutation, with no tape movement hidden. -/
theorem regroup {c : ℕ} (a : Tapes 4 0) (buffers ds : Tapes c 0)
    (left right : Tapes 2 0) (modulus current : Tapes c 0) (outer : Tapes 2 0) (s : Tapes 1 0) :
    (((((s.append ds).append right).append modulus).append current).append outer).append
      ((a.append buffers).append left) =
    Placement.combine (executionPlacement c)
      (ScalingExecution.join a buffers ds (left.append right) modulus current outer) s := by
  have h := Placement.view (synthesisPlacement c) (join a buffers ds left right modulus current outer s)
  rw [active_join,extra_join] at h
  have hr := congrArg (Tapes.reindex (executionPlacement c)) h
  simpa only [Placement.combine,executionPlacement,Tapes.reindex,Equiv.symm_symm,
    Equiv.symm_apply_apply,join] using hr

private def frame {c : ℕ} (source : ℤ → Fin 4) (p : ℤ) (background : Fin c → ℤ → Fin 4)
    (origins : Fin c → ℤ) (dest : ℤ → Fin 4) (q : ℤ) (clock marker : ℤ → Fin 4) (r : ℤ) :
    Tapes (FrameTapes c) 0 :=
  ((CountedCopyReuse.bank source (fun _ => blank) clock (fun _ => blank) p 0 r 0).append
    (⟨origins,background⟩ : Tapes c 0)).append (CountedLoopReuse.controls marker dest 0 q)

/-- Install the remaining split-clock and merge-spare sentinels physically. -/
def frameProgram (c : ℕ) : Program (FrameTapes c) 2 0 where
  tapes_pos := by dsimp [FrameTapes]; omega
  start := 0
  transition := fun state symbols => if state = 0 then
    some (1,Fin.addCases
      (Fin.addCases
        (fun i => if i = 2 then (separator,Move.right)
          else (symbols (Fin.castAdd 2 (Fin.castAdd c i)),Move.stay))
        (fun i => (symbols (Fin.castAdd 2 (Fin.natAdd 4 i)),Move.stay)))
      (fun i => if i = 0 then (separator,Move.stay) else (symbols (Fin.natAdd (4+c) i),Move.stay)))
    else none

private theorem frame_hoare {c : ℕ} (source : ℤ → Fin 4) (p : ℤ) (background : Fin c → ℤ → Fin 4)
    (origins : Fin c → ℤ) (dest : ℤ → Fin 4) (q : ℤ) :
    HoareTime (frameProgram c)
      (fun v => v = frame source p background origins dest q (fun _ => blank) (fun _ => blank) 0)
      (fun v => v = frame source p background origins dest q empty empty 1) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(frame source p background origins dest q empty empty 1).head,
    (frame source p background origins dest q empty empty 1).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,frameProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i => fin_cases i <;> simp [frame,Tapes.append,CountedCopyReuse.bank,Move.offset]
        | right i => simp [frame,Tapes.append,Move.offset]
      | right i => fin_cases i <;> simp [frame,Tapes.append,CountedLoopReuse.controls,Move.offset]
    · funext i z
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i =>
          fin_cases i <;> simp [frame,Tapes.append,CountedCopyReuse.bank,empty]
          all_goals intro h; subst z; rfl
        | right i =>
          simp [frame,Tapes.append]
          intro h; subst z; rfl
      | right i =>
        fin_cases i <;> simp [frame,Tapes.append,CountedLoopReuse.controls,empty]
        intro h; subst z; rfl
  · simp [step,frameProgram]

def readySynthesis {c : ℕ} (hc : 0 < c) (Q B : ℕ) (bs qs : List Bool) (modulus current : Tapes c 0) :
    Tapes (SynthesisTapes c) 0 :=
  CountedLoopReuse.bank
    (ScalingDescriptors.bank (ScalingDescriptorData.descriptors hc Q B Q) bs modulus current
      (OneHot.residue hc Q) (OneHot.residue hc Q)) empty (binary qs) 1 1

/-- Inputs contain only the two prepared count descriptors; all synthesized
piece descriptors and all work tapes start completely blank. -/
def input {c : ℕ} (Q : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ) (dest : ℤ → Fin 4) (q : ℤ)
    (bs qs : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) :
    Tapes (TapeCount c) 0 :=
  (ScalingDescriptors.initial bs qs modulus current).append
    (frame (putWord source p (ScalingExecution.inputWord Q payload)) p background origins dest q
      (fun _ => blank) (fun _ => blank) 0)

private theorem split_merge_controls (source dest : ℤ → Fin 4) (p q : ℤ) (bs : List Bool) :
    (CountedLoopReuse.controls source dest p q).append (CountedLoopReuse.controls empty (binary bs) 1 1) =
      CountedCopyReuse.bank source dest empty (binary bs) p q 1 1 := by
  unfold CountedLoopReuse.controls CountedCopyReuse.bank Tapes.append
  congr 1 <;> funext i <;> fin_cases i <;> rfl

/-- The synthesized physical descriptor cells are exactly the cells used by
splitting and subsequent reusable scaling, with no descriptor copying oracle. -/
theorem handoff {c : ℕ} (hc : 0 < c) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ) (dest : ℤ → Fin 4) (q : ℤ)
    (bs qs : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) :
    (readySynthesis hc Q B bs qs modulus current).append
      (frame (putWord source p (ScalingExecution.inputWord Q payload)) p background origins dest q empty empty 1) =
    Placement.combine (executionPlacement c)
      (ScalingExecutionReuse.input Q source p background origins dest q
        (ScalingDescriptorData.descriptors hc Q B Q) bs qs
        (OneHot.bank modulus (OneHot.residue hc Q)) (OneHot.bank current (OneHot.residue hc Q)) payload) spare := by
  have h := regroup
    (CountedCopyReuse.bank (putWord source p (ScalingExecution.inputWord Q payload)) (fun _ => blank)
      empty (fun _ => blank) p 0 1 0)
    (⟨origins,background⟩ : Tapes c 0)
    (⟨fun _ => 1,fun j => binary (ScalingDescriptorData.descriptors hc Q B Q j)⟩ : Tapes c 0)
    (CountedLoopReuse.controls empty dest 0 q) (CountedLoopReuse.controls empty (binary bs) 1 1)
    (OneHot.bank modulus (OneHot.residue hc Q)) (OneHot.bank current (OneHot.residue hc Q))
    (CountedLoopReuse.controls empty (binary qs) 1 1) spare
  rw [split_merge_controls] at h
  exact h

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

abbrev SynthesisStates (c : ℕ) := 2+20+(7+(c*19+1+2+5)+4)
abbrev ExecutionStates (c : ℕ) :=
  20+((ScalingSplit.states c+ScalingSplit.states c)+(7+(c*16+1+2+5)+4))+ScalingBuffersReset.states c

def prepareProgram {c : ℕ} (hc : 0 < c) : Program (TapeCount c) (SynthesisStates c+2) 0 :=
  seq (extend (ScalingDescriptors.program hc) (FrameTapes c))
    (Placement.placed (frameProgram c) (finAddFlip : Fin (FrameTapes c+SynthesisTapes c) ≃ Fin (TapeCount c)))

/-- Preparation charges synthesis, initialization of remaining work sentinels,
and the real join. The resulting descriptors are on their final executor tapes. -/
theorem prepare_hoare {c : ℕ} (hc : 0 < c) (Q B : ℕ) (hB : 0 < B)
    (source : ℤ → Fin 4) (p : ℤ) (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (bs qs : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) :
    HoareTime (prepareProgram hc)
      (fun v => v = input Q source p background origins dest q bs qs modulus current payload)
      (fun v => v = Placement.combine (executionPlacement c)
        (ScalingExecutionReuse.input Q source p background origins dest q
          (ScalingDescriptorData.descriptors hc Q B Q) bs qs
          (OneHot.bank modulus (OneHot.residue hc Q)) (OneHot.bank current (OneHot.residue hc Q)) payload) spare)
      (70*(Q*B)+53) := by
  let raw := frame (putWord source p (ScalingExecution.inputWord Q payload)) p background origins dest q
    (fun _ => blank) (fun _ => blank) 0
  let ready := frame (putWord source p (ScalingExecution.inputWord Q payload)) p background origins dest q empty empty 1
  have hs := (ScalingDescriptors.synthesize_hoare_linear hc Q B hB bs qs hb hq cb cq modulus current).extend raw
  have hs' : HoareTime (extend (ScalingDescriptors.program hc) (FrameTapes c))
      (fun v => v = input Q source p background origins dest q bs qs modulus current payload)
      (fun v => v = (readySynthesis hc Q B bs qs modulus current).append raw) (70*(Q*B)+51) := by
    apply hs.consequence _ _ le_rfl
    · intro v hv; exact ⟨_,rfl,hv⟩
    · rintro v ⟨small,rfl,hv⟩; exact hv
  have hf := Placement.hoare_at
    (frame_hoare (putWord source p (ScalingExecution.inputWord Q payload)) p background origins dest q)
    (finAddFlip : Fin (FrameTapes c+SynthesisTapes c) ≃ Fin (TapeCount c))
    ((readySynthesis hc Q B bs qs modulus current).append raw) (active_tail _ _)
  have hf' : HoareTime
      (Placement.placed (frameProgram c) (finAddFlip : Fin (FrameTapes c+SynthesisTapes c) ≃ Fin (TapeCount c)))
      (fun v => v = (readySynthesis hc Q B bs qs modulus current).append raw)
      (fun v => v = (readySynthesis hc Q B bs qs modulus current).append ready) 1 := by
    apply hf.consequence (fun _ hv => hv) _ le_rfl
    rintro v ⟨w,rfl,rfl⟩
    exact replace_tail _ _ _
  have h := hs'.seq hf'
  change HoareTime _ _ (fun v => v = (readySynthesis hc Q B bs qs modulus current).append
    (frame (putWord source p (ScalingExecution.inputWord Q payload)) p background origins dest q empty empty 1)) _ at h
  rw [handoff] at h
  exact h.consequence (fun _ hv => hv) (fun _ hv => hv) (by omega)

def output {c : ℕ} (hc : 0 < c) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ) (dest : ℤ → Fin 4) (q : ℤ)
    (bs qs : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) :
    Tapes (TapeCount c) 0 :=
  Placement.combine (executionPlacement c)
    (ScalingExecutionReuse.output hc Q B source p background origins dest q
      (ScalingDescriptorData.descriptors hc Q B Q) bs qs
      (OneHot.bank modulus (OneHot.residue hc Q)) (OneHot.bank current (OneHot.residue hc Q)) payload) spare

def program {c : ℕ} (hc : 0 < c) : Program (TapeCount c) (SynthesisStates c+2+ExecutionStates c) 0 :=
  seq (prepareProgram hc) (Placement.placed (ScalingExecutionReuse.program hc) (executionPlacement c))

private theorem input_length {Q B : ℕ} (payload : ℕ → List (Fin 4))
    (hwidth : ∀ y, (payload y).length = B) : (ScalingExecution.inputWord Q payload).length = Q*B := by
  unfold ScalingExecution.inputWord
  rw [BlockRotationData.uniform_volume B]
  · simp
  · intro block hm
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hm
    exact hwidth y

/-- Complete literal positive scaling from Q/B descriptors and initially blank
work tapes. All piece descriptors are synthesized, buffers are restored, and
the resulting descriptor bank remains available for further fibers. -/
theorem scaling_hoare {Q c B : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q) (hB : 0 < B)
    (source : ℤ → Fin 4) (p : ℤ) (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (bs qs : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4))
    (hwidth : ∀ y, (payload y).length = B)
    (hblank : ∀ j z, origins j ≤ z →
      z < origins j+(ScalingSplit.piece Q c B (ScalingExecution.inputWord Q payload) j).length → background j z = blank) :
    HoareTime (program hc)
      (fun v => v = input Q source p background origins dest q bs qs modulus current payload)
      (fun v => v = output hc Q B source p background origins dest q bs qs modulus current payload)
      (197*(Q*B)+120*c+106) := by
  have hp : ∀ j, Counter.value (ScalingDescriptorData.descriptors hc Q B Q j) =
      (ScalingSplit.piece Q c B (ScalingExecution.inputWord Q payload) j).length :=
    fun j => ScalingDescriptorData.complete_piece_length hQ hc hcop _ (input_length payload hwidth) j
  have cp := ScalingDescriptorData.descriptors_canonical hc Q B Q
  let m := OneHot.bank modulus (OneHot.residue hc Q)
  let z := OneHot.bank current (OneHot.residue hc Q)
  let ds := ScalingDescriptorData.descriptors hc Q B Q
  let before := ScalingExecutionReuse.input Q source p background origins dest q ds bs qs m z payload
  have he := Placement.hoare_at
    (ScalingExecutionReuse.scaling_hoare hQ hc hcop hB source p background origins dest q ds bs qs
      hb hq cb cq payload hp cp m z hwidth hblank)
    (executionPlacement c) (Placement.combine (executionPlacement c) before spare)
    (Placement.active_combine _ _ _)
  have he' : HoareTime (Placement.placed (ScalingExecutionReuse.program hc) (executionPlacement c))
      (fun v => v = Placement.combine (executionPlacement c) before spare)
      (fun v => v = output hc Q B source p background origins dest q bs qs modulus current payload)
      (127*(Q*B)+120*c+52) := by
    apply he.consequence (fun _ hv => hv) _ le_rfl
    rintro v ⟨w,rfl,rfl⟩
    simp only [Placement.replace,Placement.extra_combine]
    rfl
  have h := (prepare_hoare hc Q B hB source p background origins dest q bs qs hb hq cb cq modulus current payload).seq he'
  exact h.consequence (fun _ hv => hv) (fun _ hv => hv) (by omega)

/-- The final physical destination contains the inverse-scaled block sequence. -/
theorem output_tape {c : ℕ} (hc : 0 < c) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ) (dest : ℤ → Fin 4) (q : ℤ)
    (bs qs : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) :
    (output hc Q B source p background origins dest q bs qs modulus current payload).tape
      (executionPlacement c (Fin.castAdd 1 (ScalingExecution.destinationSlot c))) =
      putWord dest q (ScalingMerge.outputPrefix hc Q Q payload) := by
  rw [output,Placement.combine_tape_active]
  exact ScalingExecutionReuse.output_tape _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The spare tape's full contents and head are retained, not discarded. -/
theorem output_spare {c : ℕ} (hc : 0 < c) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ) (dest : ℤ → Fin 4) (q : ℤ)
    (bs qs : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) :
    Placement.extra (executionPlacement c)
      (output hc Q B source p background origins dest q bs qs modulus current payload) = spare :=
  Placement.extra_combine _ _ _

theorem tapeCount_eq (c : ℕ) : TapeCount c = 11+4*c := by
  dsimp [TapeCount,SynthesisTapes,FrameTapes]
  omega

theorem stateCount_eq (c : ℕ) : SynthesisStates c+2+ExecutionStates c = 117*c+85 := by
  simp only [SynthesisStates,ExecutionStates,ScalingSplit.states_eq,ScalingBuffersReset.states_eq]
  omega

end IntegerMultBounds.Machine.ScalingPreparedExecution
