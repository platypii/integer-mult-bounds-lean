import IntegerMultBounds.Machine.ScalingExecution
import IntegerMultBounds.Machine.ScalingControlInit
import IntegerMultBounds.Machine.ScalingBuffersReset

/-! Reusable literal positive-unit scaling. Both residue banks are initialized
from arbitrary scanned cells, all split/rewind/merge work is physically run,
and every temporary piece buffer is erased and rewound. Binary descriptors
remain explicit immutable inputs; no hidden preparation cost is claimed. -/

namespace IntegerMultBounds.Machine.ScalingExecutionReuse

open CountedCopyReuse (empty binary)
open ScalingExecution (SplitTapes AuxTapes TapeCount)

private def initTo {c : ℕ} : Fin (c+c+2) → Fin (AuxTapes c) :=
  Fin.addCases
    (Fin.addCases
      (fun i => Fin.castAdd 2 (Fin.castAdd c (Fin.natAdd 4 i)))
      (fun i => Fin.castAdd 2 (Fin.natAdd (4+c) i)))
    (fun i => Fin.natAdd (4+c+c) i)

private def initInverse {c : ℕ} : Fin (AuxTapes c) → Fin (c+c+2+4) :=
  Fin.addCases
    (Fin.addCases
      (Fin.addCases
        (fun i => Fin.natAdd (c+c+2) i)
        (fun i => Fin.castAdd 4 (Fin.castAdd 2 (Fin.castAdd c i))))
      (fun i => Fin.castAdd 4 (Fin.castAdd 2 (Fin.natAdd c i))))
    (fun i => Fin.castAdd 4 (Fin.natAdd (c+c) i))

/-- Static placement of the initializer on the existing auxiliary controls. -/
def initPlacement (c : ℕ) : Fin (c+c+2+4) ≃ Fin (AuxTapes c) where
  toFun := Fin.addCases initTo (fun i => Fin.castAdd 2 (Fin.castAdd c (Fin.castAdd c i)))
  invFun := initInverse
  left_inv := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases <;>
          simp only [initTo,initInverse,Fin.addCases_left,Fin.addCases_right]
      | right i => simp only [initTo,initInverse,Fin.addCases_left,Fin.addCases_right]
    | right i => simp only [initInverse,Fin.addCases_left,Fin.addCases_right]
  right_inv := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases <;>
          simp only [initTo,initInverse,Fin.addCases_left,Fin.addCases_right]
      | right i => simp only [initTo,initInverse,Fin.addCases_left,Fin.addCases_right]
    | right i => simp only [initTo,initInverse,Fin.addCases_left,Fin.addCases_right]

private def controls {c : ℕ} (b : Tapes 4 0) (modulus current : Tapes c 0)
    (outer : Tapes 2 0) : Tapes (AuxTapes c) 0 :=
  ((b.append modulus).append current).append outer

private theorem active_controls {c : ℕ} (b : Tapes 4 0) (modulus current : Tapes c 0)
    (outer : Tapes 2 0) : Placement.active (initPlacement c) (controls b modulus current outer) =
      (modulus.append current).append outer := by
  unfold Placement.active initPlacement controls
  congr 1 <;> funext i <;> induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases <;> simp only [Equiv.coe_fn_mk,initTo,Tapes.append,Fin.addCases_left,Fin.addCases_right]
  | right i => simp only [Equiv.coe_fn_mk,initTo,Tapes.append,Fin.addCases_left,Fin.addCases_right]

private theorem extra_controls {c : ℕ} (b : Tapes 4 0) (modulus current : Tapes c 0)
    (outer : Tapes 2 0) : Placement.extra (initPlacement c) (controls b modulus current outer) = b := by
  unfold Placement.extra initPlacement controls
  cases b
  simp [Tapes.append]

private theorem replace_controls {c : ℕ} (b : Tapes 4 0)
    (modulus modulus' current current' : Tapes c 0) (outer outer' : Tapes 2 0) :
    Placement.replace (initPlacement c) (controls b modulus current outer)
      ((modulus'.append current').append outer') = controls b modulus' current' outer' := by
  rw [Placement.replace,extra_controls]
  simpa only [active_controls,extra_controls] using
    Placement.view (initPlacement c) (controls b modulus' current' outer')

/-- Actual auxiliary contents; residue cells can initially contain any symbols. -/
def auxiliary {c : ℕ} (dest : ℤ → Fin 4) (q : ℤ) (bs countBits : List Bool)
    (modulus current : Tapes c 0) : Tapes (AuxTapes c) 0 :=
  controls (CountedCopyReuse.bank empty dest empty (binary bs) 0 q 1 1) modulus current
    (CountedLoopReuse.controls empty (binary countBits) 1 1)

def initAuxProgram {c : ℕ} (hc : 0 < c) : Program (AuxTapes c) 20 0 :=
  Placement.placed (ScalingControlInit.program hc) (initPlacement c)

theorem initAux_hoare {c : ℕ} (hc : 0 < c) (Q : ℕ) (dest : ℤ → Fin 4) (q : ℤ)
    (bs countBits : List Bool) (modulus current : Tapes c 0)
    (hn : Counter.value countBits = Q) (cn : GrowingCounterData.Canonical countBits) :
    HoareTime (initAuxProgram hc)
      (fun v => v = auxiliary dest q bs countBits modulus current)
      (fun v => v = ScalingExecution.auxiliary hc Q dest q bs countBits modulus current)
      (14*Q+25) := by
  have hh := Placement.hoare_at (ScalingControlInit.init_hoare_linear hc modulus current countBits Q hn cn)
    (initPlacement c) (auxiliary dest q bs countBits modulus current)
    (active_controls _ _ _ _)
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  change Placement.replace (initPlacement c) (controls _ modulus current _)
    (((OneHot.bank modulus (OneHot.residue hc Q)).append
      (OneHot.bank current (OneHot.residue hc 0))).append _) = _
  rw [replace_controls]
  rfl

/-- Place auxiliary initialization after the fixed split-side bank. -/
def initProgram {c : ℕ} (hc : 0 < c) : Program (TapeCount c) 20 0 :=
  Placement.placed (initAuxProgram hc)
    (finAddFlip : Fin (AuxTapes c+SplitTapes c) ≃ Fin (TapeCount c))

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

/-- The full initial bank, without any precomputed residue control symbols. -/
def input {c : ℕ} (Q : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) :
    Tapes (TapeCount c) 0 :=
  (ScalingSplit.bank (putWord source p (ScalingExecution.inputWord Q payload)) background descriptors p origins).append
    (auxiliary dest q bs countBits modulus current)

private theorem init_hoare {c : ℕ} (hc : 0 < c) (Q : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4))
    (hn : Counter.value countBits = Q) (cn : GrowingCounterData.Canonical countBits) :
    HoareTime (initProgram hc)
      (fun v => v = input Q source p background origins dest q descriptors bs countBits modulus current payload)
      (fun v => v = ScalingExecution.input hc Q source p background origins dest q descriptors bs countBits modulus current payload)
      (14*Q+25) := by
  have hh := Placement.hoare_at (initAux_hoare hc Q dest q bs countBits modulus current hn cn)
    (finAddFlip : Fin (AuxTapes c+SplitTapes c) ≃ Fin (TapeCount c))
    (input Q source p background origins dest q descriptors bs countBits modulus current payload)
    (active_tail _ _)
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_tail _ _ _

/-- Final auxiliary state: output heads advance by the payload volume, residue
cells both encode Q modulo c, and both reusable clocks are clean. -/
def finalAuxiliary {c : ℕ} (hc : 0 < c) (Q B : ℕ) (dest : ℤ → Fin 4) (q : ℤ)
    (bs countBits : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) :
    Tapes (AuxTapes c) 0 :=
  auxiliary (putWord dest q (ScalingMerge.outputPrefix hc Q Q payload)) (q+((Q*B : ℕ) : ℤ)) bs countBits
    (OneHot.bank modulus (ScalingControl.residue hc Q)) (OneHot.bank current (ScalingControl.residue hc Q))

/-- Final complete bank, with every temporary source buffer and its head restored.
The initializer accepts these residue cells on the next invocation. -/
def output {c : ℕ} (hc : 0 < c) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) :
    Tapes (TapeCount c) 0 :=
  (ScalingSplit.bank (putWord source p (ScalingExecution.inputWord Q payload)) background descriptors
    (p+Q*B) origins).append (finalAuxiliary hc Q B dest q bs countBits modulus current payload)

private theorem input_length {Q B : ℕ} (payload : ℕ → List (Fin 4))
    (hwidth : ∀ y, (payload y).length = B) : (ScalingExecution.inputWord Q payload).length = Q*B := by
  unfold ScalingExecution.inputWord
  rw [BlockRotationData.uniform_volume B]
  · simp
  · intro block hm
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hm
    exact hwidth y

/-- Exact shared-buffer representation at the handoff from merge to cleanup. -/
private theorem finished_state {Q c B : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (source : ℤ → Fin 4) (p : ℤ) (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4))
    (hwidth : ∀ y, (payload y).length = B) :
    ScalingExecution.state hc Q B source p background origins dest q descriptors bs countBits modulus current payload Q =
    (ScalingSplit.bank (putWord source p (ScalingExecution.inputWord Q payload))
      (fun j => putWord (background j) (origins j)
        (ScalingSplit.piece Q c B (ScalingExecution.inputWord Q payload) j))
      descriptors (p+Q*B)
      (fun j => origins j+(ScalingSplit.piece Q c B (ScalingExecution.inputWord Q payload) j).length)).append
      (finalAuxiliary hc Q B dest q bs countBits modulus current payload) := by
  have hsource : ScalingMerge.sources hc Q B background origins payload Q =
      (⟨fun j => origins j+(ScalingSplit.piece Q c B (ScalingExecution.inputWord Q payload) j).length,
        fun j => putWord (background j) (origins j)
          (ScalingSplit.piece Q c B (ScalingExecution.inputWord Q payload) j)⟩ : Tapes c 0) := by
    unfold ScalingMerge.sources
    congr 1
    · funext j
      rw [ScalingMergeData.complete_count hQ hc hcop,
        ScalingSplit.piece_length hc _ (input_length payload hwidth)]
      simp only [ScalingSplit.offset,Nat.sub_mul]
    · funext j
      rw [ScalingExecution.inputWord,ScalingPieceBridge.piece_eq_blocks hc j payload (fun y _ => hwidth y)]
  unfold ScalingExecution.state
  rw [hsource]
  rfl

/-- Restore the temporary buffers on the split-side tape bank. -/
def cleanupProgram (c : ℕ) : Program (TapeCount c) (ScalingBuffersReset.states c) 0 :=
  extend (ScalingBuffersReset.program c) (AuxTapes c)

private theorem cleanup_hoare {Q c B : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (source : ℤ → Fin 4) (p : ℤ) (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4))
    (hwidth : ∀ y, (payload y).length = B)
    (hp : ∀ j, Counter.value (descriptors j) =
      (ScalingSplit.piece Q c B (ScalingExecution.inputWord Q payload) j).length)
    (cp : ∀ j, GrowingCounterData.Canonical (descriptors j))
    (hblank : ∀ j z, origins j ≤ z →
      z < origins j+(ScalingSplit.piece Q c B (ScalingExecution.inputWord Q payload) j).length →
      background j z = blank) :
    HoareTime (cleanupProgram c)
      (fun v => v = ScalingExecution.state hc Q B source p background origins dest q descriptors
        bs countBits modulus current payload Q)
      (fun v => v = output hc Q B source p background origins dest q descriptors bs countBits modulus current payload)
      (38*(Q*B)+72*c) := by
  have hh := (ScalingBuffersReset.reset_pieces_hoare_linear hc
    (putWord source p (ScalingExecution.inputWord Q payload)) background descriptors (p+Q*B) origins
    (ScalingExecution.inputWord Q payload) (input_length payload hwidth) hp hblank cp).extend
      (finalAuxiliary hc Q B dest q bs countBits modulus current payload)
  apply hh.consequence _ _ le_rfl
  · rintro v rfl
    refine ⟨_,rfl,?_⟩
    exact finished_state hQ hc hcop source p background origins dest q descriptors bs countBits
      modulus current payload hwidth
  · rintro v ⟨w,rfl,rfl⟩
    rfl

/-- All stages are actual finite-control programs on the same fixed bank. -/
def program {c : ℕ} (hc : 0 < c) : Program (TapeCount c)
    (20+((ScalingSplit.states c+ScalingSplit.states c)+(7+(c*16+1+2+5)+4))+ScalingBuffersReset.states c) 0 :=
  seq (seq (initProgram hc) (ScalingExecution.program hc)) (cleanupProgram c)

/-- Reusable positive unit scaling, including control initialization and buffer
cleanup. Payload, all source cells, all immutable descriptors and arbitrary
out-of-buffer backgrounds are preserved exactly as the complete banks state. -/
theorem scaling_hoare {Q c B : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (hB : 0 < B) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (hb : Counter.value bs = B) (hn : Counter.value countBits = Q)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical countBits)
    (payload : ℕ → List (Fin 4))
    (hp : ∀ j, Counter.value (descriptors j) =
      (ScalingSplit.piece Q c B (ScalingExecution.inputWord Q payload) j).length)
    (cp : ∀ j, GrowingCounterData.Canonical (descriptors j))
    (modulus current : Tapes c 0) (hwidth : ∀ y, (payload y).length = B)
    (hblank : ∀ j z, origins j ≤ z →
      z < origins j+(ScalingSplit.piece Q c B (ScalingExecution.inputWord Q payload) j).length →
      background j z = blank) :
    HoareTime (program hc)
      (fun v => v = input Q source p background origins dest q descriptors bs countBits modulus current payload)
      (fun v => v = output hc Q B source p background origins dest q descriptors bs countBits modulus current payload)
      (127*(Q*B)+120*c+52) := by
  have hi := init_hoare hc Q source p background origins dest q descriptors bs countBits modulus current payload hn cn
  have he := ScalingExecution.scaling_hoare hQ hc hcop hB source p background origins dest q descriptors
    bs countBits hb hn cb cn payload hp cp modulus current hwidth
  have hc' := cleanup_hoare hQ hc hcop source p background origins dest q descriptors bs countBits
    modulus current payload hwidth hp cp hblank
  apply ((hi.seq he).seq hc').consequence (fun _ h => h) (fun _ h => h) _
  have hQB : Q ≤ Q*B := by nlinarith
  omega

/-- The emitted payload is on the same literal destination slot as the main
scaling execution, after all temporary-buffer cleanup has completed. -/
theorem output_tape {c : ℕ} (hc : 0 < c) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) :
    (output hc Q B source p background origins dest q descriptors bs countBits modulus current payload).tape
      (ScalingExecution.destinationSlot c) = putWord dest q (ScalingMerge.outputPrefix hc Q Q payload) := by
  simp [output,finalAuxiliary,auxiliary,controls,ScalingExecution.destinationSlot,Tapes.append,CountedCopyReuse.bank]

/-- Each temporary buffer is restored literally, including outside cells. -/
theorem output_buffer {c : ℕ} (hc : 0 < c) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) (j : Fin c) :
    let v := output hc Q B source p background origins dest q descriptors bs countBits modulus current payload
    let slot := Fin.castAdd (AuxTapes c) (ScalingSplit.outputSlot j)
    v.tape slot = background j ∧ v.head slot = origins j := by
  simp [output,ScalingSplit.bank,ScalingSplit.outputSlot,Tapes.append]

/-- Fixed finite control, independent of the number and width of payload blocks. -/
theorem stateCount_eq (c : ℕ) :
    20+((ScalingSplit.states c+ScalingSplit.states c)+(7+(c*16+1+2+5)+4))+ScalingBuffersReset.states c =
      98*c+42 := by
  rw [ScalingExecution.stateCount_eq,ScalingBuffersReset.states_eq]
  omega

end IntegerMultBounds.Machine.ScalingExecutionReuse
