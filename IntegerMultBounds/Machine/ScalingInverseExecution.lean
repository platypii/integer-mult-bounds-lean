import IntegerMultBounds.Machine.ScalingExecution
import IntegerMultBounds.Machine.ScalingConcatenate
import IntegerMultBounds.Machine.ScalingPartitionData
import IntegerMultBounds.Machine.ScalingControlInit
import IntegerMultBounds.Machine.ScalingBuffersReset

/-! Reusable literal inverse positive-unit scaling. Both residue banks are initialized
from arbitrary scanned cells; scatter and concatenation are physically executed,
and every temporary piece buffer is erased and rewound. Binary descriptors
remain explicit immutable inputs; no hidden preparation cost is claimed. -/

namespace IntegerMultBounds.Machine.ScalingInverseExecution

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
def auxiliary {c : ℕ} (source : ℤ → Fin 4) (p : ℤ) (bs countBits : List Bool)
    (modulus current : Tapes c 0) : Tapes (AuxTapes c) 0 :=
  controls (CountedCopyReuse.bank source empty empty (binary bs) p 0 1 1) modulus current
    (CountedLoopReuse.controls empty (binary countBits) 1 1)

def initAuxProgram {c : ℕ} (hc : 0 < c) : Program (AuxTapes c) 20 0 :=
  Placement.placed (ScalingControlInit.program hc) (initPlacement c)

theorem initAux_hoare {c : ℕ} (hc : 0 < c) (Q : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (bs countBits : List Bool) (modulus current : Tapes c 0)
    (hn : Counter.value countBits = Q) (cn : GrowingCounterData.Canonical countBits) :
    HoareTime (initAuxProgram hc)
      (fun v => v = auxiliary source p bs countBits modulus current)
      (fun v => v = auxiliary source p bs countBits
        (OneHot.bank modulus (ScalingControl.residue hc Q)) (OneHot.bank current (ScalingControl.residue hc 0)))
      (14*Q+25) := by
  have hh := Placement.hoare_at (ScalingControlInit.init_hoare_linear hc modulus current countBits Q hn cn)
    (initPlacement c) (auxiliary source p bs countBits modulus current)
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



/-- The inverse permutation reads input at c*y modulo Q for output y. -/
def outputWord (Q c : ℕ) (payload : ℕ → List (Fin 4)) : List (Fin 4) :=
  ((List.range Q).map (fun y => payload (ScalingPieces.output Q c y))).flatten

def words {c : ℕ} (Q : ℕ) (payload : ℕ → List (Fin 4)) (j : Fin c) : List (Fin 4) :=
  (ScalingScatter.targetBlocks Q c j.val payload).flatten

theorem words_flatten {c : ℕ} (hc : 0 < c) (Q : ℕ) (payload : ℕ → List (Fin 4)) :
    (List.ofFn (words (c := c) Q payload)).flatten = outputWord Q c payload := by
  have he : List.ofFn (words (c := c) Q payload) =
      (List.ofFn (fun j : Fin c => ScalingMergeData.blocks Q c j.val
        (fun y => payload (ScalingPieces.output Q c y)))).map List.flatten := by
    rw [List.map_ofFn]
    rfl
  rw [he,← List.flatten_flatten,ScalingPartitionData.blocks_ofFn hc]
  rfl

theorem output_length {Q c B : ℕ} (payload : ℕ → List (Fin 4))
    (hwidth : ∀ y, (payload y).length = B) : (outputWord Q c payload).length = Q*B := by
  unfold outputWord
  rw [BlockRotationData.uniform_volume B]
  · simp
  · intro block hm
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hm
    exact hwidth _

theorem word_eq_piece {Q c B : ℕ} (hc : 0 < c) (payload : ℕ → List (Fin 4))
    (hwidth : ∀ y, (payload y).length = B) (j : Fin c) :
    words Q payload j = ScalingSplit.piece Q c B (outputWord Q c payload) j := by
  unfold outputWord
  rw [ScalingPieceBridge.piece_eq_blocks hc j _ (fun y _ => hwidth _)]
  rfl

private def splitControl (dest : ℤ → Fin 4) (q : ℤ) : Tapes 4 0 :=
  CountedCopyReuse.bank dest (fun _ => blank) empty (fun _ => blank) q 0 1 0

private def scatterControl (source : ℤ → Fin 4) (p : ℤ) (bs : List Bool) : Tapes 4 0 :=
  CountedCopyReuse.bank source empty empty (binary bs) p 0 1 1

private def descriptorBank {c : ℕ} (descriptors : Fin c → List Bool) : Tapes c 0 :=
  ⟨fun _ => 1,fun j => binary (descriptors j)⟩

/-- Unprepared residue cells and initially empty temporary buffers. -/
def input {c : ℕ} (Q : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) :
    Tapes (TapeCount c) 0 :=
  (ScalingSplit.bank dest background descriptors q origins).append
    (auxiliary (putWord source p (ScalingScatter.inputWord Q payload)) p bs countBits modulus current)

/-- Global bank while the original input stream is scattered into shared buffers. -/
def state {c : ℕ} (hc : 0 < c) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (modulus current : Tapes c 0)
    (payload : ℕ → List (Fin 4)) (z : ℕ) : Tapes (TapeCount c) 0 :=
  ScalingExecution.join (splitControl dest q) (ScalingScatter.buffers hc Q B background origins payload z)
    (descriptorBank descriptors)
    (scatterControl (putWord source p (ScalingScatter.inputWord Q payload)) (p+((z*B : ℕ) : ℤ)) bs)
    (OneHot.bank modulus (ScalingControl.residue hc Q)) (OneHot.bank current (ScalingControl.residue hc z))
    (CountedLoopReuse.controls empty (binary countBits) 1 1)

/-- Read-only source at its consumed end and retained residue/binary controls. -/
def finalAuxiliary {c : ℕ} (hc : 0 < c) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (bs countBits : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) :
    Tapes (AuxTapes c) 0 :=
  auxiliary (putWord source p (ScalingScatter.inputWord Q payload)) (p+((Q*B : ℕ) : ℤ)) bs countBits
    (OneHot.bank modulus (ScalingControl.residue hc Q)) (OneHot.bank current (ScalingControl.residue hc Q))

/-- Complete final bank: inverse-scaled destination and restored temporary buffers. -/
def output {c : ℕ} (hc : 0 < c) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) :
    Tapes (TapeCount c) 0 :=
  (ScalingSplit.bank (putWord dest q (outputWord Q c payload)) background descriptors
    (q+((Q*B : ℕ) : ℤ)) origins).append
    (finalAuxiliary hc Q B source p bs countBits modulus current payload)

section Execution
variable {Q c B : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (source : ℤ → Fin 4) (p : ℤ) (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4))

private theorem init_hoare (hn : Counter.value countBits = Q) (cn : GrowingCounterData.Canonical countBits) :
    HoareTime (initProgram hc)
      (fun v => v = input Q source p background origins dest q descriptors bs countBits modulus current payload)
      (fun v => v = state hc Q B source p background origins dest q descriptors bs countBits modulus current payload 0)
      (14*Q+25) := by
  have hh := Placement.hoare_at
    (initAux_hoare hc Q (putWord source p (ScalingScatter.inputWord Q payload)) p bs countBits modulus current hn cn)
    (finAddFlip : Fin (AuxTapes c+SplitTapes c) ≃ Fin (TapeCount c))
    (input Q source p background origins dest q descriptors bs countBits modulus current payload)
    (active_tail _ _)
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [show input Q source p background origins dest q descriptors bs countBits modulus current payload =
    (ScalingSplit.bank dest background descriptors q origins).append
      (auxiliary (putWord source p (ScalingScatter.inputWord Q payload)) p bs countBits modulus current) from rfl,
    replace_tail]
  unfold state
  rw [ScalingScatter.buffers_initial]
  simp only [zero_mul,Nat.cast_zero,add_zero]
  rfl

include hQ hcop in
private theorem scatter_hoare (hB : 0 < B) (hb : Counter.value bs = B) (hn : Counter.value countBits = Q)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical countBits)
    (hwidth : ∀ y, (payload y).length = B) :
    HoareTime (Placement.placed (ScalingScatter.program hc) (ScalingExecution.placement c))
      (fun v => v = state hc Q B source p background origins dest q descriptors bs countBits modulus current payload 0)
      (fun v => v = state hc Q B source p background origins dest q descriptors bs countBits modulus current payload Q)
      (51*(Q*B)+23) := by
  have ha : Placement.active (ScalingExecution.placement c)
      (state hc Q B source p background origins dest q descriptors bs countBits modulus current payload 0) =
      CountedLoopReuse.bank (ScalingScatter.state hc Q B background origins source p bs modulus current payload 0)
        empty (binary countBits) 1 1 := by
    rw [state,ScalingExecution.active_join]
    rfl
  have hh := Placement.hoare_at (ScalingScatter.scatter_hoare_linear hQ hc hcop hB background origins source p
    bs countBits hb hn cb cn modulus current payload hwidth) (ScalingExecution.placement c) _ ha
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  unfold state CountedLoopReuse.bank ScalingScatter.state ScalingScatter.bank ScalingScatter.core
  exact ScalingExecution.replace_join _ _ _ _ _ _ _ _ _ _ _ _

include hQ hcop in
private theorem finished_state (hwidth : ∀ y, (payload y).length = B) :
    state hc Q B source p background origins dest q descriptors bs countBits modulus current payload Q =
    (ScalingSplit.bank dest (fun j => putWord (background j) (origins j) (words Q payload j))
      descriptors q (fun j => origins j+(words Q payload j).length)).append
      (finalAuxiliary hc Q B source p bs countBits modulus current payload) := by
  have he : ScalingScatter.buffers hc Q B background origins payload Q =
      (⟨fun j => origins j+(words Q payload j).length,
        fun j => putWord (background j) (origins j) (words Q payload j)⟩ : Tapes c 0) := by
    change Tapes.mk _ _ = Tapes.mk _ _
    congr 1
    · funext j
      rw [ScalingMergeData.complete_count hQ hc hcop]
      have hl : (words Q payload j).length =
          (ScalingControl.boundary Q c (j.val+1)-ScalingControl.boundary Q c j.val)*B := by
        unfold words ScalingScatter.targetBlocks
        rw [BlockRotationData.uniform_volume B]
        · simp [ScalingMergeData.blocks]
        · intro block hm
          obtain ⟨y,_,rfl⟩ := List.mem_map.mp hm
          exact hwidth _
      simp only [hl]
    · funext j
      exact ScalingScatter.buffers_final_tape hQ hc hcop B background origins payload j
  unfold state
  rw [he]
  rfl
end Execution

/-- The four stages share literal buffers and immutable descriptors. -/
def program {c : ℕ} (hc : 0 < c) : Program (TapeCount c)
    (20+(7+(c*16+1+2+5)+4)+ScalingConcatenate.states c+ScalingBuffersReset.states c) 0 :=
  seq (seq (seq (initProgram hc)
    (Placement.placed (ScalingScatter.program hc) (ScalingExecution.placement c)))
    (extend (ScalingConcatenate.program c) (AuxTapes c)))
    (extend (ScalingBuffersReset.program c) (AuxTapes c))

/-- Full reusable inverse-unit scaling with physically initialized residue
controls, scatter, concatenation and buffer cleanup. Prepared binary descriptors
are retained, every source cell survives, and no scratch output remains. -/
theorem scaling_hoare {Q c B : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (hB : 0 < B) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (hb : Counter.value bs = B) (hn : Counter.value countBits = Q)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical countBits)
    (payload : ℕ → List (Fin 4))
    (hp : ∀ j, Counter.value (descriptors j) = (words Q payload j).length)
    (cp : ∀ j, GrowingCounterData.Canonical (descriptors j))
    (modulus current : Tapes c 0) (hwidth : ∀ y, (payload y).length = B)
    (hblank : ∀ j z, origins j ≤ z → z < origins j+(words Q payload j).length → background j z = blank) :
    HoareTime (program hc)
      (fun v => v = input Q source p background origins dest q descriptors bs countBits modulus current payload)
      (fun v => v = output hc Q B source p background origins dest q descriptors bs countBits modulus current payload)
      (127*(Q*B)+120*c+51) := by
  have hi := init_hoare (B := B) hc source p background origins dest q descriptors bs countBits modulus current payload hn cn
  have hs := scatter_hoare hQ hc hcop source p background origins dest q descriptors bs countBits modulus current
    payload hB hb hn cb cn hwidth
  let aux := finalAuxiliary hc Q B source p bs countBits modulus current payload
  let afterConcat :=
    (ScalingSplit.bank (putWord dest q (outputWord Q c payload))
      (fun j => putWord (background j) (origins j) (words Q payload j)) descriptors
      (q+((Q*B : ℕ) : ℤ)) (fun j => origins j+(words Q payload j).length)).append aux
  have hlen := output_length (Q := Q) (c := c) payload hwidth
  have hc₀ := (ScalingConcatenate.concatenate_hoare_linear dest background descriptors q origins
    (words Q payload) hp cp).extend aux
  have hconcat : HoareTime (extend (ScalingConcatenate.program c) (AuxTapes c))
      (fun v => v = state hc Q B source p background origins dest q descriptors bs countBits modulus current payload Q)
      (fun v => v = afterConcat) (24*(Q*B)+48*c) := by
    apply hc₀.consequence _ _ _
    · rintro v rfl
      refine ⟨_,rfl,?_⟩
      exact finished_state hQ hc hcop source p background origins dest q descriptors bs countBits modulus current payload hwidth
    · rintro v ⟨w,rfl,rfl⟩
      simp only [words_flatten hc,hlen]
      rfl
    · rw [words_flatten hc,hlen]
  have hp' : ∀ j, Counter.value (descriptors j) =
      (ScalingSplit.piece Q c B (outputWord Q c payload) j).length := by
    intro j
    rw [← word_eq_piece hc payload hwidth j]
    exact hp j
  have hblank' : ∀ j z, origins j ≤ z →
      z < origins j+(ScalingSplit.piece Q c B (outputWord Q c payload) j).length → background j z = blank := by
    simpa only [← word_eq_piece hc payload hwidth] using hblank
  have hr₀ := (ScalingBuffersReset.reset_pieces_hoare_linear hc
    (putWord dest q (outputWord Q c payload)) background descriptors (q+((Q*B : ℕ) : ℤ)) origins
    (outputWord Q c payload) hlen hp' hblank' cp).extend aux
  have hreset : HoareTime (extend (ScalingBuffersReset.program c) (AuxTapes c))
      (fun v => v = afterConcat)
      (fun v => v = output hc Q B source p background origins dest q descriptors bs countBits modulus current payload)
      (38*(Q*B)+72*c) := by
    apply hr₀.consequence _ _ le_rfl
    · rintro v rfl
      refine ⟨_,rfl,?_⟩
      simp only [afterConcat,word_eq_piece hc payload hwidth]
    · rintro v ⟨w,rfl,rfl⟩
      rfl
  apply (((hi.seq hs).seq hconcat).seq hreset).consequence (fun _ h => h) (fun _ h => h) _
  have hv : Q ≤ Q*B := by nlinarith
  omega

/-- The inverse result is on the split-side tape zero in this shared layout. -/
def destinationSlot (c : ℕ) : Fin (TapeCount c) := Fin.castAdd (AuxTapes c) (Fin.castAdd (c+c) (0 : Fin 4))

theorem output_tape {c : ℕ} (hc : 0 < c) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) :
    (output hc Q B source p background origins dest q descriptors bs countBits modulus current payload).tape
      (destinationSlot c) = putWord dest q (outputWord Q c payload) := by
  simp [output,destinationSlot,ScalingSplit.bank,Tapes.append,CountedCopyReuse.bank]

theorem output_buffer {c : ℕ} (hc : 0 < c) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) (j : Fin c) :
    let v := output hc Q B source p background origins dest q descriptors bs countBits modulus current payload
    let slot := Fin.castAdd (AuxTapes c) (ScalingSplit.outputSlot j)
    v.tape slot = background j ∧ v.head slot = origins j := by
  simp [output,ScalingSplit.bank,ScalingSplit.outputSlot,Tapes.append]

theorem stateCount_eq (c : ℕ) :
    20+(7+(c*16+1+2+5)+4)+ScalingConcatenate.states c+ScalingBuffersReset.states c = 98*c+41 := by
  have hs : ScalingConcatenate.states c = 1+32*c := by
    induction c with
    | zero => rfl
    | succ c ih => simp only [ScalingConcatenate.states,ih]; omega
  rw [hs,ScalingBuffersReset.states_eq]
  omega

end IntegerMultBounds.Machine.ScalingInverseExecution
