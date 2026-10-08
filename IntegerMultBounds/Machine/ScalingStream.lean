import IntegerMultBounds.Machine.ScalingExecutionReuse

/-! Repeated literal positive-unit scaling on consecutive equal-size fibers.
Every fiber physically initializes residue controls and restores its temporary
buffers. The outer descriptor and clock are prepared, consumed, and cleaned by
the actual reusable counted loop. -/

namespace IntegerMultBounds.Machine.ScalingStream

open CountedCopyReuse (empty binary)

/-- The original unscaled fibers, each comprising Q consecutive B-symbol blocks. -/
def fibers (Q n : ℕ) (payload : ℕ → ℕ → List (Fin 4)) : List (List (Fin 4)) :=
  (List.range n).map (fun i => ScalingExecution.inputWord Q (payload i))

/-- Exact prefix of the fiberwise scaled output. -/
def outputPrefix {c : ℕ} (hc : 0 < c) (Q n : ℕ) (payload : ℕ → ℕ → List (Fin 4)) : List (Fin 4) :=
  ((List.range n).map (fun i => ScalingMerge.outputPrefix hc Q Q (payload i))).flatten

private theorem fiber_length (Q B i : ℕ) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) :
    (ScalingExecution.inputWord Q (payload i)).length = Q*B := by
  unfold ScalingExecution.inputWord
  rw [BlockRotationData.uniform_volume B]
  · simp
  · intro block hb
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
    exact hwidth i y

private theorem scaled_length {c : ℕ} (hc : 0 < c) (Q B i : ℕ)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B) :
    (ScalingMerge.outputPrefix hc Q Q (payload i)).length = Q*B := by
  unfold ScalingMerge.outputPrefix
  rw [BlockRotationData.uniform_volume B]
  · simp
  · intro block hb
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
    exact hwidth i _

theorem prefix_length {c : ℕ} (hc : 0 < c) (Q B n : ℕ)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B) :
    (outputPrefix hc Q n payload).length = n*(Q*B) := by
  unfold outputPrefix
  rw [BlockRotationData.uniform_volume (Q*B)]
  · simp
  · intro word hw
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
    exact scaled_length hc Q B i payload hwidth

theorem prefix_succ {c : ℕ} (hc : 0 < c) (Q n : ℕ) (payload : ℕ → ℕ → List (Fin 4)) :
    outputPrefix hc Q (n+1) payload = outputPrefix hc Q n payload ++
      ScalingMerge.outputPrefix hc Q Q (payload n) := by
  simp [outputPrefix,List.range_succ,List.map_append,List.flatten_append]

private theorem source_fiber (Q B n i : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B) (hi : i < n) :
    putWord (putWord source p (fibers Q n payload).flatten) (p+((i*(Q*B) : ℕ) : ℤ))
      (ScalingExecution.inputWord Q (payload i)) = putWord source p (fibers Q n payload).flatten := by
  have hu : BlockRotationData.Uniform (Q*B) (fibers Q n payload) := by
    intro word hw
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hw
    exact fiber_length Q B j payload hwidth
  have hi' : i < (fibers Q n payload).length := by simpa [fibers] using hi
  have hh := FiberShift.source_fiber source p (fibers Q n payload) (Q*B) i hu hi'
  simpa [fibers] using hh

/-- Controls are arbitrary before the first fiber, then hold the last residue.
Every subsequent body still initializes these cells with real transitions. -/
def residueState {c : ℕ} (hc : 0 < c) (Q i : ℕ) (v : Tapes c 0) : Tapes c 0 :=
  if i = 0 then v else OneHot.bank v (ScalingControl.residue hc Q)

theorem residueState_step {c : ℕ} (hc : 0 < c) (Q i : ℕ) (v : Tapes c 0) :
    OneHot.bank (residueState hc Q i v) (ScalingControl.residue hc Q) =
      residueState hc Q (i+1) v := by
  by_cases hi : i = 0 <;> simp [residueState,hi]

/-- Full physical bank at a fiber boundary: buffers and descriptors are ready,
source/destination heads point at the next fiber, and only output prefix grows. -/
def state {c : ℕ} (hc : 0 < c) (Q B n : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (modulus current : Tapes c 0)
    (payload : ℕ → ℕ → List (Fin 4)) (i : ℕ) : Tapes (ScalingExecution.TapeCount c) 0 :=
  (ScalingSplit.bank (putWord source p (fibers Q n payload).flatten) background descriptors
    (p+((i*(Q*B) : ℕ) : ℤ)) origins).append
    (ScalingExecutionReuse.auxiliary (putWord dest q (outputPrefix hc Q i payload))
      (q+((i*(Q*B) : ℕ) : ℤ)) bs countBits (residueState hc Q i modulus) (residueState hc Q i current))

/-- A physical source-and-destination step for one complete fiber, including
control initialization and restoration of all temporary payload buffers. -/
theorem body_hoare {Q c B n i : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (hB : 0 < B) (hi : i < n) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (hb : Counter.value bs = B) (hn : Counter.value countBits = Q)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical countBits)
    (hp : ∀ j, Counter.value (descriptors j) =
      ScalingSplit.offset Q c B (j.val+1)-ScalingSplit.offset Q c B j.val)
    (cp : ∀ j, GrowingCounterData.Canonical (descriptors j))
    (modulus current : Tapes c 0) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B)
    (hblank : ∀ j z, origins j ≤ z → z < origins j+
      ((ScalingSplit.offset Q c B (j.val+1)-ScalingSplit.offset Q c B j.val : ℕ) : ℤ) → background j z = blank) :
    HoareTime (ScalingExecutionReuse.program hc)
      (fun v => v = state hc Q B n source p background origins dest q descriptors bs countBits modulus current payload i)
      (fun v => v = state hc Q B n source p background origins dest q descriptors bs countBits modulus current payload (i+1))
      (127*(Q*B)+120*c+52) := by
  have hlength (j : Fin c) := ScalingSplit.piece_length hc (ScalingExecution.inputWord Q (payload i))
    (fiber_length Q B i payload hwidth) j
  have hh := ScalingExecutionReuse.scaling_hoare hQ hc hcop hB
    (putWord source p (fibers Q n payload).flatten) (p+((i*(Q*B) : ℕ) : ℤ)) background origins
    (putWord dest q (outputPrefix hc Q i payload)) (q+((i*(Q*B) : ℕ) : ℤ)) descriptors
    bs countBits hb hn cb cn (payload i) (fun j => (hp j).trans (hlength j).symm) cp
    (residueState hc Q i modulus) (residueState hc Q i current) (hwidth i)
    (by intro j z hl hu; rw [hlength j] at hu; exact hblank j z hl hu)
  unfold ScalingExecutionReuse.input ScalingExecutionReuse.output ScalingExecutionReuse.finalAuxiliary at hh
  rw [source_fiber Q B n i source p payload hwidth hi] at hh
  have hout : putWord (putWord dest q (outputPrefix hc Q i payload)) (q+((i*(Q*B) : ℕ) : ℤ))
      (ScalingMerge.outputPrefix hc Q Q (payload i)) = putWord dest q (outputPrefix hc Q (i+1) payload) := by
    rw [← prefix_length hc Q B i payload hwidth,putWord_append_forward,prefix_succ]
  rw [hout,residueState_step,residueState_step] at hh
  have hpos (r : ℤ) : r+(i : ℤ)*((Q : ℤ)*B)+(Q : ℤ)*B =
      r+((i+1 : ℕ) : ℤ)*((Q : ℤ)*B) := by
    push_cast
    ring
  simpa only [state,Nat.cast_mul,hpos] using hh

/-- A fixed reusable counted loop around the complete scaling fiber machine. -/
def program {c : ℕ} (hc : 0 < c) : Program (ScalingExecution.TapeCount c+2)
    (7+(20+((ScalingSplit.states c+ScalingSplit.states c)+(7+(c*16+1+2+5)+4))+
      ScalingBuffersReset.states c+5)+4) 0 :=
  CountedLoopReuse.program (ScalingExecutionReuse.program hc)

/-- Complete repeated scaling with an exact physical boundary invariant.
All per-fiber and outer descriptors survive and every work clock is restored. -/
theorem scale_hoare {Q c B n : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (hB : 0 < B) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits outerBits : List Bool) (hb : Counter.value bs = B) (hn : Counter.value countBits = Q)
    (ho : Counter.value outerBits = n)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical countBits)
    (hp : ∀ j, Counter.value (descriptors j) =
      ScalingSplit.offset Q c B (j.val+1)-ScalingSplit.offset Q c B j.val)
    (cp : ∀ j, GrowingCounterData.Canonical (descriptors j))
    (modulus current : Tapes c 0) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B)
    (hblank : ∀ j z, origins j ≤ z → z < origins j+
      ((ScalingSplit.offset Q c B (j.val+1)-ScalingSplit.offset Q c B j.val : ℕ) : ℤ) → background j z = blank) :
    HoareTime (program hc)
      (fun v => v = CountedLoopReuse.bank
        (state hc Q B n source p background origins dest q descriptors bs countBits modulus current payload 0)
        empty (binary outerBits) 1 1)
      (fun v => v = CountedLoopReuse.bank
        (state hc Q B n source p background origins dest q descriptors bs countBits modulus current payload n)
        empty (binary outerBits) 1 1)
      (n*(127*(Q*B)+120*c+58)+7*outerBits.length+16) := by
  have hh := CountedLoopReuse.loop_hoare (ScalingExecutionReuse.program hc) outerBits n
    (state hc Q B n source p background origins dest q descriptors bs countBits modulus current payload)
    (fun _ => 127*(Q*B)+120*c+52) ho
    (fun i hi => body_hoare hQ hc hcop hB hi source p background origins dest q descriptors
      bs countBits hb hn cb cn hp cp modulus current payload hwidth hblank)
  have hcost : (∑ _i ∈ Finset.range n, (127*(Q*B)+120*c+52))+6*n+7*outerBits.length+16 =
      n*(127*(Q*B)+120*c+58)+7*outerBits.length+16 := by
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    ring
  simpa only [program,hcost] using hh

/-- Total physical source volume, equal to the final output volume. -/
theorem source_length (Q B n : ℕ) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) :
    (fibers Q n payload).flatten.length = n*(Q*B) := by
  rw [BlockRotationData.uniform_volume (Q*B)]
  · simp [fibers]
  · intro word hw
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
    exact fiber_length Q B i payload hwidth

/-- Fixed-c additive per-fiber costs are absorbed into the volume coefficient
because every fiber has positive physical volume. -/
theorem linear_bound (Q B c n : ℕ) (outerBits : List Bool) (hQ : 0 < Q) (hB : 0 < B)
    (hw : outerBits.length ≤ n+1) :
    n*(127*(Q*B)+120*c+58)+7*outerBits.length+16 ≤ (192+120*c)*(n*(Q*B))+23 := by
  have hvol : 1 ≤ Q*B := by nlinarith
  have hnvol : n ≤ n*(Q*B) := by nlinarith
  have hcvol := Nat.mul_le_mul_left (120*c+65) hnvol
  nlinarith

/-- A complete volume-linear machine for any number of successive fibers,
with a coefficient depending only on the fixed multiplier c. -/
theorem scale_hoare_linear {Q c B n : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (hB : 0 < B) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits outerBits : List Bool) (hb : Counter.value bs = B) (hn : Counter.value countBits = Q)
    (ho : Counter.value outerBits = n)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical countBits)
    (co : GrowingCounterData.Canonical outerBits)
    (hp : ∀ j, Counter.value (descriptors j) =
      ScalingSplit.offset Q c B (j.val+1)-ScalingSplit.offset Q c B j.val)
    (cp : ∀ j, GrowingCounterData.Canonical (descriptors j))
    (modulus current : Tapes c 0) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B)
    (hblank : ∀ j z, origins j ≤ z → z < origins j+
      ((ScalingSplit.offset Q c B (j.val+1)-ScalingSplit.offset Q c B j.val : ℕ) : ℤ) → background j z = blank) :
    HoareTime (program hc)
      (fun v => v = CountedLoopReuse.bank
        (state hc Q B n source p background origins dest q descriptors bs countBits modulus current payload 0)
        empty (binary outerBits) 1 1)
      (fun v => v = CountedLoopReuse.bank
        (state hc Q B n source p background origins dest q descriptors bs countBits modulus current payload n)
        empty (binary outerBits) 1 1)
      ((192+120*c)*(fibers Q n payload).flatten.length+23) := by
  have hw := GrowingCounterData.canonical_width outerBits co
  have hl := Nat.log2_le_self (Counter.value outerBits)
  have hbnd := linear_bound Q B c n outerBits hQ hB (by omega)
  rw [← source_length Q B n payload hwidth] at hbnd
  exact (scale_hoare hQ hc hcop hB source p background origins dest q descriptors
    bs countBits outerBits hb hn ho cb cn hp cp modulus current payload hwidth hblank).consequence
      (fun _ h => h) (fun _ h => h) hbnd

/-- Tape and finite-control sizes depend only on the fixed multiplier. -/
theorem tapeCount_eq (c : ℕ) : ScalingExecution.TapeCount c+2 = 12+4*c := by
  rw [ScalingExecution.tapeCount_eq]
  omega

theorem stateCount_eq (c : ℕ) :
    7+(20+((ScalingSplit.states c+ScalingSplit.states c)+(7+(c*16+1+2+5)+4))+
      ScalingBuffersReset.states c+5)+4 = 98*c+58 := by
  rw [ScalingExecutionReuse.stateCount_eq]
  omega

end IntegerMultBounds.Machine.ScalingStream
