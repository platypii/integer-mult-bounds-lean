import IntegerMultBounds.Machine.TranslationExecutionReuse
import IntegerMultBounds.Machine.FiberShift

/-! Repeated literal translation on consecutive fibers. The same canonical
Q/a/B descriptors serve every fiber; all derived descriptors and work clocks
are constructed and erased by real transitions inside the loop body. -/

namespace IntegerMultBounds.Machine.TranslationStream

open CountedCopyReuse (empty binary)

def blocks (Q : ℕ) (payload : ℕ → List (Fin 4)) : List (List (Fin 4)) :=
  (List.range Q).map payload

def fibers (Q n : ℕ) (payload : ℕ → ℕ → List (Fin 4)) : List (List (Fin 4)) :=
  (List.range n).map (fun i => (blocks Q (payload i)).flatten)

def outputPrefix (a Q n : ℕ) (payload : ℕ → ℕ → List (Fin 4)) : List (Fin 4) :=
  ((List.range n).map (fun i => (BlockRotationData.rotate a (blocks Q (payload i))).flatten)).flatten

private theorem blocks_uniform (Q B i : ℕ) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) :
    BlockRotationData.Uniform B (blocks Q (payload i)) := by
  intro block hb
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
  exact hwidth i y

private theorem fiber_length (Q B i : ℕ) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) :
    (blocks Q (payload i)).flatten.length = Q*B := by
  rw [BlockRotationData.uniform_volume B _ (blocks_uniform Q B i payload hwidth)]
  simp [blocks]

theorem prefix_length (a Q B n : ℕ) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) :
    (outputPrefix a Q n payload).length = n*(Q*B) := by
  unfold outputPrefix
  rw [BlockRotationData.uniform_volume (Q*B)]
  · simp
  · intro word hw
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
    rw [BlockRotationData.payload_length]
    exact fiber_length Q B i payload hwidth

theorem prefix_succ (a Q n : ℕ) (payload : ℕ → ℕ → List (Fin 4)) :
    outputPrefix a Q (n+1) payload = outputPrefix a Q n payload ++
      (BlockRotationData.rotate a (blocks Q (payload n))).flatten := by
  simp [outputPrefix,List.range_succ,List.map_append,List.flatten_append]

private theorem source_fiber (Q B n i : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B) (hi : i < n) :
    putWord (putWord source p (fibers Q n payload).flatten) (p+((i*(Q*B) : ℕ) : ℤ))
      (blocks Q (payload i)).flatten = putWord source p (fibers Q n payload).flatten := by
  have hu : BlockRotationData.Uniform (Q*B) (fibers Q n payload) := by
    intro word hw
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hw
    exact fiber_length Q B j payload hwidth
  have hi' : i < (fibers Q n payload).length := by simpa [fibers] using hi
  have hh := FiberShift.source_fiber source p (fibers Q n payload) (Q*B) i hu hi'
  simpa [fibers] using hh

/-- Exact recurring workspace and the literal output prefix at a fiber boundary. -/
def state (a Q B n : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs as : List Bool)
    (payload : ℕ → ℕ → List (Fin 4)) (i : ℕ) : Tapes 12 0 :=
  TranslationExecutionReuse.bank (putWord source p (fibers Q n payload).flatten)
    (putWord dest q (outputPrefix a Q i payload))
    (p+((i*(Q*B) : ℕ) : ℤ)) (q+((i*(Q*B) : ℕ) : ℤ)) bs qs as

theorem body_hoare {Q a B n i : ℕ} (ha : a ≤ Q) (hB : 0 < B) (hi : i < n)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs as : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (ha' : Counter.value as = a)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (ca : GrowingCounterData.Canonical as) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) :
    HoareTime TranslationExecutionReuse.program
      (fun v => v = state a Q B n source dest p q bs qs as payload i)
      (fun v => v = state a Q B n source dest p q bs qs as payload (i+1))
      (207*(Q*B)+241) := by
  have hh := TranslationExecutionReuse.translate_hoare Q a B ha hB
    (putWord source p (fibers Q n payload).flatten) (putWord dest q (outputPrefix a Q i payload))
    (p+((i*(Q*B) : ℕ) : ℤ)) (q+((i*(Q*B) : ℕ) : ℤ))
    (blocks Q (payload i)) (by simp [blocks]) (blocks_uniform Q B i payload hwidth)
    bs qs as hb hq ha' cb cq ca
  unfold TranslationExecutionReuse.input TranslationExecutionReuse.output at hh
  rw [source_fiber Q B n i source p payload hwidth hi] at hh
  have hout : putWord (putWord dest q (outputPrefix a Q i payload)) (q+((i*(Q*B) : ℕ) : ℤ))
      (BlockRotationData.rotate a (blocks Q (payload i))).flatten =
      putWord dest q (outputPrefix a Q (i+1) payload) := by
    rw [← prefix_length a Q B i payload hwidth,putWord_append_forward,prefix_succ]
  rw [hout] at hh
  have hpos (r : ℤ) : r+(i : ℤ)*((Q : ℤ)*B)+(Q : ℤ)*B =
      r+((i+1 : ℕ) : ℤ)*((Q : ℤ)*B) := by push_cast; ring
  simpa only [state,Nat.cast_mul,hpos] using hh

/-- Repeated translation with a real count-copy, decrement, rewind and cleanup. -/
def loopProgram : Program 14 233 0 := CountedLoopReuse.program TranslationExecutionReuse.program

theorem loop_hoare {Q a B n : ℕ} (ha : a ≤ Q) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs as ns : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (ha' : Counter.value as = a)
    (hn : Counter.value ns = n) (cb : GrowingCounterData.Canonical bs)
    (cq : GrowingCounterData.Canonical qs) (ca : GrowingCounterData.Canonical as)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B) :
    HoareTime loopProgram
      (fun v => v = CountedLoopReuse.bank (state a Q B n source dest p q bs qs as payload 0) empty (binary ns) 1 1)
      (fun v => v = CountedLoopReuse.bank (state a Q B n source dest p q bs qs as payload n) empty (binary ns) 1 1)
      (n*(207*(Q*B)+247)+7*ns.length+16) := by
  have hh := CountedLoopReuse.loop_hoare TranslationExecutionReuse.program ns n
    (state a Q B n source dest p q bs qs as payload) (fun _ => 207*(Q*B)+241) hn
    (fun i hi => body_hoare ha hB hi source dest p q bs qs as hb hq ha' cb cq ca payload hwidth)
  have hcost : (∑ _i ∈ Finset.range n, (207*(Q*B)+241))+6*n+7*ns.length+16 =
      n*(207*(Q*B)+247)+7*ns.length+16 := by
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    ring
  simpa only [loopProgram,hcost] using hh

theorem source_length (Q B n : ℕ) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) :
    (fibers Q n payload).flatten.length = n*(Q*B) := by
  rw [BlockRotationData.uniform_volume (Q*B)]
  · simp [fibers]
  · intro word hw
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
    exact fiber_length Q B i payload hwidth

/-- Initial writable workspaces are genuinely blank; only Q/a/B/n are supplied. -/
def input (Q n : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs as ns : List Bool)
    (payload : ℕ → ℕ → List (Fin 4)) : Tapes 14 0 :=
  CountedLoopReuse.bank
    ((TranslationDescriptors.initial bs qs as).append
      (TranslationPreparedExecution.payload (putWord source p (fibers Q n payload).flatten) dest p q))
    (fun _ => blank) (binary ns) 0 1

private def markerMask (i : Fin 14) : Bool :=
  decide (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 12)

private def marked (v : Tapes 14 0) : Tapes 14 0 :=
  ⟨fun i => v.head i+if markerMask i then 1 else 0,
    fun i => if markerMask i then Function.update (v.tape i) (v.head i) separator else v.tape i⟩

/-- Install all six mutable sentinels in one literal transition. -/
def markerProgram : Program 14 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols => if state = 0 then
    some (1,fun i => if markerMask i then (separator,Move.right) else (symbols i,Move.stay)) else none

private theorem marker_hoare (v : Tapes 14 0) :
    HoareTime markerProgram (fun w => w = v) (fun w => w = marked v) 1 := by
  intro w hw
  subst w
  refine ⟨1,⟨1,(marked v).head,(marked v).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,markerProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i
      cases h : markerMask i <;> simp [h,marked,Move.offset]
    · funext i z
      cases h : markerMask i <;> by_cases hz : z = v.head i <;> simp [h,marked,hz]
  · simp [step,markerProgram]

private theorem marker_input (a Q B n : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs as ns : List Bool) (payload : ℕ → ℕ → List (Fin 4)) :
    marked (input Q n source dest p q bs qs as ns payload) =
      CountedLoopReuse.bank (state a Q B n source dest p q bs qs as payload 0) empty (binary ns) 1 1 := by
  unfold marked markerMask input state TranslationExecutionReuse.bank TranslationPreparedExecution.bank
    TranslationDescriptors.initial TranslationDescriptors.bank TranslationProduct.bank
    ScalingDescriptors.innerBank ScalingDescriptors.counters CountedLoopReuse.bank
    CountedLoopReuse.controls TranslationPreparedExecution.payload Tapes.append
  congr 1
  · funext i
    fin_cases i <;> simp [Fin.addCases]
  · funext i z
    fin_cases i <;> simp [Fin.addCases,binary,empty,putBits,Function.update_apply,outputPrefix,putWord]

/-- One fixed 235-state machine for arbitrary family count and fixed runtime offset. -/
def program : Program 14 235 0 := seq markerProgram loopProgram

theorem translate_hoare {Q a B n : ℕ} (ha : a ≤ Q) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs as ns : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (ha' : Counter.value as = a)
    (hn : Counter.value ns = n) (cb : GrowingCounterData.Canonical bs)
    (cq : GrowingCounterData.Canonical qs) (ca : GrowingCounterData.Canonical as)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B) :
    HoareTime program
      (fun v => v = input Q n source dest p q bs qs as ns payload)
      (fun v => v = CountedLoopReuse.bank (state a Q B n source dest p q bs qs as payload n) empty (binary ns) 1 1)
      (n*(207*(Q*B)+247)+7*ns.length+18) := by
  have hm := marker_hoare (input Q n source dest p q bs qs as ns payload)
  rw [marker_input a Q B n source dest p q bs qs as ns payload] at hm
  have hh := hm.seq (loop_hoare ha hB source dest p q bs qs as ns hb hq ha' hn cb cq ca payload hwidth)
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- The per-fiber setup cost is absorbed into positive physical fiber volume. -/
theorem linear_bound (Q B n : ℕ) (ns : List Bool) (hQ : 0 < Q) (hB : 0 < B)
    (hw : ns.length ≤ n+1) :
    n*(207*(Q*B)+247)+7*ns.length+18 ≤ 461*(n*(Q*B))+25 := by
  have hvol : 1 ≤ Q*B := by nlinarith
  have hnvol : n ≤ n*(Q*B) := by nlinarith
  nlinarith

/-- Complete volume-linear literal translation with no derived descriptor inputs. -/
theorem translate_hoare_linear {Q a B n : ℕ} (hQ : 0 < Q) (ha : a ≤ Q) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs as ns : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (ha' : Counter.value as = a)
    (hn : Counter.value ns = n) (cb : GrowingCounterData.Canonical bs)
    (cq : GrowingCounterData.Canonical qs) (ca : GrowingCounterData.Canonical as)
    (cn : GrowingCounterData.Canonical ns) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) :
    HoareTime program
      (fun v => v = input Q n source dest p q bs qs as ns payload)
      (fun v => v = CountedLoopReuse.bank (state a Q B n source dest p q bs qs as payload n) empty (binary ns) 1 1)
      (461*(fibers Q n payload).flatten.length+25) := by
  have hw := GrowingCounterData.canonical_width ns cn
  have hl := Nat.log2_le_self (Counter.value ns)
  have hbound := linear_bound Q B n ns hQ hB (by omega)
  rw [← source_length Q B n payload hwidth] at hbound
  exact (translate_hoare ha hB source dest p q bs qs as ns hb hq ha' hn cb cq ca payload hwidth).consequence
    (fun _ h => h) (fun _ h => h) hbound

end IntegerMultBounds.Machine.TranslationStream
