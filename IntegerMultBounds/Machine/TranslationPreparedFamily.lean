import IntegerMultBounds.Machine.TranslationStream

/-! Literal varying-offset translation. A single fixed offset-preparation
machine physically updates the canonical offset descriptor and any spectator
workspace. Its exact whole-bank contract is composed with descriptor synthesis,
rotation, metadata cleanup and an actual reusable outer counted loop. -/

namespace IntegerMultBounds.Machine.TranslationPreparedFamily

open CountedCopyReuse (empty binary)
open TranslationStream (blocks fibers)

def outputPrefix (offset : ℕ → ℕ) (Q n : ℕ) (payload : ℕ → ℕ → List (Fin 4)) : List (Fin 4) :=
  ((List.range n).map (fun i => (BlockRotationData.rotate (offset i) (blocks Q (payload i))).flatten)).flatten

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

theorem prefix_length (offset : ℕ → ℕ) (Q B n : ℕ) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) :
    (outputPrefix offset Q n payload).length = n*(Q*B) := by
  unfold outputPrefix
  rw [BlockRotationData.uniform_volume (Q*B)]
  · simp
  · intro word hw
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
    rw [BlockRotationData.payload_length]
    exact fiber_length Q B i payload hwidth

theorem prefix_succ (offset : ℕ → ℕ) (Q n : ℕ) (payload : ℕ → ℕ → List (Fin 4)) :
    outputPrefix offset Q (n+1) payload = outputPrefix offset Q n payload ++
      (BlockRotationData.rotate (offset n) (blocks Q (payload n))).flatten := by
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

/-- Physical boundary bank. Offset words and spectator banks are specifications
of actual intermediate machine states, not extra tape inputs or machine code. -/
def state {s : ℕ} (offset : ℕ → ℕ) (Q B n : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs : List Bool) (as : ℕ → List Bool) (frame : ℕ → Tapes s 0)
    (payload : ℕ → ℕ → List (Fin 4)) (i : ℕ) : Tapes (12+s) 0 :=
  (TranslationExecutionReuse.bank (putWord source p (fibers Q n payload).flatten)
    (putWord dest q (outputPrefix offset Q i payload))
    (p+((i*(Q*B) : ℕ) : ℤ)) (q+((i*(Q*B) : ℕ) : ℤ)) bs qs (as i)).append (frame i)

/-- Preparation writes the next offset and updates its own complete workspace,
while preserving Q/B, clean derived metadata, and the physical payload banks. -/
def prepared {s : ℕ} (offset : ℕ → ℕ) (Q B n : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs : List Bool) (as : ℕ → List Bool) (frame : ℕ → Tapes s 0)
    (payload : ℕ → ℕ → List (Fin 4)) (i : ℕ) : Tapes (12+s) 0 :=
  (TranslationExecutionReuse.bank (putWord source p (fibers Q n payload).flatten)
    (putWord dest q (outputPrefix offset Q i payload))
    (p+((i*(Q*B) : ℕ) : ℤ)) (q+((i*(Q*B) : ℕ) : ℤ)) bs qs (as (i+1))).append (frame (i+1))

/-- Translation preserves every cell and head of the arbitrary prep workspace. -/
theorem translate_hoare {s Q B n i : ℕ} (offset : ℕ → ℕ) (ha : offset i ≤ Q)
    (hB : 0 < B) (hi : i < n) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs : List Bool) (as : ℕ → List Bool) (frame : ℕ → Tapes s 0)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q)
    (ha' : Counter.value (as (i+1)) = offset i)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (ca : GrowingCounterData.Canonical (as (i+1)))
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B) :
    HoareTime (extend TranslationExecutionReuse.program s)
      (fun v => v = prepared offset Q B n source dest p q bs qs as frame payload i)
      (fun v => v = state offset Q B n source dest p q bs qs as frame payload (i+1))
      (207*(Q*B)+241) := by
  have hh := TranslationExecutionReuse.translate_hoare Q (offset i) B ha hB
    (putWord source p (fibers Q n payload).flatten) (putWord dest q (outputPrefix offset Q i payload))
    (p+((i*(Q*B) : ℕ) : ℤ)) (q+((i*(Q*B) : ℕ) : ℤ))
    (blocks Q (payload i)) (by simp [blocks]) (blocks_uniform Q B i payload hwidth)
    bs qs (as (i+1)) hb hq ha' cb cq ca
  unfold TranslationExecutionReuse.input TranslationExecutionReuse.output at hh
  rw [source_fiber Q B n i source p payload hwidth hi] at hh
  have hout : putWord (putWord dest q (outputPrefix offset Q i payload)) (q+((i*(Q*B) : ℕ) : ℤ))
      (BlockRotationData.rotate (offset i) (blocks Q (payload i))).flatten =
      putWord dest q (outputPrefix offset Q (i+1) payload) := by
    rw [← prefix_length offset Q B i payload hwidth,putWord_append_forward,prefix_succ]
  rw [hout] at hh
  have hpos (r : ℤ) : r+(i : ℤ)*((Q : ℤ)*B)+(Q : ℤ)*B =
      r+((i+1 : ℕ) : ℤ)*((Q : ℤ)*B) := by push_cast; ring
  simp only [Nat.cast_mul,hpos] at hh
  have he := hh.extend (frame (i+1))
  apply he.consequence _ _ le_rfl
  · intro v hv; exact ⟨_,rfl,hv⟩
  · rintro v ⟨w,rfl,hv⟩; exact hv

/-- One fixed body: run the provided finite-state preparation, then translation. -/
def bodyProgram {s m : ℕ} (prep : Program (12+s) m 0) : Program (12+s) (m+217) 0 :=
  seq prep (extend TranslationExecutionReuse.program s)

/-- Fixed program, independent of the number of fibers or their offset values. -/
def program {s m : ℕ} (prep : Program (12+s) m 0) : Program (12+s+2) (7+(m+217+5)+4) 0 :=
  CountedLoopReuse.program (bodyProgram prep)

/-- Conditional only on an actual preparation machine's proved runtime contract.
The offset for fiber i is physically present as as(i+1) after preparation. -/
theorem family_hoare {s m Q B n : ℕ} (prep : Program (12+s) m 0)
    (offset : ℕ → ℕ) (ha : ∀ i < n, offset i ≤ Q) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool)
    (as : ℕ → List Bool) (frame : ℕ → Tapes s 0)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (hn : Counter.value ns = n)
    (ha' : ∀ i < n, Counter.value (as (i+1)) = offset i)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (ca : ∀ i < n, GrowingCounterData.Canonical (as (i+1)))
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B)
    (prepCost : ℕ → ℕ)
    (hprep : ∀ i < n, HoareTime prep
      (fun v => v = state offset Q B n source dest p q bs qs as frame payload i)
      (fun v => v = prepared offset Q B n source dest p q bs qs as frame payload i)
      (prepCost i)) :
    HoareTime (program prep)
      (fun v => v = CountedLoopReuse.bank
        (state offset Q B n source dest p q bs qs as frame payload 0) empty (binary ns) 1 1)
      (fun v => v = CountedLoopReuse.bank
        (state offset Q B n source dest p q bs qs as frame payload n) empty (binary ns) 1 1)
      ((∑ i ∈ Finset.range n, prepCost i)+n*(207*(Q*B)+248)+7*ns.length+16) := by
  have hbody (i : ℕ) (hi : i < n) : HoareTime (bodyProgram prep)
      (fun v => v = state offset Q B n source dest p q bs qs as frame payload i)
      (fun v => v = state offset Q B n source dest p q bs qs as frame payload (i+1))
      (prepCost i+1+(207*(Q*B)+241)) := by
    exact (hprep i hi).seq (translate_hoare offset (ha i hi) hB hi source dest p q bs qs as frame hb hq (ha' i hi)
      cb cq (ca i hi) payload hwidth)
  have hh := CountedLoopReuse.loop_hoare (bodyProgram prep) ns n
    (state offset Q B n source dest p q bs qs as frame payload)
    (fun i => prepCost i+1+(207*(Q*B)+241)) hn hbody
  have hcost : (∑ i ∈ Finset.range n, (prepCost i+1+(207*(Q*B)+241)))+6*n+7*ns.length+16 =
      (∑ i ∈ Finset.range n, prepCost i)+n*(207*(Q*B)+248)+7*ns.length+16 := by
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul]
    ring
  simpa only [program,hcost] using hh

/-- Separate the actual offset-preparation cost from linear data movement. -/
theorem linear_bound (Q B n : ℕ) (ns : List Bool) (hQ : 0 < Q) (hB : 0 < B)
    (hw : ns.length ≤ n+1) :
    n*(207*(Q*B)+248)+7*ns.length+16 ≤ 462*(n*(Q*B))+23 := by
  have hvol : 1 ≤ Q*B := by nlinarith
  have hnvol : n ≤ n*(Q*B) := by nlinarith
  nlinarith

/-- Full finite-state family execution, retaining the charged preparation sum.
Only the initial boundary's descriptor and spectator bank occur in the input. -/
theorem family_hoare_linear {s m Q B n : ℕ} (prep : Program (12+s) m 0)
    (offset : ℕ → ℕ) (hQ : 0 < Q) (ha : ∀ i < n, offset i ≤ Q) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool)
    (as : ℕ → List Bool) (frame : ℕ → Tapes s 0)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (hn : Counter.value ns = n)
    (ha' : ∀ i < n, Counter.value (as (i+1)) = offset i)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) (ca : ∀ i < n, GrowingCounterData.Canonical (as (i+1)))
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B)
    (prepCost : ℕ → ℕ)
    (hprep : ∀ i < n, HoareTime prep
      (fun v => v = state offset Q B n source dest p q bs qs as frame payload i)
      (fun v => v = prepared offset Q B n source dest p q bs qs as frame payload i)
      (prepCost i)) :
    HoareTime (program prep)
      (fun v => v = CountedLoopReuse.bank
        (state offset Q B n source dest p q bs qs as frame payload 0) empty (binary ns) 1 1)
      (fun v => v = CountedLoopReuse.bank
        (state offset Q B n source dest p q bs qs as frame payload n) empty (binary ns) 1 1)
      ((∑ i ∈ Finset.range n, prepCost i)+462*(fibers Q n payload).flatten.length+23) := by
  have hw := GrowingCounterData.canonical_width ns cn
  have hl := Nat.log2_le_self (Counter.value ns)
  have hbound := linear_bound Q B n ns hQ hB (by omega)
  rw [← TranslationStream.source_length Q B n payload hwidth] at hbound
  exact (family_hoare prep offset ha hB source dest p q bs qs ns as frame hb hq hn ha'
    cb cq ca payload hwidth prepCost hprep).consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- A uniform bound on the actual preparation subroutine gives its full charge. -/
theorem preparation_sum_bound (n P : ℕ) (prepCost : ℕ → ℕ)
    (hcost : ∀ i < n, prepCost i ≤ P) :
    (∑ i ∈ Finset.range n, prepCost i) ≤ n*P := by
  calc
    (∑ i ∈ Finset.range n, prepCost i) ≤ ∑ _i ∈ Finset.range n, P :=
      Finset.sum_le_sum (fun i hi => hcost i (Finset.mem_range.mp hi))
    _ = n*P := by simp

/-- Finite control depends on the chosen preparation machine, not the inputs. -/
theorem stateCount_eq (m : ℕ) : 7+(m+217+5)+4 = m+233 := by omega

end IntegerMultBounds.Machine.TranslationPreparedFamily
