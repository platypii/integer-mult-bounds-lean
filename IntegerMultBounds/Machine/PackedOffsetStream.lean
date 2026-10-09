import IntegerMultBounds.Machine.PackedOffsetStreamBlock
import IntegerMultBounds.Machine.StreamedFiberTranslation
import IntegerMultBounds.Machine.CountedGatherClockPair

/-! Synthesize a literal stream of canonical offsets from fixed-width packed
binary blocks. Only the original width/count headers are initialized inputs.
All three private tapes start and finish blank, including both loop markers. -/
namespace IntegerMultBounds.Machine.PackedOffsetStream
open PackedOffsetStreamBlock (canonical)
open CountedCopyReuse (binary empty)
noncomputable section

def words (blocks : List (List Bool)) := blocks.map canonical
def output (blocks : List (List Bool)) := StreamedFiberTranslation.encoded (words blocks)

theorem words_canonical (blocks : List (List Bool)) :
    ∀ xs ∈ words blocks, GrowingCounterData.Canonical xs := by
  intro xs hx
  obtain ⟨ys,_,rfl⟩ := List.mem_map.mp hx
  exact (PackedOffsetStreamBlock.canonical_facts ys).1

theorem words_values (blocks : List (List Bool)) : (words blocks).map Counter.value = blocks.map Counter.value := by
  simp only [words,List.map_map]
  apply List.map_congr_left
  intro xs _
  exact (PackedOffsetStreamBlock.canonical_facts xs).2.1

theorem output_append (xs ys : List (List Bool)) : output (xs++ys) = output xs++output ys := by
  simp [output,words,StreamedFiberTranslation.encoded_append]

theorem output_succ (blocks : List (List Bool)) (i : ℕ) (hi : i < blocks.length) :
    output (blocks.take (i+1)) = output (blocks.take i) ++ PackedOffsetStreamEmit.encoded (canonical blocks[i]) := by
  rw [List.take_succ_eq_append_getElem hi,output_append]
  simp [output,words,StreamedFiberTranslation.encoded,PackedOffsetStreamEmit.encoded]

theorem output_length (blocks : List (List Bool)) (w : ℕ)
    (hw : BlockRotationData.Uniform w blocks) : (output blocks).length ≤ blocks.length*(w+1) := by
  induction blocks with
  | nil => simp [output,words,StreamedFiberTranslation.encoded]
  | cons xs blocks ih =>
    have htail : BlockRotationData.Uniform w blocks := fun ys hy => hw ys (by simp [hy])
    have hxs := hw xs (by simp)
    have hc := (PackedOffsetStreamBlock.canonical_facts xs).2.2
    have ht := ih htail
    change (PackedOffsetStreamEmit.encoded (canonical xs) ++ output blocks).length ≤ _
    simp only [PackedOffsetStreamEmit.encoded,List.length_append,List.length_map,List.length_cons,List.length_nil]
    nlinarith

def state (blocks : List (List Bool)) (w : ℕ) (f g : ℤ → Fin 4) (p q : ℤ) (bs : List Bool) (i : ℕ) :=
  PackedOffsetStreamBlock.bank (putWord f p (blocks.flatten.map bitSymbol))
    (putWord g q (output (blocks.take i))) (p+((i*w : ℕ) : ℤ)) (q+(output (blocks.take i)).length) bs

private theorem source_block (blocks : List (List Bool)) (w : ℕ) (hw : BlockRotationData.Uniform w blocks)
    (f : ℤ → Fin 4) (p : ℤ) (i : ℕ) (hi : i < blocks.length) :
    putWord (putWord f p (blocks.flatten.map bitSymbol)) (p+((i*w : ℕ) : ℤ)) (blocks[i].map bitSymbol) =
      putWord f p (blocks.flatten.map bitSymbol) := by
  have hu : BlockRotationData.Uniform w (blocks.map (List.map (bitSymbol (a := 0)))) := by
    intro xs hx
    obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx
    simpa using hw ys hy
  have hh := FiberShift.source_fiber f p (blocks.map (List.map bitSymbol)) w i hu (by simpa using hi)
  simpa only [List.getElem_map,List.map_flatten] using hh

theorem body_hoare (blocks : List (List Bool)) (w : ℕ) (hw : BlockRotationData.Uniform w blocks)
    (f g : ℤ → Fin 4) (p q : ℤ) (bs : List Bool) (hb : Counter.value bs = w) (i : ℕ) (hi : i < blocks.length) :
    HoareTime PackedOffsetStreamBlock.program (fun v => v = state blocks w f g p q bs i)
      (fun v => v = state blocks w f g p q bs (i+1)) (8*w+7*bs.length+31) := by
  have hl := hw blocks[i] (List.getElem_mem hi)
  have hh := PackedOffsetStreamBlock.runs blocks[i] bs
    (putWord f p (blocks.flatten.map bitSymbol)) (putWord g q (output (blocks.take i)))
    (p+((i*w : ℕ) : ℤ)) (q+(output (blocks.take i)).length) (by omega)
  rw [source_block blocks w hw f p i hi] at hh
  rw [putWord_append_forward,← output_succ blocks i hi,hl] at hh
  have hp : p+((i*w : ℕ) : ℤ)+w = p+(((i+1)*w : ℕ) : ℤ) := by push_cast; ring
  have hq : q+((output (blocks.take i)).length : ℤ)+(PackedOffsetStreamEmit.encoded (canonical blocks[i])).length =
      q+(output (blocks.take (i+1))).length := by
    rw [output_succ blocks i hi,List.length_append]
    push_cast; ring
  simpa only [state,hp,hq] using hh

def loopProgram : Program 7 46 0 := CountedLoopReuse.program PackedOffsetStreamBlock.program
def ready (f g : ℤ → Fin 4) (p q : ℤ) (bs ns : List Bool) :=
  CountedLoopReuse.bank (PackedOffsetStreamBlock.bank f g p q bs) empty (binary ns) 1 1

theorem loop_hoare (blocks : List (List Bool)) (w : ℕ) (hw : BlockRotationData.Uniform w blocks)
    (f g : ℤ → Fin 4) (p q : ℤ) (bs ns : List Bool)
    (hb : Counter.value bs = w) (hn : Counter.value ns = blocks.length) :
    HoareTime loopProgram (fun v => v = ready (putWord f p (blocks.flatten.map bitSymbol)) g p q bs ns)
      (fun v => v = ready (putWord f p (blocks.flatten.map bitSymbol)) (putWord g q (output blocks))
        (p+((blocks.length*w : ℕ) : ℤ)) (q+(output blocks).length) bs ns)
      (blocks.length*(8*w+7*bs.length+37)+7*ns.length+16) := by
  have hh := CountedLoopReuse.loop_hoare PackedOffsetStreamBlock.program ns blocks.length
    (state blocks w f g p q bs) (fun _ => 8*w+7*bs.length+31) hn
    (body_hoare blocks w hw f g p q bs hb)
  apply hh.consequence ?_ ?_ ?_
  · intro v hv
    simpa [state,ready,output,words,StreamedFiberTranslation.encoded,putWord] using hv
  · intro v hv
    simpa only [state,List.take_length,ready] using hv
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    nlinarith

/-- Original source/output and canonical width/count headers; three private
tapes are wholly blank at head zero. -/
def input (f g : ℤ → Fin 4) (p q : ℤ) (bs ns : List Bool) : Tapes 7 0 :=
  ⟨![p,0,0,1,q,0,1],![f,(fun _ => blank),(fun _ => blank),binary bs,g,(fun _ => blank),binary ns]⟩

def clocks : Fin (2+5) ≃ Fin 7 where
  toFun := ![2,5,0,1,3,4,6]
  invFun := ![2,3,0,4,5,1,6]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def initProgram := Placement.placed (CountedGatherClockPair.init 0) clocks
def clearProgram := Placement.placed (CountedGatherClockPair.clear 0) clocks
def program : Program 7 51 0 := seq (seq initProgram loopProgram) clearProgram

theorem initializes (f g : ℤ → Fin 4) (p q : ℤ) (bs ns : List Bool) :
    HoareTime initProgram (fun v => v = input f g p q bs ns) (fun v => v = ready f g p q bs ns) 1 := by
  have ha : Placement.active clocks (input f g p q bs ns) = CountedGatherClockPair.empty := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hh := Placement.hoare_at (CountedGatherClockPair.init_hoare (a := 0)) clocks _ ha
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem clears (f g : ℤ → Fin 4) (p q : ℤ) (bs ns : List Bool) :
    HoareTime clearProgram (fun v => v = ready f g p q bs ns) (fun v => v = input f g p q bs ns) 2 := by
  have ha : Placement.active clocks (ready f g p q bs ns) = CountedGatherClockPair.marked := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hh := Placement.hoare_at (CountedGatherClockPair.clear_hoare (a := 0)) clocks _ ha
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- All physical copying, trimming, stream delimiters, clocks and cleanup are
charged. Width zero emits one empty-word delimiter per block; count zero
still executes and erases clock initialization. -/
theorem runs (blocks : List (List Bool)) (w : ℕ) (hw : BlockRotationData.Uniform w blocks)
    (f g : ℤ → Fin 4) (p q : ℤ) (bs ns : List Bool)
    (hb : Counter.value bs = w) (hn : Counter.value ns = blocks.length)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical ns) :
    HoareTime program (fun v => v = input (putWord f p (blocks.flatten.map bitSymbol)) g p q bs ns)
      (fun v => v = input (putWord f p (blocks.flatten.map bitSymbol)) (putWord g q (output blocks))
        (p+((blocks.length*w : ℕ) : ℤ)) (q+(output blocks).length) bs ns)
      (66*(blocks.length*(w+1))+28) := by
  have h₀ := initializes (putWord f p (blocks.flatten.map bitSymbol)) g p q bs ns
  have h₁ := loop_hoare blocks w hw f g p q bs ns hb hn
  have h₂ := clears (putWord f p (blocks.flatten.map bitSymbol)) (putWord g q (output blocks))
    (p+((blocks.length*w : ℕ) : ℤ)) (q+(output blocks).length) bs ns
  have wb := GrowingCounterData.canonical_width bs cb
  have wn := GrowingCounterData.canonical_width ns cn
  have lb := Nat.log2_le_self (Counter.value bs)
  have ln := Nat.log2_le_self (Counter.value ns)
  have hbs : bs.length ≤ w+1 := by omega
  have hns : ns.length ≤ blocks.length+1 := by omega
  have hm := Nat.mul_le_mul_left blocks.length (show 8*w+7*bs.length+37 ≤ 15*w+44 by omega)
  apply ((h₀.seq h₁).seq h₂).consequence (fun _ h => h) (fun _ h => h)
  nlinarith

end
end IntegerMultBounds.Machine.PackedOffsetStream
