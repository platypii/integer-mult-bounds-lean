import IntegerMultBounds.Machine.RadixPowerDescriptor
import IntegerMultBounds.Machine.TranslationProduct

/-! Canonical product synthesis from two real binary inputs and blank work.
This adapter charges marker setup and restores all three scratch tapes. -/
namespace IntegerMultBounds.Machine.DimensionProductDescriptor

variable {q : ℕ}

def bits (N W : ℕ) : List Bool := GrowingCounterData.advance (N*W) []

theorem bits_value (N W : ℕ) : Counter.value (bits N W) = N*W :=
  TranslationProduct.product_value N W

theorem bits_canonical (N W : ℕ) : GrowingCounterData.Canonical (bits N W) :=
  TranslationProduct.product_canonical N W

/-- Slots: spare, product output, inner clock, W input, outer clock, N input. -/
def input (ws ns : List Bool) : Tapes 6 q :=
  ⟨![0,0,0,1,0,1],![fun _ => blank,fun _ => blank,fun _ => blank,
    RadixZeroFill.encodedBinary ws,fun _ => blank,RadixZeroFill.encodedBinary ns]⟩

private def prepared (ds ws ns : List Bool) : Tapes 6 q :=
  ⟨fun _ => 1,![fun _ => blank,RadixZeroFill.encodedBinary ds,MarkedWordCleanup.empty,
    RadixZeroFill.encodedBinary ws,MarkedWordCleanup.empty,RadixZeroFill.encodedBinary ns]⟩

def output (ws ns : List Bool) (N W : ℕ) : Tapes 6 q :=
  ⟨![0,1,0,1,0,1],![fun _ => blank,RadixZeroFill.encodedBinary (bits N W),fun _ => blank,
    RadixZeroFill.encodedBinary ws,fun _ => blank,RadixZeroFill.encodedBinary ns]⟩

private def initProgram : Program 6 2 q where
  tapes_pos := by decide
  start := 0
  transition := fun s sy => if s = 0 then
    some (1,fun i => if i = 3 ∨ i = 5 then (sy i,.stay)
      else (if i = 0 then blank else separator,.right)) else none

private theorem init_hoare (ws ns : List Bool) :
    HoareTime (initProgram (q := q)) (fun v => v = input ws ns)
      (fun v => v = prepared [] ws ns) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(prepared (q := q) [] ws ns).head,(prepared [] ws ns).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,initProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z
      fin_cases i <;> by_cases hz : z = 0 <;> by_cases hz1 : z = 1 <;>
        simp [input,prepared,hz,hz1,RadixZeroFill.encodedBinary,
          RadixToBinary.binaryEncoding,CountedCopyReuse.binary,putBits,
          CountedCopyReuse.empty,MarkedWordCleanup.empty,blank,separator]
  · simp [step,initProgram]

private theorem mapped_bank (ds ws ns : List Bool) :
    Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := q))
      (TranslationProduct.bank (fun _ : Fin 1 => ds) ws ns) = prepared ds ws ns := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i z
    fin_cases i <;> try rfl
    all_goals
      change (RadixToBinary.binaryEncoding (q := q)).encode (CountedCopyReuse.empty z) = MarkedWordCleanup.empty z
      by_cases hz : z = 0 <;>
        simp [hz,RadixToBinary.binaryEncoding,CountedCopyReuse.empty,MarkedWordCleanup.empty,blank,separator]

private def coreProgram : Program 6 35 q :=
  Alphabet.program RadixToBinary.binaryEncoding (TranslationProduct.program (0 : Fin 1))

private theorem core_hoare (ws ns : List Bool) (N W : ℕ) (hW : 0 < W)
    (hw : Counter.value ws = W) (hn : Counter.value ns = N)
    (cw : GrowingCounterData.Canonical ws) (cn : GrowingCounterData.Canonical ns) :
    HoareTime (coreProgram (q := q)) (fun v => v = prepared [] ws ns)
      (fun v => v = prepared (bits N W) ws ns) (53*(N*W)+23) := by
  have hu : Function.update (fun _ : Fin 1 => ([] : List Bool)) 0 (bits N W) = fun _ => bits N W := by
    funext i; fin_cases i; simp
  have hh := TranslationProduct.product_empty_hoare_linear (fun _ : Fin 1 => []) 0 rfl
    ws ns W N hW hw hn cw cn
  change HoareTime _ _ (fun v => v = TranslationProduct.bank
    (Function.update (fun _ : Fin 1 => []) 0 (bits N W)) ws ns) _ at hh
  rw [hu] at hh
  apply (Alphabet.map_hoare (RadixToBinary.binaryEncoding (q := q)) hh).consequence _ _ le_rfl
  · intro v hv; exact ⟨_,rfl,hv.trans (mapped_bank [] ws ns).symm⟩
  · rintro v ⟨w,rfl,hv⟩
    exact hv.trans (mapped_bank (bits N W) ws ns)

private def cleanProgram : Program 6 3 q where
  tapes_pos := by decide
  start := 0
  transition := fun s sy =>
    if s = 0 then some (1,fun i => (sy i,if i = 0 ∨ i = 2 ∨ i = 4 then .left else .stay))
    else if s = 1 then some (2,fun i => (if i = 2 ∨ i = 4 then blank else sy i,.stay))
    else none

private theorem clean_hoare (ws ns : List Bool) (N W : ℕ) :
    HoareTime (cleanProgram (q := q)) (fun v => v = prepared (bits N W) ws ns)
      (fun v => v = output ws ns N W) 2 := by
  let middle : Tapes 6 q := ⟨(output (q := q) ws ns N W).head,(prepared (bits N W) ws ns).tape⟩
  have hs : step cleanProgram ((prepared (bits N W) ws ns).start cleanProgram) =
      some (⟨1,middle.head,middle.tape⟩ : Config 6 3 q) := by
    simp only [step,cleanProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z
      by_cases hz : z = 1 <;> simp [hz,middle,prepared]
  rintro v rfl
  refine ⟨2,⟨2,(output (q := q) ws ns N W).head,(output ws ns N W).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_add cleanProgram 1 1,run_one,hs]
    simp only [Option.bind_some,run_one,step,cleanProgram,
      show (1 : Fin 3) ≠ 0 by decide,ite_false,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z
      fin_cases i <;> by_cases hz : z = 0 <;> by_cases hz1 : z = 1 <;>
        simp [middle,output,prepared,MarkedWordCleanup.empty,hz,hz1]
  · simp [step,cleanProgram]

/-- A forty-state physical constructor, with no supplied workspace markers. -/
def program : Program 6 40 q := seq (seq initProgram coreProgram) cleanProgram

theorem construct_hoare (ws ns : List Bool) (N W : ℕ) (hW : 0 < W)
    (hw : Counter.value ws = W) (hn : Counter.value ns = N)
    (cw : GrowingCounterData.Canonical ws) (cn : GrowingCounterData.Canonical ns) :
    HoareTime (program (q := q)) (fun v => v = input ws ns) (fun v => v = output ws ns N W)
      (53*(N*W)+28) := by
  exact (((init_hoare ws ns).seq (core_hoare ws ns N W hW hw hn cw cn)).seq
    (clean_hoare ws ns N W)).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.DimensionProductDescriptor
