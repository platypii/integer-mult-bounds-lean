import IntegerMultBounds.Machine.RadixToBinary
import IntegerMultBounds.Machine.PrefixCounter
import IntegerMultBounds.Machine.CountedLoopReuse

/-! Physical construction of a zero radix field from a supplied binary width.
A counted binary loop writes one placeholder per digit; a backward finite
transducer recodes those placeholders and restores the field head. -/
namespace IntegerMultBounds.Machine.RadixZeroFill

open CountedCopyReuse (empty binary)
variable {q : ℕ} (hq : 2 ≤ q)

private def one {a : ℕ} (f : ℤ → Fin (a+4)) (r : ℤ) : Tapes 1 a := ⟨fun _ => r,fun _ => f⟩

private def writeProgram : Program 1 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun st _ => if st = 0 then some (1,fun _ => (bitSymbol false,.right)) else none

private def filled (n : ℕ) : Tapes 1 0 :=
  one (putWord empty 1 (List.replicate n (bitSymbol false))) (1+n)

private theorem write_hoare (n : ℕ) :
    HoareTime writeProgram (fun v => v = filled n) (fun v => v = filled (n+1)) 1 := by
  have he : Function.update (putWord empty 1 (List.replicate n (bitSymbol false))) (1+n) (bitSymbol false) =
      putWord empty 1 (List.replicate (n+1) (bitSymbol false)) := by
    rw [List.replicate_add]
    simpa only [List.replicate_one,List.length_replicate,putWord] using
      putWord_append_forward empty 1 (List.replicate n (bitSymbol false)) [bitSymbol false]
  rintro v rfl
  refine ⟨1,⟨1,(filled (n+1)).head,(filled (n+1)).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,writeProgram,Tapes.start,ite_true,filled,one,Move.offset]
    congr 1
    congr 1
    funext i z
    simpa [Function.update_apply] using congrFun he z
  · simp [step,writeProgram]

private def binaryFill : Program 3 18 0 := CountedLoopReuse.program writeProgram

private def binaryBank (bs : List Bool) (n : ℕ) : Tapes 3 0 :=
  CountedLoopReuse.bank (filled n) empty (binary bs) 1 1

private theorem binaryFill_hoare (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n) :
    HoareTime binaryFill (fun v => v = binaryBank bs 0) (fun v => v = binaryBank bs n)
      (7*n+7*bs.length+16) := by
  have h := CountedLoopReuse.loop_hoare writeProgram bs n filled (fun _ => 1) hn (fun i _ => write_hoare i)
  apply h.consequence (fun _ h => h) (fun _ h => h) _
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
  omega

def radixEmpty : ℤ → Fin (q+4) := fun z => if z = 0 then separator else blank

def radixZeros (n : ℕ) : ℤ → Fin (q+4) :=
  putWord radixEmpty 1 (List.replicate n (RadixDigits.digitSymbol (RadixCounterData.zeroDigit hq)))

private def placeholders (n : ℕ) : ℤ → Fin (q+4) :=
  putWord radixEmpty 1 (List.replicate n (bitSymbol false))

def encodedBinary (bs : List Bool) : ℤ → Fin (q+4) :=
  fun z => (RadixToBinary.binaryEncoding (q := q)).encode (binary bs z)

private def triple (out clock descriptor : ℤ → Fin (q+4)) (p r s : ℤ) : Tapes 3 q :=
  ⟨![p,r,s],![out,clock,descriptor]⟩

/-- No marker or placeholder is supplied on either writable tape. -/
def input (bs : List Bool) : Tapes 3 q :=
  triple (fun _ => blank) (fun _ => blank) (encodedBinary bs) 0 0 1

def output (bs : List Bool) (n : ℕ) : Tapes 3 q :=
  triple (radixZeros hq n) radixEmpty (encodedBinary bs) 1 1 1

private def afterFill (bs : List Bool) (n : ℕ) : Tapes 3 q :=
  triple (placeholders n) radixEmpty (encodedBinary bs) (1+n) 1 1

private theorem encode_word (f : ℤ → Fin 4) (p : ℤ) (xs : List (Fin 4)) :
    (fun z => (RadixToBinary.binaryEncoding (q := q)).encode (putWord f p xs z)) =
      putWord (fun z => (RadixToBinary.binaryEncoding (q := q)).encode (f z)) p
        (xs.map (RadixToBinary.binaryEncoding (q := q)).encode) := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    funext z
    by_cases hz : z = p <;> simp [putWord,hz,← ih]

private theorem encode_empty :
    (fun z => (RadixToBinary.binaryEncoding (q := q)).encode (empty z)) = radixEmpty := by
  funext z
  by_cases hz : z = 0 <;> simp [hz,empty,radixEmpty,RadixToBinary.binaryEncoding,separator,blank]

private theorem map_bank (bs : List Bool) (n : ℕ) :
    Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := q)) (binaryBank bs n) = afterFill bs n := by
  have hf : (fun z => (RadixToBinary.binaryEncoding (q := q)).encode
      (putWord empty 1 (List.replicate n (bitSymbol false)) z)) = placeholders n := by
    rw [encode_word,encode_empty,List.map_replicate]
    rfl
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i
    · exact hf
    · exact encode_empty
    · rfl

private def initializeProgram : Program 3 2 q where
  tapes_pos := by decide
  start := 0
  transition := fun st symbols => if st = 0 then
    some (1,fun i => if i = 2 then (symbols i,.stay) else (separator,.right)) else none

private theorem initialize_hoare (bs : List Bool) :
    HoareTime (initializeProgram (q := q)) (fun v => v = input bs) (fun v => v = afterFill bs 0) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(afterFill (q := q) bs 0).head,(afterFill bs 0).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,initializeProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z
      fin_cases i
      · simp [input,afterFill,triple,placeholders,putWord,radixEmpty]
      · simp [input,afterFill,triple,radixEmpty]
      · by_cases hz : z = 1 <;> simp [input,afterFill,triple,hz]
  · simp [step,initializeProgram]

private def fillProgram : Program 3 18 q :=
  Alphabet.program (RadixToBinary.binaryEncoding (q := q)) binaryFill

private theorem fill_hoare (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n) :
    HoareTime (fillProgram (q := q)) (fun v => v = afterFill bs 0) (fun v => v = afterFill bs n)
      (7*n+7*bs.length+16) := by
  apply (Alphabet.map_hoare (RadixToBinary.binaryEncoding (q := q)) (binaryFill_hoare bs n hn)).consequence
    _ _ le_rfl
  · intro v hv
    exact ⟨_,rfl,hv.trans (map_bank bs 0).symm⟩
  · rintro v ⟨w,rfl,hv⟩
    exact hv.trans (map_bank bs n)

/-- Move left from the output endpoint, recode each placeholder, and restore
the least-significant head. Every converted digit takes one actual transition. -/
private def recodeProgram : Program 1 3 q where
  tapes_pos := by decide
  start := 0
  transition := fun st symbols =>
    if st = 0 then some (1,fun i => (symbols i,.left))
    else if st = 1 then
      if symbols 0 = separator then some (2,fun _ => (separator,.right))
      else some (1,fun _ => (RadixDigits.digitSymbol (RadixCounterData.zeroDigit hq),.left))
    else none

private def recodeCfg (f : ℤ → Fin (q+4)) (p : ℤ) (st : Fin 3) : Config 1 3 q :=
  ⟨st,fun _ => p,fun _ => f⟩

private theorem recode_step (f : ℤ → Fin (q+4)) (p : ℤ) (h : f p ≠ separator) :
    step (recodeProgram hq) (recodeCfg f p 1) =
      some (recodeCfg (Function.update f p (RadixDigits.digitSymbol (RadixCounterData.zeroDigit hq))) (p-1) 1) := by
  simp only [step,recodeProgram,recodeCfg,show (1 : Fin 3) ≠ 0 by decide,ite_false,ite_true,h]
  congr 1
  congr 1
  funext i z
  simp [Function.update_apply,eq_comm]

private theorem recode_scan (n : ℕ) (f : ℤ → Fin (q+4)) (p : ℤ)
    (h : ∀ j : ℕ, j < n → f (p-j) ≠ separator) :
    run (recodeProgram hq) n (recodeCfg f p 1) =
      some (recodeCfg (putWord f (p-n+1) (List.replicate n
        (RadixDigits.digitSymbol (RadixCounterData.zeroDigit hq)))) (p-n) 1) := by
  induction n with
  | zero => simp [run,putWord]
  | succ n ih =>
    rw [run_add,ih (fun j hj => h j (by omega))]
    simp only [Option.bind_some,run_one]
    have he : putWord f (p-n+1) (List.replicate n
        (RadixDigits.digitSymbol (RadixCounterData.zeroDigit hq))) (p-n) = f (p-n) :=
      putWord_outside _ _ _ _ (Or.inl (by omega))
    rw [recode_step hq _ _ (by rw [he]; exact h n (by omega))]
    have hp : p-((n+1 : ℕ) : ℤ)+1 = p-n := by omega
    rw [List.replicate_succ,putWord,hp]
    congr 1
    congr 1
    omega

private theorem overwrite_word (f : ℤ → Fin (q+4)) (p : ℤ) (xs ys : List (Fin (q+4)))
    (hl : xs.length = ys.length) : putWord (putWord f p xs) p ys = putWord f p ys := by
  induction xs generalizing f p ys with
  | nil => have hy : ys = [] := List.length_eq_zero_iff.mp hl.symm; subst ys; rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have ht : xs.length = ys.length := by simpa using hl
      rw [putWord_cons f p x xs]
      rw [putWord_cons _ p y ys]
      rw [← putWord_update_before _ (p+1) p y xs (by omega)]
      simp only [Function.update_idem]
      rw [ih (Function.update f p y) (p+1) ys ht,← putWord_cons]

private theorem recode_hoare (n : ℕ) :
    HoareTime (recodeProgram hq) (fun v => v = one (placeholders n) (1+n))
      (fun v => v = one (radixZeros hq n) 1) (n+2) := by
  have hs : step (recodeProgram hq) (recodeCfg (placeholders n) (1+n) 0) =
      some (recodeCfg (placeholders n) n 1) := by
    simp only [step,recodeProgram,recodeCfg,ite_true]
    congr 1
    congr 1
    · funext i; simp [Move.offset]
    · funext i z
      by_cases hz : z = 1+n <;> simp [hz]
  have hr := recode_scan hq n (placeholders n) n (by
    intro j hj
    have hi : n-j-1 < (List.replicate n (bitSymbol false : Fin (q+4))).length := by simp; omega
    have hz : (n:ℤ)-j = 1+((n-j-1 : ℕ) : ℤ) := by omega
    rw [placeholders,hz,WordSegments.get _ _ _ _ hi]
    simp [bitSymbol,separator])
  simp only [sub_self,zero_add] at hr
  have he : putWord (placeholders n) 1
      (List.replicate n (RadixDigits.digitSymbol (RadixCounterData.zeroDigit hq))) = radixZeros hq n :=
    overwrite_word radixEmpty 1 _ _ (by simp)
  rw [he] at hr
  have hm : radixZeros hq n 0 = separator := by
    rw [radixZeros,putWord_outside _ _ _ _ (Or.inl (by omega))]
    rfl
  rintro v rfl
  refine ⟨n+2,recodeCfg (radixZeros hq n) 1 2,le_rfl,?_,?_,rfl⟩
  · rw [show n+2 = 1+n+1 by omega,run_add,run_add]
    change ((run (recodeProgram hq) 1 (recodeCfg (placeholders n) (1+n) 0)).bind _).bind _ = _
    rw [run_one,hs]
    simp only [Option.bind_some]
    rw [hr]
    simp only [Option.bind_some,run_one,step,recodeProgram,recodeCfg,
      show (1 : Fin 3) ≠ 0 by decide,ite_false,ite_true,hm]
    congr 1
    congr 1
    funext i z
    by_cases hz : z = 0 <;> simp [hz,hm]
  · simp [step,recodeProgram,recodeCfg]

/-- One fixed per-field initializer, including every marker and physical return. -/
def program : Program 3 23 q :=
  seq (seq initializeProgram fillProgram) (extend (recodeProgram hq) 2)

theorem fill_zeros (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n) :
    HoareTime (program hq) (fun v => v = input bs) (fun v => v = output hq bs n)
      (8*n+7*bs.length+21) := by
  let hframe := Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := q))
    (CountedLoopReuse.controls empty (binary bs) 1 1)
  have hh := (recode_hoare hq n).extend hframe
  have hh' : HoareTime (extend (recodeProgram hq) 2) (fun v => v = afterFill bs n)
      (fun v => v = output hq bs n) (n+2) := by
    apply hh.consequence _ _ le_rfl
    · intro v hv
      refine ⟨_,rfl,?_⟩
      rw [hv]
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> try rfl
      exact encode_empty.symm
    · rintro v ⟨w,rfl,rfl⟩
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> try rfl
      exact encode_empty
  apply (((initialize_hoare bs).seq (fill_hoare bs n hn)).seq hh').consequence (fun _ h => h) (fun _ h => h) _
  omega

theorem fill_zeros_linear (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n)
    (hc : GrowingCounterData.Canonical bs) :
    HoareTime (program hq) (fun v => v = input bs) (fun v => v = output hq bs n) (15*n+28) := by
  have hw := GrowingCounterData.canonical_width bs hc
  have hl := Nat.log2_le_self n
  rw [hn] at hw
  exact (fill_zeros hq bs n hn).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.RadixZeroFill
