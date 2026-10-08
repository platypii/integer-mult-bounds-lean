import IntegerMultBounds.Machine.MultiControlPrefixTranslationStream
import IntegerMultBounds.Machine.RadixLinearCombinationBootstrap

/-! Blank-workspace bootstrap for the actual multi-control prefix stream.
The shared radix fields and canonical B/Q/n descriptors are the only numeric
inputs. One physical marker step and one actual expression evaluation construct
the recurring state; the first loop body recomputes it, with all work charged. -/
namespace IntegerMultBounds.Machine.MultiControlPrefixTranslationBootstrap

open RadixLinearCombinationRefresh (Expr leaves)
open MultiControlPrefixTranslationExecution (read)
open MultiControlTranslationExecution (ArithmeticTapes)
variable {c radix : ℕ}

def workspace (i : Fin 14) : Bool := decide (i ≠ 5 ∧ i ≠ 7 ∧ i ≠ 10 ∧ i ≠ 11 ∧ i ≠ 13)
private def marker (i : Fin 14) : Bool := decide (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 12)

def raw (v : Tapes 14 radix) : Tapes 14 radix :=
  ⟨fun i => if workspace i then 0 else v.head i,
    fun i => if workspace i then (fun _ => blank) else v.tape i⟩

private def marked (v : Tapes 14 radix) : Tapes 14 radix :=
  ⟨fun i => v.head i+if marker i || decide (i = 0) then 1 else 0,
    fun i => if marker i then Function.update (v.tape i) (v.head i) separator else v.tape i⟩

private def markerProgram : Program 14 2 radix where
  tapes_pos := by decide
  start := 0
  transition := fun st symbols => if st = 0 then some (1,fun i =>
    if marker i then (separator,.right) else if i = 0 then (symbols i,.right) else (symbols i,.stay)) else none

private theorem marker_hoare (v : Tapes 14 radix) :
    HoareTime markerProgram (fun x => x = v) (fun x => x = marked v) 1 := by
  intro x hx
  subst x
  refine ⟨1,⟨1,(marked v).head,(marked v).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,markerProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i
      cases hm : marker i <;> by_cases hi : i = 0 <;> simp [hm,hi,marked,Move.offset]
    · funext i z
      by_cases hi : i = 0
      · subst i; simp [marker,marked]; intro hz; rw [hz]
      · cases hm : marker i <;> by_cases hz : z = v.head i <;> simp [hm,hi,hz,marked]
  · simp [step,markerProgram]

/-- Translation workspace and two outer-loop controls. Only five tapes carry
supplied data: B/Q/n descriptors and payload source/destination. -/
def frame (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) : Tapes 14 radix :=
  ⟨![1,1,1,1,1,1,1,1,0,0,p,q,1,1],
    ![fun _ => blank,MarkedWordCleanup.empty,MarkedWordCleanup.empty,MarkedWordCleanup.empty,
      MarkedWordCleanup.empty,fun z => RadixToBinary.binaryEncoding.encode (CountedCopyReuse.binary bs z),
      MarkedWordCleanup.empty,fun z => RadixToBinary.binaryEncoding.encode (CountedCopyReuse.binary qs z),
      fun _ => blank,fun _ => blank,fun z => RadixToBinary.binaryEncoding.encode (source z),
      fun z => RadixToBinary.binaryEncoding.encode (dest z),CountedLoopReuseAlphabet.empty,
      CountedLoopReuseAlphabet.binary ns]⟩

private theorem frame_eq (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :
    frame (radix := radix) source dest p q bs qs ns =
      (MultiControlTranslationExecution.translationBank source dest p q bs qs).append
        (CountedLoopReuseAlphabet.controls CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1) := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i z
    fin_cases i <;> try rfl
    all_goals
      change MarkedWordCleanup.empty z = (RadixToBinary.binaryEncoding (q := radix)).encode (CountedCopyReuse.empty z)
      by_cases hz : z = 0 <;> simp [hz,CountedCopyReuse.empty,MarkedWordCleanup.empty,RadixToBinary.binaryEncoding,blank,separator]

private theorem frame_marked (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :
    marked (raw (frame (radix := radix) source dest p q bs qs ns)) = frame source dest p q bs qs ns := by
  unfold marked raw frame
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> simp [workspace,marker]
  · funext i z
    fin_cases i <;> simp [workspace,marker,Function.update_apply,MarkedWordCleanup.empty,CountedLoopReuseAlphabet.empty]

/-- All writable metadata starts blank at origin, without inherited sentinels. -/
theorem raw_workspace (v : Tapes 14 radix) (i : Fin 14) (hi : workspace i = true) :
    (raw v).head i = 0 ∧ (raw v).tape i = (fun _ => blank) := by simp [raw,hi]

/-- Supplied descriptor/payload tapes and their heads are retained literally. -/
theorem raw_retained (v : Tapes 14 radix) (i : Fin 14) (hi : workspace i = false) :
    (raw v).head i = v.head i ∧ (raw v).tape i = v.tape i := by simp [raw,hi]

private def assoc (a : ℕ) : Fin (a+14) ≃ Fin ((a+12)+2) := finCongr (by omega)

private theorem append_assoc {a : ℕ} (v : Tapes a radix) (w : Tapes 12 radix) (z : Tapes 2 radix) :
    (v.append (w.append z)).reindex (assoc a) = (v.append w).append z := by
  have hl (i : Fin a) : (assoc a).symm (Fin.castAdd 2 (Fin.castAdd 12 i)) = Fin.castAdd 14 i := Fin.ext rfl
  have hm (i : Fin 12) : (assoc a).symm (Fin.castAdd 2 (Fin.natAdd a i)) = Fin.natAdd a (Fin.castAdd 2 i) := Fin.ext rfl
  have hr (i : Fin 2) : (assoc a).symm (Fin.natAdd (a+12) i) = Fin.natAdd a (Fin.natAdd 12 i) := Fin.ext (by change (a+12)+i.val = a+(12+i.val); omega)
  unfold Tapes.reindex
  apply congrArg₂ Tapes.mk
  all_goals
    funext i
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i => rw [hl]; simp [Tapes.append]
      | right i => rw [hm]; simp [Tapes.append]
    | right i => rw [hr]; simp [Tapes.append]

private def setup (a : ℕ) : Program (a+14) 2 radix :=
  Placement.placed markerProgram (finAddFlip : Fin (14+a) ≃ Fin (a+14))

private theorem setup_hoare {a : ℕ} (arithmetic : Tapes a radix)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :
    HoareTime (setup a) (fun v => v = arithmetic.append (raw (frame source dest p q bs qs ns)))
      (fun v => v = arithmetic.append (frame source dest p q bs qs ns)) 1 := by
  let wire : Fin (14+a) ≃ Fin (a+14) := finAddFlip
  have ha (w : Tapes 14 radix) : Placement.active wire (arithmetic.append w) = w := by
    cases w; simp [Placement.active,wire,Tapes.append,finAddFlip_apply_castAdd]
  have he (w : Tapes 14 radix) : Placement.extra wire (arithmetic.append w) = arithmetic := by
    cases arithmetic; simp [Placement.extra,wire,Tapes.append,finAddFlip_apply_natAdd]
  have hh := Placement.hoare_at (marker_hoare (raw (frame source dest p q bs qs ns))) wire _ (ha _)
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨small,hsmall,rfl⟩
  rw [frame_marked] at hsmall
  subst small
  rw [Placement.replace,he]
  simpa only [ha,he] using Placement.view wire (arithmetic.append (frame source dest p q bs qs ns))

variable [Fact radix.Prime]

abbrev TapeCount (e : Expr c) := (MultiControlTranslationExecution.TapeCount e)+2

/-- All expression scratch and writable metadata are blank. Actual marked shared
radix fields remain supplied; their initialization is a separate obligation. -/
def input (e : Expr c) (seed : Fin c) (b n : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs ns : List Bool) (initial : Fin c → List (Fin radix)) (payload : ℕ → ℕ → List (Fin 4)) :
    Tapes (TapeCount e) radix :=
  ((RadixLinearCombinationBootstrap.input e (read seed initial)).append
    (raw (frame (putWord source p (TranslationStream.fibers (radix^b) n payload).flatten) dest p q bs qs ns))).reindex
    (assoc (ArithmeticTapes e))

private def prepareProgram (e : Expr c) : Program (TapeCount e) (2+RadixLinearCombinationBootstrap.States e) radix :=
  reindex (seq (setup (ArithmeticTapes e)) (extend (RadixLinearCombinationBootstrap.program e) 14)) (assoc (ArithmeticTapes e))

private theorem prepare_hoare (e : Expr c) (seed : Fin c) (order : List (Fin c)) (b B n : ℕ)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) (initial : Fin c → List (Fin radix))
    (hw : ∀ j, (initial j).length = b) (payload : ℕ → ℕ → List (Fin 4)) :
    HoareTime (prepareProgram e) (fun v => v = input e seed b n source dest p q bs qs ns initial payload)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (MultiControlPrefixTranslationStream.state e seed order b B n source dest p q bs qs initial initial payload 0)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      ((15*leaves e+RadixLinearCombination.linearConstant e.erase+40)*radix^b+2) := by
  let S := putWord source p (TranslationStream.fibers (radix^b) n payload).flatten
  have hh := (setup_hoare (RadixLinearCombinationBootstrap.input e (read seed initial)) S dest p q bs qs ns).seq
    (FamilyPlacementAlphabet.extend_hoare
      (RadixLinearCombinationBootstrap.compute_finite_hoare e seed initial b hw) (frame S dest p q bs qs ns))
  have hr := hh.reindex (assoc (ArithmeticTapes e))
  apply hr.consequence _ _ (by omega)
  · rintro v rfl; exact ⟨_,rfl,rfl⟩
  · rintro v ⟨w,rfl,rfl⟩
    rw [frame_eq,append_assoc]
    simp only [CountedLoopReuseAlphabet.bank,MultiControlPrefixTranslationStream.state,
      MultiControlPrefixTranslationStream.fields,PrefixCounterData.iterateFields,
      MultiControlPrefixTranslationStream.stale,MultiControlPrefixTranslationStream.outputPrefix,
      TranslationPreparedFamily.outputPrefix,List.range_zero,List.map_nil,List.flatten_nil,putWord,
      Nat.zero_mul,Nat.cast_zero,add_zero]
    rfl

def program (e : Expr c) (order : List (Fin c)) (hne : order ≠ []) :=
  seq (prepareProgram (radix := radix) e) (MultiControlPrefixTranslationStream.program e order hne)

private theorem lex_nonempty (seed : Fin c) : List.finRange c ≠ [] := by
  intro h
  have hh := congrArg List.length h
  simp at hh
  have := seed.isLt
  omega

def lexProgram (e : Expr c) (seed : Fin c) := program (radix := radix) e (List.finRange c) (lex_nonempty seed)

/-- A complete control cycle from genuinely blank writable workspaces. The
redundant initial evaluation is actual machine work and included in this bound. -/
theorem full_cycle_hoare (e : Expr c) (seed : Fin c) {b B n : ℕ} (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) (initial : Fin c → List (Fin radix))
    (hw : ∀ j, (initial j).length = b) (hperiod : n = radix^(c*b))
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^b) (hn : Counter.value ns = n)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) (cn : GrowingCounterData.Canonical ns)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ j y, (payload j y).length = B) :
    HoareTime (lexProgram e seed)
      (fun v => v = input e seed b n source dest p q bs qs ns initial payload)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (MultiControlPrefixTranslationStream.state e seed (List.finRange c) b B n source dest p q bs qs initial initial payload n)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      ((28*leaves e+2*RadixLinearCombination.linearConstant e.erase+552+4*c)*
        (TranslationStream.fibers (radix^b) n payload).flatten.length+26) := by
  have hp := prepare_hoare e seed (List.finRange c) b B n source dest p q bs qs ns initial hw payload
  have ht := MultiControlPrefixTranslationStream.full_cycle_hoare e seed hB source dest p q bs qs ns initial initial
    hw hw hperiod hb hq hn cb cq cn payload hwidth
  apply (hp.seq ht).consequence (fun _ h => h) (fun _ h => h)
  rw [TranslationStream.source_length (radix^b) B n payload hwidth]
  have hnpos : 1 ≤ n := by rw [hperiod]; exact Nat.one_le_pow _ _ (by have := (Fact.out : radix.Prime).two_le; omega)
  have hBpos : 1 ≤ B := hB
  have hvol : radix^b ≤ n*(radix^b*B) :=
    (Nat.le_mul_of_pos_right _ hB).trans (Nat.le_mul_of_pos_left _ (by omega))
  have hm := Nat.mul_le_mul_left (15*leaves e+RadixLinearCombination.linearConstant e.erase+40) hvol
  nlinarith

end IntegerMultBounds.Machine.MultiControlPrefixTranslationBootstrap
