import IntegerMultBounds.Machine.RationalPrefixTranslationInit

/-! A physical one-step bootstrap for every writable translation metadata tape.
Only the canonical dimension descriptors and payload tapes are supplied. Prefix
fields/clocks remain blank until the existing counted initializer constructs them. -/
namespace IntegerMultBounds.Machine.RationalPrefixTranslationBootstrap
open PrefixCounterInitPlacement
variable {radix c B : ℕ}

/-- Input descriptors B/Q/n and payload source/destination are the only retained tapes. -/
def workspace (i : Fin 17) : Bool := decide (i ≠ 5 ∧ i ≠ 7 ∧ i ≠ 10 ∧ i ≠ 11 ∧ i ≠ 16)

def marker (i : Fin 17) : Bool := decide (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 8 ∨ i = 12 ∨ i = 15)

def raw (v : Tapes 17 radix) : Tapes 17 radix :=
  ⟨fun i => if workspace i then 0 else v.head i,
    fun i => if workspace i then (fun _ => blank) else v.tape i⟩

private def marked (v : Tapes 17 radix) : Tapes 17 radix :=
  ⟨fun i => v.head i+if marker i || decide (i = 0) then 1 else 0,
    fun i => if marker i then Function.update (v.tape i) (v.head i) separator else v.tape i⟩

def markerProgram : Program 17 2 radix where
  tapes_pos := by decide
  start := 0
  transition := fun st symbols => if st = 0 then some (1,fun i =>
    if marker i then (separator,.right) else if i = 0 then (symbols i,.right) else (symbols i,.stay)) else none

private theorem marker_hoare (v : Tapes 17 radix) :
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

private theorem extra_left (i : Fin 15) :
    RationalPrefixTranslationInit.streamPlacement c (Fin.natAdd (c+1) (Fin.castAdd 2 i)) =
      Fin.castAdd 2 (Fin.castAdd c (Fin.castAdd 1 i)) := by
  change appendEquiv (RationalPrefixTranslationExecution.prefixPlacement c) 2 _ = _
  have he : (Fin.natAdd (c+1) (Fin.castAdd 2 i) : Fin (((c+1)+15)+2)) =
      Fin.castAdd 2 (Fin.natAdd (c+1) i) := Fin.ext rfl
  rw [he,appendEquiv_left]
  apply congrArg (Fin.castAdd 2)
  apply Fin.ext
  simp [RationalPrefixTranslationExecution.prefixPlacement,finAddFlip_apply_natAdd]

private theorem extra_right (i : Fin 2) :
    RationalPrefixTranslationInit.streamPlacement c (Fin.natAdd (c+1) (Fin.natAdd 15 i)) =
      Fin.natAdd (16+c) i := by
  change appendEquiv (RationalPrefixTranslationExecution.prefixPlacement c) 2 _ = _
  have he : (Fin.natAdd (c+1) (Fin.natAdd 15 i) : Fin (((c+1)+15)+2)) =
      Fin.natAdd ((c+1)+15) i := Fin.ext (by simp; omega)
  rw [he,appendEquiv_right]

private def frame (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) : Tapes 17 radix :=
  ⟨![1,1,1,1,1,1,1,1,1,0,p,q,1,0,0,1,1],
    ![fun _ => blank,RadixZeroFill.radixEmpty,RadixZeroFill.radixEmpty,RadixZeroFill.radixEmpty,
      RadixZeroFill.radixEmpty,RadixZeroFill.encodedBinary bs,RadixZeroFill.radixEmpty,
      RadixZeroFill.encodedBinary qs,RadixZeroFill.radixEmpty,fun _ => blank,
      fun z => RadixToBinary.binaryEncoding.encode (source z),
      fun z => RadixToBinary.binaryEncoding.encode (dest z),
      RadixZeroFill.radixEmpty,fun _ => blank,fun _ => blank,RadixZeroFill.radixEmpty,
      CountedLoopReuseAlphabet.binary ns]⟩

private theorem metadata_eq (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool)
    (ds : Fin (c+1) → List (Fin radix)) :
    Placement.extra (RationalPrefixTranslationInit.streamPlacement c)
      (CountedLoopReuseAlphabet.bank
        (RationalPrefixTranslationExecution.bank source dest p q bs qs [] [] ds)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1) =
      frame source dest p q bs qs ns := by
  apply congrArg₂ Tapes.mk
  · funext i
    change Fin (15+2) at i
    induction i using Fin.addCases with
    | left i =>
      rw [extra_left]
      simp only [CountedLoopReuseAlphabet.bank,RationalPrefixTranslationExecution.bank,Tapes.append,Fin.addCases_left]
      fin_cases i <;> rfl
    | right i =>
      rw [extra_right]
      simp only [CountedLoopReuseAlphabet.bank,Tapes.append,Fin.addCases_right]
      fin_cases i <;> rfl
  · funext i z
    change Fin (15+2) at i
    induction i using Fin.addCases with
    | left i =>
      rw [extra_left]
      simp only [CountedLoopReuseAlphabet.bank,RationalPrefixTranslationExecution.bank,Tapes.append,Fin.addCases_left]
      fin_cases i <;> try rfl
      all_goals
        change (RadixToBinary.binaryEncoding (q := radix)).encode (CountedCopyReuse.empty z) = RadixZeroFill.radixEmpty z
        by_cases hz : z = 0 <;> simp [hz,CountedCopyReuse.empty,RadixZeroFill.radixEmpty,RadixToBinary.binaryEncoding,blank,separator]
    | right i =>
      rw [extra_right]
      simp only [CountedLoopReuseAlphabet.bank,Tapes.append,Fin.addCases_right]
      fin_cases i <;> rfl

private theorem frame_marked (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :
    marked (raw (frame (radix := radix) source dest p q bs qs ns)) = frame source dest p q bs qs ns := by
  unfold marked raw frame
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> simp [workspace,marker]
  · funext i z
    fin_cases i <;> simp [workspace,marker,Function.update_apply,RadixZeroFill.radixEmpty]

private theorem metadata_marked (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool)
    (ds : Fin (c+1) → List (Fin radix)) :
    let metadata := Placement.extra (RationalPrefixTranslationInit.streamPlacement c)
      (CountedLoopReuseAlphabet.bank
        (RationalPrefixTranslationExecution.bank source dest p q bs qs [] [] ds)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
    marked (raw metadata) = metadata := by
  dsimp only
  rw [metadata_eq]
  exact frame_marked _ _ _ _ _ _ _

/-- Every writable metadata tape is genuinely blank, with its head at zero. -/
theorem raw_workspace (v : Tapes 17 radix) (i : Fin 17) (hi : workspace i = true) :
    (raw v).head i = 0 ∧ (raw v).tape i = (fun _ => blank) := by simp [raw,hi]

/-- Both complete supplied descriptor/payload tapes and their heads are retained. -/
theorem raw_retained (v : Tapes 17 radix) (i : Fin 17) (hi : workspace i = false) :
    (raw v).head i = v.head i ∧ (raw v).tape i = v.tape i := by simp [raw,hi]

def setup (t : ℕ) : Program (t+17) 2 radix :=
  Placement.placed markerProgram (finAddFlip : Fin (17+t) ≃ Fin (t+17))

private theorem setup_hoare {t : ℕ} (prefixBank : Tapes t radix) (v : Tapes 17 radix)
    (hv : marked (raw v) = v) :
    HoareTime (setup t) (fun x => x = prefixBank.append (raw v)) (fun x => x = prefixBank.append v) 1 := by
  let e : Fin (17+t) ≃ Fin (t+17) := finAddFlip
  have ha (w : Tapes 17 radix) : Placement.active e (prefixBank.append w) = w := by
    cases w; simp [Placement.active,e,Tapes.append,finAddFlip_apply_castAdd]
  have he (w : Tapes 17 radix) : Placement.extra e (prefixBank.append w) = prefixBank := by
    cases prefixBank; simp [Placement.extra,e,Tapes.append,finAddFlip_apply_natAdd]
  have hm := marker_hoare (raw v)
  rw [hv] at hm
  have hh := Placement.hoare_at hm e (prefixBank.append (raw v)) (ha (raw v))
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro x ⟨w,hw,hx⟩
  subst w
  rw [hx,Placement.replace,he]
  simpa only [ha,he] using Placement.view e (prefixBank.append v)

variable [Fact radix.Prime]

private theorem initial_marked {P : ℕ} (r : ℚ) (order : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (a : Fin (P*(radix^(width 0)*B)) → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs ns : List Bool) :
    let frame := Placement.extra (RationalPrefixTranslationInit.streamPlacement c)
      (FlatControlledShift.bank r order width a source dest p q bs qs ns 0)
    marked (raw frame) = frame := by
  exact metadata_marked _ _ _ _ _ _ _ _

/-- All writable prefix and metadata tapes begin blank; only dimensional
input descriptors and payload tapes retain their supplied representation. -/
def input {P : ℕ} (r : ℚ) (order : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (ws : Fin (c+1) → List Bool) (a : Fin (P*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :=
  (PrefixCounterInit.input (q := radix) (c+1) ws).append
    (raw (Placement.extra (RationalPrefixTranslationInit.streamPlacement c)
      (FlatControlledShift.bank r order width a source dest p q bs qs ns 0)))

def program (r : ℚ) (order : List (Fin (c+1))) (hne : order ≠ []) :=
  seq (setup (radix := radix) (PrefixCounterInit.tapeCount (c+1)))
    (RationalPrefixTranslationInit.program (radix := radix) r order hne)

/-- One literal transition creates every initial sentinel and moves the spare
head, preserving the supplied numeric descriptors and all payload symbols. -/
theorem bootstrap_hoare {P : ℕ} (r : ℚ) (order : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (ws : Fin (c+1) → List Bool) (a : Fin (P*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :
    HoareTime (setup (PrefixCounterInit.tapeCount (c+1)))
      (fun v => v = input r order width ws a source dest p q bs qs ns)
      (fun v => v = RationalPrefixTranslationInit.input r order width ws a source dest p q bs qs ns) 1 :=
  setup_hoare _ _ (initial_marked r order width a source dest p q bs qs ns)

/-- Complete blank-workspace controlled shift. The bound includes marker setup,
all prefix initialization, rational arithmetic, scheduling, and data movement. -/
theorem realizes_hoare (r : ℚ) (hden : r.den < radix)
    (low high : List (Fin (c+1))) (hfull : (low++0::high).Perm (List.finRange (c+1)))
    (width : Fin (c+1) → ℕ) (ws : Fin (c+1) → List Bool)
    (hw : ∀ i, Counter.value (ws i) = width i) (cw : ∀ i, GrowingCounterData.Canonical (ws i))
    (hB : 0 < B)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^(width 0))
    (hn : Counter.value ns = radix^PrefixAddressData.widthSum (low++0::high) width)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) :
    HoareTime (program r (low++0::high) (by simp))
      (fun v => v = input r (low++0::high) width ws a source dest p q bs qs ns)
      (fun v => v = RationalPrefixTranslationInit.output r (low++0::high) width ws a source dest p q bs qs ns)
      ((551+4*c)*(radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B))+29*(c+1)+26) := by
  have hm := bootstrap_hoare r (low++0::high) width ws a source dest p q bs qs ns
  have hs := RationalPrefixTranslationInit.realizes_hoare_linear r hden low high hfull width ws hw cw hB
    a source dest p q bs qs ns hb hq hn cb cq cn
  exact (hm.seq hs).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.RationalPrefixTranslationBootstrap
