import IntegerMultBounds.Machine.WordSegments
import IntegerMultBounds.Machine.Hoare

/-! Fixed two-phase machines use a preserved bit word as a unary length clock.
Each clock bit pays exactly two transitions. Seeking retains every cell;
reverse copying writes Booleanized source cells, treating blank as false. -/
namespace IntegerMultBounds.Machine.DoubleClockReverseCopy
variable {a : ℕ}

def readBit (x : Fin (a+4)) : Bool := decide (x = bitSymbol true)
@[simp] theorem readBit_symbol (b : Bool) : readBit (bitSymbol (a := a) b) = b := by
  cases b <;> simp [readBit,bitSymbol,Fin.ext_iff]
@[simp] theorem readBit_blank : readBit (blank : Fin (a+4)) = false := by
  simp [readBit,blank,bitSymbol,Fin.ext_iff]

def copied (f : ℤ → Fin (a+4)) (p : ℤ) : ℕ → List Bool
  | 0 => []
  | n+1 => [readBit (f p),readBit (f (p-1))] ++ copied f (p-2) n

@[simp] theorem copied_length (f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ) :
    (copied f p n).length = 2*n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp [copied,ih]; omega

def seekBank (f g : ℤ → Fin (a+4)) (p pc : ℤ) : Tapes 2 a := ⟨![p,pc],![f,g]⟩
def copyBank (f g h : ℤ → Fin (a+4)) (p pc pt : ℤ) : Tapes 3 a := ⟨![p,pc,pt],![f,g,h]⟩
def seekCfg (f g : ℤ → Fin (a+4)) (p pc : ℤ) (st : Fin 2) : Config 2 2 a :=
  ⟨st,(seekBank f g p pc).head,(seekBank f g p pc).tape⟩
def copyCfg (f g h : ℤ → Fin (a+4)) (p pc pt : ℤ) (st : Fin 2) : Config 3 2 a :=
  ⟨st,(copyBank f g h p pc pt).head,(copyBank f g h p pc pt).tape⟩

def doubleSeekProgram (a : ℕ) : Program 2 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun st sy => if st = 0 then
    if sy 1 = blank then none else some (1,fun i => (sy i,if i = 0 then .right else .stay))
    else some (0,fun i => (sy i,.right))

def reverseCopyProgram (a : ℕ) : Program 3 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun st sy => if st = 0 then
    if sy 1 = blank then none else some (1,fun i =>
      (if i = 2 then bitSymbol (readBit (sy 0)) else sy i,
        if i = 0 then .left else if i = 1 then .stay else .right))
    else some (0,fun i => (if i = 2 then bitSymbol (readBit (sy 0)) else sy i,
      if i = 0 then .left else .right))

private theorem seek_zero (f g : ℤ → Fin (a+4)) (p pc : ℤ) (hg : g pc ≠ blank) :
    step (doubleSeekProgram a) (seekCfg f g p pc 0) = some (seekCfg f g (p+1) pc 1) := by
  have hg' : ![f,g] (1 : Fin 2) (![p,pc] 1) ≠ blank := hg
  dsimp only [step,doubleSeekProgram,seekCfg,seekBank]
  simp only [ite_true,ite_eq_right hg',Move.offset]
  congr 1
  apply congrArg₂ (Config.mk (1 : Fin 2))
  · funext i; fin_cases i <;> simp
  · funext i z; fin_cases i <;> simp
    all_goals intro he; rw [he]

private theorem seek_one (f g : ℤ → Fin (a+4)) (p pc : ℤ) :
    step (doubleSeekProgram a) (seekCfg f g p pc 1) = some (seekCfg f g (p+1) (pc+1) 0) := by
  simp only [step,doubleSeekProgram,seekCfg,seekBank,show (1 : Fin 2) ≠ 0 by decide,ite_false,Move.offset]
  congr 1
  apply congrArg₂ (Config.mk (0 : Fin 2))
  · funext i; fin_cases i <;> rfl
  · funext i z; fin_cases i <;> simp
    all_goals intro he; rw [he]

private theorem seek_two (f g : ℤ → Fin (a+4)) (p pc : ℤ) (hg : g pc ≠ blank) :
    run (doubleSeekProgram a) 2 (seekCfg f g p pc 0) = some (seekCfg f g (p+2) (pc+1) 0) := by
  change (step (doubleSeekProgram a) (seekCfg f g p pc 0)).bind
    (fun c => (step (doubleSeekProgram a) c).bind (fun d => some d)) = _
  rw [seek_zero f g p pc hg]
  simp only [Option.bind_some,seek_one]
  congr 2
  omega

private theorem copy_zero (f g h : ℤ → Fin (a+4)) (p pc pt : ℤ) (hg : g pc ≠ blank) :
    step (reverseCopyProgram a) (copyCfg f g h p pc pt 0) =
      some (copyCfg f g (Function.update h pt (bitSymbol (readBit (f p)))) (p-1) pc (pt+1) 1) := by
  have hg' : ![f,g,h] (1 : Fin 3) (![p,pc,pt] 1) ≠ blank := hg
  dsimp only [step,reverseCopyProgram,copyCfg,copyBank]
  simp only [ite_true,ite_eq_right hg',Move.offset]
  congr 1
  apply congrArg₂ (Config.mk (1 : Fin 2))
  · funext i; fin_cases i <;> simp
    omega
  · funext i z; fin_cases i <;> simp [Function.update_apply]
    all_goals intro he; rw [he]

private theorem copy_one (f g h : ℤ → Fin (a+4)) (p pc pt : ℤ) :
    step (reverseCopyProgram a) (copyCfg f g h p pc pt 1) =
      some (copyCfg f g (Function.update h pt (bitSymbol (readBit (f p)))) (p-1) (pc+1) (pt+1) 0) := by
  simp only [step,reverseCopyProgram,copyCfg,copyBank,show (1 : Fin 2) ≠ 0 by decide,ite_false,Move.offset]
  congr 1
  apply congrArg₂ (Config.mk (0 : Fin 2))
  · funext i; fin_cases i <;> simp
    omega
  · funext i z; fin_cases i <;> simp [Function.update_apply]
    all_goals intro he; rw [he]

private theorem copy_two (f g h : ℤ → Fin (a+4)) (p pc pt : ℤ) (hg : g pc ≠ blank) :
    run (reverseCopyProgram a) 2 (copyCfg f g h p pc pt 0) =
      some (copyCfg f g (putWord h pt ([readBit (f p),readBit (f (p-1))].map bitSymbol))
        (p-2) (pc+1) (pt+2) 0) := by
  change (step (reverseCopyProgram a) (copyCfg f g h p pc pt 0)).bind
    (fun c => (step (reverseCopyProgram a) c).bind (fun d => some d)) = _
  rw [copy_zero f g h p pc pt hg]
  simp only [Option.bind_some,copy_one,List.map_cons,List.map_nil,putWord_cons,putWord]
  congr 2 <;> omega

private theorem seek_run (f g : ℤ → Fin (a+4)) (p pc : ℤ) (n : ℕ)
    (hg : ∀ i < n, g (pc+i) ≠ blank) :
    run (doubleSeekProgram a) (2*n) (seekCfg f g p pc 0) =
      some (seekCfg f g (p+2*n) (pc+n) 0) := by
  induction n generalizing p pc with
  | zero => simp [run]
  | succ n ih =>
    rw [show 2*(n+1)=2+2*n by omega,run_add,seek_two f g p pc (by simpa using hg 0 (by omega))]
    simp only [Option.bind_some]
    rw [ih (p+2) (pc+1) (by
      intro i hi
      have h := hg (i+1) (by omega)
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using h)]
    congr 2 <;> push_cast <;> ring

private theorem copy_run (f g h : ℤ → Fin (a+4)) (p pc pt : ℤ) (n : ℕ)
    (hg : ∀ i < n, g (pc+i) ≠ blank) :
    run (reverseCopyProgram a) (2*n) (copyCfg f g h p pc pt 0) =
      some (copyCfg f g (putWord h pt ((copied f p n).map bitSymbol)) (p-2*n) (pc+n) (pt+2*n) 0) := by
  induction n generalizing h p pc pt with
  | zero => simp [run,copied,putWord]
  | succ n ih =>
    rw [show 2*(n+1)=2+2*n by omega,run_add,copy_two f g h p pc pt (by simpa using hg 0 (by omega))]
    simp only [Option.bind_some]
    rw [ih _ (p-2) (pc+1) (pt+2) (by
      intro i hi
      have h := hg (i+1) (by omega)
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using h)]
    have hw := putWord_append_forward h pt ([readBit (f p),readBit (f (p-1))].map bitSymbol)
      ((copied f (p-2) n).map bitSymbol)
    simp only [List.length_map,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.cast_ofNat,
      ← List.map_append] at hw
    rw [hw]
    simp only [copied]
    congr 2 <;> push_cast <;> ring

private theorem clock_nonblank (g : ℤ → Fin (a+4)) (pc : ℤ) (xs : List Bool)
    (i : ℕ) (hi : i < xs.length) : putWord g pc (xs.map bitSymbol) (pc+i) ≠ blank := by
  rw [WordSegments.get _ _ _ i (by simpa using hi),List.getElem_map]
  cases xs[i] <;> simp [bitSymbol,blank,Fin.ext_iff]

private theorem clock_end (g : ℤ → Fin (a+4)) (pc : ℤ) (xs : List Bool)
    (hg : g (pc+xs.length) = blank) : putWord g pc (xs.map bitSymbol) (pc+xs.length) = blank := by
  rw [putWord_outside _ _ _ _ (Or.inr (by simp)),hg]

/-- Exactly two paid transitions per clock symbol, including the empty clock.
The complete source and clock tapes are retained literally. -/
theorem doubleSeek_exact (f g : ℤ → Fin (a+4)) (p pc : ℤ) (xs : List Bool)
    (hg : g (pc+xs.length) = blank) :
    run (doubleSeekProgram a) (2*xs.length)
        (seekCfg f (putWord g pc (xs.map bitSymbol)) p pc 0) =
      some (seekCfg f (putWord g pc (xs.map bitSymbol)) (p+2*xs.length) (pc+xs.length) 0) ∧
    step (doubleSeekProgram a)
      (seekCfg f (putWord g pc (xs.map bitSymbol)) (p+2*xs.length) (pc+xs.length) 0) = none := by
  refine ⟨seek_run _ _ _ _ _ (clock_nonblank g pc xs),?_⟩
  simp [step,doubleSeekProgram,seekCfg,seekBank,clock_end g pc xs hg]

theorem doubleSeek_hoare (f g : ℤ → Fin (a+4)) (p pc : ℤ) (xs : List Bool)
    (hg : g (pc+xs.length) = blank) :
    HoareTime (doubleSeekProgram a)
      (fun v => v = seekBank f (putWord g pc (xs.map bitSymbol)) p pc)
      (fun v => v = seekBank f (putWord g pc (xs.map bitSymbol)) (p+2*xs.length) (pc+xs.length))
      (2*xs.length) := by
  obtain ⟨hr,hh⟩ := doubleSeek_exact f g p pc xs hg
  rintro v rfl
  exact ⟨2*xs.length,_,le_rfl,hr,hh,rfl⟩

/-- Reverse exactly twice the clock length, Booleanizing each read cell.
Only the displayed target segment changes; both input tapes stay literal. -/
theorem reverseCopy_exact (f g h : ℤ → Fin (a+4)) (p pc pt : ℤ) (xs : List Bool)
    (hg : g (pc+xs.length) = blank) :
    run (reverseCopyProgram a) (2*xs.length)
        (copyCfg f (putWord g pc (xs.map bitSymbol)) h p pc pt 0) =
      some (copyCfg f (putWord g pc (xs.map bitSymbol))
        (putWord h pt ((copied f p xs.length).map bitSymbol))
        (p-2*xs.length) (pc+xs.length) (pt+2*xs.length) 0) ∧
    step (reverseCopyProgram a)
      (copyCfg f (putWord g pc (xs.map bitSymbol))
        (putWord h pt ((copied f p xs.length).map bitSymbol))
        (p-2*xs.length) (pc+xs.length) (pt+2*xs.length) 0) = none := by
  refine ⟨copy_run _ _ _ _ _ _ _ (clock_nonblank g pc xs),?_⟩
  simp [step,reverseCopyProgram,copyCfg,copyBank,clock_end g pc xs hg]

theorem reverseCopy_hoare (f g h : ℤ → Fin (a+4)) (p pc pt : ℤ) (xs : List Bool)
    (hg : g (pc+xs.length) = blank) :
    HoareTime (reverseCopyProgram a)
      (fun v => v = copyBank f (putWord g pc (xs.map bitSymbol)) h p pc pt)
      (fun v => v = copyBank f (putWord g pc (xs.map bitSymbol))
        (putWord h pt ((copied f p xs.length).map bitSymbol))
        (p-2*xs.length) (pc+xs.length) (pt+2*xs.length)) (2*xs.length) := by
  obtain ⟨hr,hh⟩ := reverseCopy_exact f g h p pc pt xs hg
  rintro v rfl
  exact ⟨2*xs.length,_,le_rfl,hr,hh,rfl⟩

end IntegerMultBounds.Machine.DoubleClockReverseCopy
