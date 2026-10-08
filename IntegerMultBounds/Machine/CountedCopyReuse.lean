import IntegerMultBounds.Machine.CountedCopy
import IntegerMultBounds.Machine.Copy
import IntegerMultBounds.Machine.Frame
import IntegerMultBounds.Machine.Rewind

/-! Reusable binary-counted copying. The immutable binary descriptor is already
prepared on its own tape. The program physically copies it to a local work
clock, resets both heads, transfers the raw payload, and clears and resets the
clock. All joins and head movements are charged. Source and destination data
need no markers; their heads finish just after the transferred segment. -/

namespace IntegerMultBounds.Machine.CountedCopyReuse

private def ExactRun {t q : ℕ} (M : Program t q 0) (n : ℕ) (v w : Tapes t 0) : Prop :=
  ∃ c, run M n (v.start M) = some c ∧ step M c = none ∧ c.tapes = w

private theorem exact_seq {t q r : ℕ} {M : Program t q 0} {N : Program t r 0}
    {k l : ℕ} {v w z : Tapes t 0} (hm : ExactRun M k v w) (hn : ExactRun N l w z) :
    ExactRun (seq M N) (k+1+l) v z := by
  obtain ⟨c,hr,hh,hc⟩ := hm
  obtain ⟨d,hs,hd,he⟩ := hn
  refine ⟨d.mapState (Fin.natAdd q),?_,seq_halt_right M N hd,he⟩
  rw [← hc] at hs
  exact seq_run M N hr hh hs

/-- An empty local clock/descriptor area with a retained left sentinel. -/
def empty : ℤ → Fin 4 := fun j => if j = 0 then separator else blank

def binary (bs : List Bool) : ℤ → Fin 4 := putBits empty 1 bs

private theorem binary_marker (bs : List Bool) : binary bs 0 = separator := by
  rw [binary,putBits_outside _ _ _ _ (Or.inl (by omega))]
  rfl

private theorem binary_end (bs : List Bool) : binary bs (1+bs.length) = blank := by
  rw [binary,putBits_outside _ _ _ _ (Or.inr (by omega))]
  simp [empty,show (1:ℤ)+bs.length ≠ 0 by omega]

private theorem binary_ne_marker (bs : List Bool) (j : ℤ) (hj : 0 < j) :
    binary bs j ≠ separator := by
  by_cases hh : j < 1+bs.length
  · exact putBits_ne_separator empty 1 j bs (by omega) hh
  · rw [binary,putBits_outside _ _ _ _ (Or.inr (by omega))]
    simp [empty,ne_of_gt hj,blank,separator]

private theorem bits_word (f : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
    putBits f p bs = putWord f p (bs.map bitSymbol) := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih => simp only [putBits,putWord,List.map_cons,ih]

/-- One real head movement after a sentinel-stopping rewind. -/
def rightProgram : Program 1 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols => if s = 0 then some (1,fun i => (symbols i,.right)) else none

private def one (f : ℤ → Fin 4) (p : ℤ) : Tapes 1 0 := ⟨fun _ => p,fun _ => f⟩

private theorem right_exact (f : ℤ → Fin 4) (p : ℤ) :
    ExactRun rightProgram 1 (one f p) (one f (p+1)) := by
  refine ⟨⟨1,fun _ => p+1,fun _ => f⟩,?_,?_,rfl⟩
  · simp only [run_one,step,rightProgram,one,Tapes.start,↓reduceIte,Move.offset]
    congr 1
    congr 1
    funext i j
    by_cases hj : j = p
    · subst j; simp
    · simp [hj]
  · simp [step,rightProgram]

/-- Rewind to the marker and physically return to the first data position. -/
def resetProgram : Program 1 3 0 := seq (Rewind.program separator) rightProgram

private theorem reset_exact (bs : List Bool) (n : ℕ) :
    ExactRun resetProgram (n+2) (one (binary bs) n) (one (binary bs) 1) := by
  obtain ⟨hr,hh⟩ := Rewind.rewind_exact separator (binary bs) n n
    (by intro j hj; exact binary_ne_marker bs _ (by omega))
    (by simpa using binary_marker bs)
  have h₁ : ExactRun (Rewind.program separator) n (one (binary bs) n) (one (binary bs) 0) := by
    refine ⟨Rewind.cfg (binary bs) 0,?_,?_,rfl⟩
    · simpa only [sub_self,one,Tapes.start,Rewind.cfg,Rewind.program] using hr
    · simpa only [sub_self] using hh
  simpa only [zero_add,resetProgram,Nat.add_assoc] using exact_seq h₁ (right_exact (binary bs) 0)

/-- Erase the locally stored clock by a forward scan. No payload cells or
ancestor workspace are traversed by this one-tape primitive. -/
def clearProgram : Program 1 1 0 where
  tapes_pos := by decide
  start := 0
  transition := fun _ symbols => if symbols 0 = blank then none else
    some (0,fun _ => (blank,.right))

private def clearCfg (f : ℤ → Fin 4) (p : ℤ) : Config 1 1 0 := ⟨0,fun _ => p,fun _ => f⟩

private theorem clear_step (f : ℤ → Fin 4) (p : ℤ) (h : f p ≠ blank) :
    step clearProgram (clearCfg f p) = some (clearCfg (Function.update f p blank) (p+1)) := by
  simp only [step,clearProgram,clearCfg,h,↓reduceIte,Move.offset]
  congr 1
  congr 1
  funext i j
  simp [Function.update_apply,eq_comm]

private theorem clear_run (f : ℤ → Fin 4) (p : ℤ) (xs : List (Fin 4))
    (hxs : ∀ x ∈ xs, x ≠ blank) :
    run clearProgram xs.length (clearCfg (putWord f p xs) p) =
      some (clearCfg (putWord f p (xs.map (fun _ => blank))) (p+xs.length)) := by
  induction xs generalizing f p with
  | nil => simp [run,putWord]
  | cons x xs ih =>
    have hs := clear_step (putWord f p (x::xs)) p
      (by rw [putWord_head]; exact hxs x (by simp))
    rw [putWord_replace_head] at hs
    simp only [List.length_cons,run,hs,Option.bind_some]
    have hr := ih (Function.update f p blank) (p+1) (fun y hy => hxs y (by simp [hy]))
    simpa only [List.map_cons,← putWord_cons,Nat.cast_add,Nat.cast_one,
      add_assoc,add_comm,add_left_comm] using hr

private theorem putWord_blank_eq (f : ℤ → Fin 4) (p : ℤ) (xs : List (Fin 4))
    (hf : ∀ j : ℤ, p ≤ j → f j = blank) :
    putWord f p (xs.map (fun _ => blank)) = f := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,putWord,ih (p+1) (fun j hj => hf j (by omega))]
    exact Function.update_eq_self_iff.mpr (hf p le_rfl).symm

private theorem clear_exact (bs : List Bool) :
    ExactRun clearProgram bs.length (one (binary bs) 1) (one empty (1+bs.length)) := by
  have hxs : ∀ x ∈ bs.map bitSymbol, x ≠ (blank : Fin 4) := by
    intro x hx
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
    cases b <;> decide
  have hr := clear_run empty 1 (bs.map bitSymbol) hxs
  have he : putWord empty 1 ((bs.map bitSymbol).map (fun _ => blank)) = empty :=
    putWord_blank_eq empty 1 _ (by intro j hj; simp [empty,show j ≠ 0 by omega])
  rw [he,List.length_map,← bits_word] at hr
  refine ⟨clearCfg empty (1+bs.length),hr,?_,rfl⟩
  simp [step,clearProgram,clearCfg,empty,show (1:ℤ)+bs.length ≠ 0 by omega]

private def place (i : Fin 4) : Fin 4 ≃ Fin 4 := Equiv.swap 0 i

private def single (v : Tapes 4 0) (i : Fin 4) : Tapes 1 0 :=
  one (v.tape i) (v.head i)

private def extra (v : Tapes 4 0) (i : Fin 4) : Tapes 3 0 :=
  ⟨fun j => v.head (place i (Fin.natAdd 1 j)),fun j => v.tape (place i (Fin.natAdd 1 j))⟩

private def replace (v : Tapes 4 0) (i : Fin 4) (w : Tapes 1 0) : Tapes 4 0 :=
  ⟨Function.update v.head i (w.head 0),Function.update v.tape i (w.tape 0)⟩

/-- Physical placement of a one-tape subroutine, retaining the other tapes. -/
def placed {q : ℕ} (M : Program 1 q 0) (i : Fin 4) : Program 4 q 0 :=
  reindex (extend M 3) (place i)

private theorem single_view (v : Tapes 4 0) (i : Fin 4) :
    ((single v i).append (extra v i)).reindex (place i) = v := by
  cases v
  unfold single one extra Tapes.append Tapes.reindex
  congr 1
  · funext j; fin_cases i <;> fin_cases j <;> rfl
  · funext j; fin_cases i <;> fin_cases j <;> rfl

private theorem placed_exact {q n : ℕ} (M : Program 1 q 0) (v : Tapes 4 0) (i : Fin 4)
    (w : Tapes 1 0) (h : ExactRun M n (single v i) w) :
    ExactRun (placed M i) n v (replace v i w) := by
  obtain ⟨c,hr,hh,hc⟩ := h
  have hs := reindex_run (extend M 3) (place i) (extend_run M (extra v i) hr)
  have ht := reindex_halt (extend M 3) (place i) (extend_halt M (extra v i) hh)
  have hb : (((single v i).start M).extend (extra v i)).reindex (place i) =
      v.start (placed M i) := by
    have hv := single_view v i
    unfold Config.reindex Config.extend Tapes.start
    congr 1
    · exact congrArg Tapes.head hv
    · exact congrArg Tapes.tape hv
  rw [hb] at hs
  refine ⟨_,hs,ht,?_⟩
  change (c.tapes.append (extra v i)).reindex (place i) = _
  rw [hc]
  unfold Tapes.append Tapes.reindex extra replace
  congr 1
  · funext j; fin_cases i <;> fin_cases j <;> rfl
  · funext j; fin_cases i <;> fin_cases j <;> rfl

/-- Tape slots are source, destination, work clock, immutable descriptor. -/
def bank (source dest clock descriptor : ℤ → Fin 4) (p q r s : ℤ) : Tapes 4 0 where
  head := fun i => if i = 0 then p else if i = 1 then q else if i = 2 then r else s
  tape := fun i => if i = 0 then source else if i = 1 then dest else if i = 2 then clock else descriptor

private theorem reset_clock (source dest : ℤ → Fin 4) (bs desc : List Bool) (p q s : ℤ) (n : ℕ) :
    ExactRun (placed resetProgram 2) (n+2)
      (bank source dest (binary bs) (binary desc) p q n s)
      (bank source dest (binary bs) (binary desc) p q 1 s) := by
  have h := placed_exact resetProgram (bank source dest (binary bs) (binary desc) p q n s) 2
    (one (binary bs) 1) (reset_exact bs n)
  convert h using 1
  unfold replace bank one
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

private theorem reset_descriptor (source dest : ℤ → Fin 4) (bs desc : List Bool)
    (p q r : ℤ) (n : ℕ) :
    ExactRun (placed resetProgram 3) (n+2)
      (bank source dest (binary bs) (binary desc) p q r n)
      (bank source dest (binary bs) (binary desc) p q r 1) := by
  have h := placed_exact resetProgram (bank source dest (binary bs) (binary desc) p q r n) 3
    (one (binary desc) 1) (reset_exact desc n)
  convert h using 1
  unfold replace bank one
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

private theorem clear_clock (source dest : ℤ → Fin 4) (bs desc : List Bool) (p q s : ℤ) :
    ExactRun (placed clearProgram 2) bs.length
      (bank source dest (binary bs) (binary desc) p q 1 s)
      (bank source dest empty (binary desc) p q (1+bs.length) s) := by
  have h := placed_exact clearProgram (bank source dest (binary bs) (binary desc) p q 1 s) 2
    (one empty (1+bs.length)) (clear_exact bs)
  convert h using 1
  unfold replace bank one
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-- Place the descriptor-to-clock copy at physical slots three and two. -/
def preparePlacement : Fin 4 ≃ Fin 4 where
  toFun := fun i => if i = 0 then 3 else if i = 1 then 2 else if i = 2 then 1 else 0
  invFun := fun i => if i = 0 then 3 else if i = 1 then 2 else if i = 2 then 1 else 0
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

def prepareProgram : Program 4 1 0 :=
  reindex (extend (Copy.program blank false) 2) preparePlacement

private def prepareExtra (source dest : ℤ → Fin 4) (p q : ℤ) : Tapes 2 0 :=
  ⟨fun i => if i = 0 then q else p,fun i => if i = 0 then dest else source⟩

private theorem prepare_bank (source dest clock descriptor : ℤ → Fin 4) (p q r s : ℤ) :
    ((Copy.tapes descriptor clock s r).append (prepareExtra source dest p q)).reindex
      preparePlacement = bank source dest clock descriptor p q r s := by
  unfold Copy.tapes Copy.cfg Config.tapes Tapes.append Tapes.reindex prepareExtra bank
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

private theorem prepare_exact (source dest : ℤ → Fin 4) (p q : ℤ) (bs : List Bool) :
    ExactRun prepareProgram bs.length
      (bank source dest empty (binary bs) p q 1 1)
      (bank source dest (binary bs) (binary bs) p q (1+bs.length) (1+bs.length)) := by
  have hxs : ∀ x ∈ bs.map bitSymbol, x ≠ (blank : Fin 4) := by
    intro x hx
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
    cases b <;> decide
  obtain ⟨hr,hh⟩ := Copy.copy_exact blank false empty empty 1 1 (bs.map bitSymbol) hxs
    (by simp [empty,show (1:ℤ)+bs.length ≠ 0 by omega])
  have hret : (Copy.retained false : Fin 4 → Fin 4) = id := rfl
  simp only [hret,List.map_id,List.length_map,← bits_word] at hr hh
  have hs := reindex_run (extend (Copy.program blank false) 2) preparePlacement
    (extend_run (Copy.program blank false) (prepareExtra source dest p q) hr)
  have ht := reindex_halt (extend (Copy.program blank false) 2) preparePlacement
    (extend_halt (Copy.program blank false) (prepareExtra source dest p q) hh)
  have hb : ((Copy.cfg (binary bs) empty 1 1).extend (prepareExtra source dest p q)).reindex
      preparePlacement = (bank source dest empty (binary bs) p q 1 1).start prepareProgram := by
    have hv := prepare_bank source dest empty (binary bs) p q 1 1
    unfold Config.reindex Config.extend Tapes.start
    congr 1
    · exact congrArg Tapes.head hv
    · exact congrArg Tapes.tape hv
  simp only [binary] at hb
  rw [hb] at hs
  exact ⟨_,hs,ht,prepare_bank source dest (binary bs) (binary bs) p q _ _⟩

private theorem counted_bank (source dest clock descriptor : ℤ → Fin 4)
    (p q r s : ℤ) (state : Fin 5) :
    ((CountedCopy.cfg source dest clock p q r state).tapes.append (one descriptor s)) =
      bank source dest clock descriptor p q r s := by
  unfold CountedCopy.cfg Config.tapes Tapes.append bank one
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

private theorem counted_exact (source dest : ℤ → Fin 4) (p q : ℤ)
    (xs : List (Fin 4)) (bs : List Bool) (hcount : Counter.value bs = xs.length) :
    ExactRun (extend CountedCopy.program 1) (CountedCopy.runtime xs.length bs)
      (bank (putWord source p xs) dest (binary bs) (binary bs) p q 1 1)
      (bank (putWord source p xs) (putWord dest q xs)
        (binary (List.replicate bs.length true)) (binary bs) (p+xs.length) (q+xs.length) 1 1) := by
  obtain ⟨_,hr,hh⟩ := CountedCopy.copy_exact source dest empty p q xs bs hcount rfl
    (by simp [empty,show (1:ℤ)+bs.length ≠ 0 by omega])
  have hs := extend_run CountedCopy.program (one (binary bs) 1) hr
  have ht := extend_halt CountedCopy.program (one (binary bs) 1) hh
  have hb : (CountedCopy.cfg (putWord source p xs) dest (binary bs) p q 1 0).extend
      (one (binary bs) 1) =
      (bank (putWord source p xs) dest (binary bs) (binary bs) p q 1 1).start
        (extend CountedCopy.program 1) := by
    have hv := counted_bank (putWord source p xs) dest (binary bs) (binary bs) p q 1 1 0
    unfold Config.extend Tapes.start
    congr 1
    · exact congrArg Tapes.head hv
    · exact congrArg Tapes.tape hv
  change run (extend CountedCopy.program 1) (CountedCopy.runtime xs.length bs)
    ((CountedCopy.cfg (putWord source p xs) dest (binary bs) p q 1 0).extend
      (one (binary bs) 1)) = _ at hs
  rw [hb] at hs
  exact ⟨_,hs,ht,counted_bank _ _ _ _ _ _ _ _ _⟩

/-- Fixed finite control prepares the clock, copies the raw stream, and restores
both reusable control areas. It never scans payload cells for a sentinel. -/
def program : Program 4 16 0 :=
  seq (seq (seq (seq (seq prepareProgram (placed resetProgram 3))
    (placed resetProgram 2)) (extend CountedCopy.program 1))
    (placed clearProgram 2)) (placed resetProgram 2)

def runtime (length : ℕ) (bs : List Bool) : ℕ :=
  CountedCopy.runtime length bs + 5*bs.length+14

/-- All work-clock cells are blank again, its left sentinel is retained, and
both control heads return to the first bit. The entire descriptor is preserved.
Raw source/destination head movement is exactly the transferred length. -/
theorem copy_exact (source dest : ℤ → Fin 4) (p q : ℤ)
    (xs : List (Fin 4)) (bs : List Bool) (hcount : Counter.value bs = xs.length) :
    ∃ c, run program (runtime xs.length bs)
      ((bank (putWord source p xs) dest empty (binary bs) p q 1 1).start program) = some c ∧
      step program c = none ∧
      c.tapes = bank (putWord source p xs) (putWord dest q xs) empty (binary bs)
        (p+xs.length) (q+xs.length) 1 1 := by
  let input := putWord source p xs
  let output := putWord dest q xs
  let ones := List.replicate bs.length true
  have h₀ := prepare_exact input dest p q bs
  have h₁ := reset_descriptor input dest bs bs p q (1+bs.length) (bs.length+1)
  have h₂ := reset_clock input dest bs bs p q 1 (bs.length+1)
  have h₃ := counted_exact source dest p q xs bs hcount
  have h₄ := clear_clock input output ones bs (p+xs.length) (q+xs.length) 1
  have h₅ := reset_clock input output [] bs (p+xs.length) (q+xs.length) 1 (bs.length+1)
  simp only [ones,List.length_replicate] at h₄
  simp only [binary,putBits] at h₅
  have hcast : ((bs.length+1:ℕ):ℤ) = 1+bs.length := by omega
  simp only [hcast] at h₁ h₂ h₅
  have hs := exact_seq (exact_seq (exact_seq (exact_seq (exact_seq h₀ h₁) h₂) h₃) h₄) h₅
  have htime : bs.length+1+(bs.length+1+2)+1+(bs.length+1+2)+1+
      CountedCopy.runtime xs.length bs+1+bs.length+1+(bs.length+1+2) = runtime xs.length bs := by
    unfold runtime
    omega
  simpa only [program,htime,ExactRun,input,output,binary] using hs

theorem runtime_le_linear (xs : List (Fin 4)) (bs : List Bool)
    (hcount : Counter.value bs = xs.length) :
    runtime xs.length bs ≤ 5*xs.length+7*bs.length+16 := by
  have hh := CountdownData.countdown_cost bs
  change CountedCopy.runtime (Counter.value bs) bs ≤ 5*Counter.value bs+2*bs.length+2 at hh
  rw [hcount] at hh
  dsimp only [runtime]
  omega

/-- Reusable Hoare contract with actual linear time, including all preparation,
cleanup, subroutine joins, and control-head return movements. -/
theorem copy_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (xs : List (Fin 4)) (bs : List Bool) (hcount : Counter.value bs = xs.length) :
    HoareTime program
      (fun v => v = bank (putWord source p xs) dest empty (binary bs) p q 1 1)
      (fun v => v = bank (putWord source p xs) (putWord dest q xs) empty (binary bs)
        (p+xs.length) (q+xs.length) 1 1)
      (5*xs.length+7*bs.length+16) := by
  rintro v rfl
  obtain ⟨c,hr,hh,hc⟩ := copy_exact source dest p q xs bs hcount
  exact ⟨runtime xs.length bs,c,runtime_le_linear xs bs hcount,hr,hh,hc⟩

end IntegerMultBounds.Machine.CountedCopyReuse
