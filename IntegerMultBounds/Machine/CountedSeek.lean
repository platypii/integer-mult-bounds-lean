import IntegerMultBounds.Machine.CountedCopyReuse
import IntegerMultBounds.Machine.Reflection

/-! Delimiter-free seeking through an arbitrary raw payload. Project the
verified reusable counted-copy machine onto its source, clock, and descriptor
tapes. Its discarded destination cannot influence retained actions or control.
The resulting fixed three-tape machine preserves every payload cell and retains
all descriptor preparation, local clock cleanup, and exact runtime guarantees. -/

namespace IntegerMultBounds.Machine.CountedSeek

/-- Retain source, clock, and immutable descriptor, discarding only destination. -/
def pick (i : Fin 3) : Fin 4 := if i = 0 then 0 else if i = 1 then 2 else 3

def fill (symbols : Fin 3 → Fin 4) : Fin 4 → Fin 4 :=
  fun i => if i = 0 then symbols 0 else if i = 1 then blank else if i = 2 then symbols 1 else symbols 2

def projectAction (action : Fin 4 → Fin 4 × Move) : Fin 3 → Fin 4 × Move :=
  fun i => action (pick i)

def projectResult {q : ℕ} (result : Option (Fin q × (Fin 4 → Fin 4 × Move))) :
    Option (Fin q × (Fin 3 → Fin 4 × Move)) :=
  result.map (fun (state,action) => (state,projectAction action))

/-- This is an ordinary finite transition table. The omitted read is filled
with blank only after proving that it cannot affect the retained execution. -/
def program : Program 3 16 0 where
  tapes_pos := by decide
  start := CountedCopyReuse.program.start
  transition := fun state symbols => projectResult (CountedCopyReuse.program.transition state (fill symbols))

private theorem fill_pick (symbols : Fin 4 → Fin 4) (i : Fin 3) :
    fill (fun j => symbols (pick j)) (pick i) = symbols (pick i) := by
  fin_cases i <;> rfl

private def Independent {q : ℕ} (M : Program 4 q 0) : Prop :=
  ∀ state symbols, projectResult (M.transition state symbols) =
    projectResult (M.transition state (fill (fun i => symbols (pick i))))

private theorem project_seq_left {q r : ℕ} (M : Program 4 q 0) (N : Program 4 r 0)
    (state : Fin q) (symbols : Fin 4 → Fin 4) :
    projectResult ((seq M N).transition (Fin.castAdd r state) symbols) =
      match projectResult (M.transition state symbols) with
      | none => some (Fin.natAdd q N.start,fun i => (symbols (pick i),Move.stay))
      | some (s,act) => some (Fin.castAdd r s,act) := by
  simp only [seq,Fin.addCases_left]
  cases h : M.transition state symbols with
  | none => rfl
  | some v => rcases v with ⟨s,act⟩; rfl

private theorem project_seq_right {q r : ℕ} (M : Program 4 q 0) (N : Program 4 r 0)
    (state : Fin r) (symbols : Fin 4 → Fin 4) :
    projectResult ((seq M N).transition (Fin.natAdd q state) symbols) =
      (projectResult (N.transition state symbols)).map (fun (s,act) => (Fin.natAdd q s,act)) := by
  simp only [seq,Fin.addCases_right]
  cases h : N.transition state symbols with
  | none => rfl
  | some v => rcases v with ⟨s,act⟩; rfl

private theorem independent_seq {q r : ℕ} (M : Program 4 q 0) (N : Program 4 r 0)
    (hm : Independent M) (hn : Independent N) : Independent (seq M N) := by
  intro state symbols
  induction state using Fin.addCases with
  | left state =>
    rw [project_seq_left,project_seq_left,hm state symbols]
    simp only [fill_pick]
  | right state => rw [project_seq_right,project_seq_right,hn state symbols]

private theorem prepare_independent : Independent CountedCopyReuse.prepareProgram := by
  intro state symbols
  fin_cases state
  by_cases h : symbols 3 = blank <;>
    simp [CountedCopyReuse.prepareProgram,CountedCopyReuse.preparePlacement,Copy.program,Copy.retained,
      reindex,extend,projectResult,fill,pick,h]
  funext i
  fin_cases i <;> simp [projectAction,pick,Fin.addCases]

private theorem reset_independent (i : Fin 4) (hi : i = 2 ∨ i = 3) :
    Independent (CountedCopyReuse.placed CountedCopyReuse.resetProgram i) := by
  change Independent (reindex (extend CountedCopyReuse.resetProgram 3) (Equiv.swap 0 i))
  intro state symbols
  rcases hi with rfl | rfl
  · fin_cases state <;> (by_cases h : symbols 2 = separator) <;>
      simp [CountedCopyReuse.resetProgram,CountedCopyReuse.rightProgram,Rewind.program,
        seq,reindex,extend,Fin.addCases,Equiv.swap_apply_def,projectResult,fill,pick,h]
    all_goals funext j; fin_cases j <;> simp [projectAction,pick,h]
  · fin_cases state <;> (by_cases h : symbols 3 = separator) <;>
      simp [CountedCopyReuse.resetProgram,CountedCopyReuse.rightProgram,Rewind.program,
        seq,reindex,extend,Fin.addCases,Equiv.swap_apply_def,projectResult,fill,pick,h]
    all_goals funext j; fin_cases j <;> simp [projectAction,pick,h]

private theorem counted_independent : Independent (extend CountedCopy.program 1) := by
  intro state symbols
  fin_cases state <;> (generalize h : symbols 2 = x) <;> fin_cases x <;>
    simp [extend,CountedCopy.program,projectResult,fill,pick,h,bitSymbol,blank,separator]
  all_goals funext i; fin_cases i <;> simp [projectAction,pick,h,CountedCopy.clockAction,Fin.addCases,Fin.castLT]

private theorem clear_independent : Independent (CountedCopyReuse.placed CountedCopyReuse.clearProgram 2) := by
  change Independent (reindex (extend CountedCopyReuse.clearProgram 3) (Equiv.swap 0 2))
  intro state symbols
  fin_cases state
  by_cases h : symbols 2 = blank <;>
    simp [CountedCopyReuse.clearProgram,reindex,extend,Equiv.swap_apply_def,
      projectResult,fill,pick,h]
  funext i
  fin_cases i <;> simp [projectAction,pick,Fin.addCases]

private theorem transition_projection : Independent CountedCopyReuse.program := by
  exact independent_seq _ _ (independent_seq _ _ (independent_seq _ _
    (independent_seq _ _ (independent_seq _ _ prepare_independent (reset_independent 3 (Or.inr rfl)))
      (reset_independent 2 (Or.inl rfl))) counted_independent) clear_independent)
    (reset_independent 2 (Or.inl rfl))

/-- Forget only the discarded destination tape. -/
def projectConfig (c : Config 4 16 0) : Config 3 16 0 :=
  ⟨c.state,fun i => c.head (pick i),fun i => c.tape (pick i)⟩

/-- Exact transition simulation includes arbitrary discarded destination cells. -/
theorem step_projection (c : Config 4 16 0) :
    step program (projectConfig c) = (step CountedCopyReuse.program c).map projectConfig := by
  have htrans : program.transition (projectConfig c).state
      (fun i => (projectConfig c).tape i ((projectConfig c).head i)) =
      projectResult (CountedCopyReuse.program.transition c.state (fun i => c.tape i (c.head i))) :=
    (transition_projection c.state (fun i => c.tape i (c.head i))).symm
  unfold step
  rw [htrans]
  cases ht : CountedCopyReuse.program.transition c.state (fun i => c.tape i (c.head i)) with
  | none => rfl
  | some v => rcases v with ⟨state,action⟩; rfl

theorem run_projection {n : ℕ} {c d : Config 4 16 0}
    (h : run CountedCopyReuse.program n c = some d) :
    run program n (projectConfig c) = some (projectConfig d) := by
  apply run_simulation CountedCopyReuse.program program projectConfig _ h
  intro c d hs
  rw [step_projection,hs]
  rfl

theorem halt_projection {c : Config 4 16 0} (h : step CountedCopyReuse.program c = none) :
    step program (projectConfig c) = none := by
  rw [step_projection,h]
  rfl

/-- Input and output boundary layout: raw payload, empty reusable clock, and
immutable already-prepared little-endian binary descriptor. -/
def bank (payload : ℤ → Fin 4) (p : ℤ) (bs : List Bool) : Tapes 3 0 where
  head := fun i => if i = 0 then p else 1
  tape := fun i => if i = 0 then payload else if i = 1 then CountedCopyReuse.empty
    else CountedCopyReuse.binary bs

private theorem project_bank (source dest : ℤ → Fin 4) (p q : ℤ) (bs : List Bool) :
    (projectConfig ((CountedCopyReuse.bank source dest CountedCopyReuse.empty
      (CountedCopyReuse.binary bs) p q 1 1).start CountedCopyReuse.program)).tapes = bank source p bs := by
  unfold projectConfig CountedCopyReuse.bank Config.tapes Tapes.start bank
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

private def segment (payload : ℤ → Fin 4) (p : ℤ) : ℕ → List (Fin 4)
  | 0 => []
  | n+1 => payload p :: segment payload (p+1) n

private theorem segment_length (payload : ℤ → Fin 4) (p : ℤ) (n : ℕ) :
    (segment payload p n).length = n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [segment,List.length_cons,ih]

private theorem putWord_segment (payload : ℤ → Fin 4) (p : ℤ) (n : ℕ) :
    putWord payload p (segment payload p n) = payload := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [segment,putWord,ih,Function.update_eq_self]

/-- Head displacement is delimiter-free: every payload cell, including blank,
is retained literally. The reusable clock and descriptor return to their
original complete-tape representations and head positions. -/
theorem seek_exact (payload : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
    ∃ c, run program (CountedCopyReuse.runtime (Counter.value bs) bs)
      ((bank payload p bs).start program) = some c ∧ step program c = none ∧
      c.tapes = bank payload (p+Counter.value bs) bs := by
  let xs := segment payload p (Counter.value bs)
  have hlen : xs.length = Counter.value bs := segment_length payload p _
  obtain ⟨c,hr,hh,hc⟩ := CountedCopyReuse.copy_exact payload (fun _ => blank) p 0 xs bs hlen.symm
  have hself : putWord payload p xs = payload := putWord_segment payload p _
  simp only [hself,hlen] at hr hc
  have hs := run_projection hr
  have hbefore : projectConfig ((CountedCopyReuse.bank payload (fun _ => blank) CountedCopyReuse.empty
      (CountedCopyReuse.binary bs) p 0 1 1).start CountedCopyReuse.program) =
      (bank payload p bs).start program := by
    have hv := project_bank payload (fun _ => blank) p 0 bs
    unfold projectConfig Tapes.start
    congr 1
    · exact congrArg Tapes.head hv
    · exact congrArg Tapes.tape hv
  rw [hbefore] at hs
  refine ⟨projectConfig c,hs,halt_projection hh,?_⟩
  have hp := congrArg (fun v : Tapes 4 0 =>
    (⟨fun i => v.head (pick i),fun i => v.tape (pick i)⟩ : Tapes 3 0)) hc
  change (projectConfig c).tapes = _ at hp
  rw [hp]
  unfold CountedCopyReuse.bank bank
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-- Linear-time forward seek with a physically restored reusable clock. -/
theorem seek_hoare (payload : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
    HoareTime program (fun v => v = bank payload p bs)
      (fun v => v = bank payload (p+Counter.value bs) bs)
      (5*Counter.value bs+7*bs.length+16) := by
  rintro v rfl
  obtain ⟨c,hr,hh,hc⟩ := seek_exact payload p bs
  have hb := CountedCopyReuse.runtime_le_linear (segment payload p (Counter.value bs)) bs
    (segment_length payload p _).symm
  rw [segment_length] at hb
  exact ⟨_,c,hb,hr,hh,hc⟩

/-- Reflect only the payload head; the clock and descriptor keep their original
physical orientation. This changes actual transition directions, at no cost. -/
def backwardProgram : Program 3 16 0 := Reflection.program program (fun i => i = 0)

private theorem reflect_bank (payload : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
    Reflection.tapes (fun i : Fin 3 => i = 0) (bank payload p bs) =
      bank (fun j => payload (-j)) (-p) bs := by
  unfold Reflection.tapes bank
  congr 1
  · funext i; fin_cases i <;> simp [Reflection.coord]
  · funext i j; fin_cases i <;> simp [Reflection.coord]

/-- Backwards raw seek has exactly the same bound and cleanup contract. -/
theorem seek_backward_hoare (payload : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
    HoareTime backwardProgram (fun v => v = bank payload p bs)
      (fun v => v = bank payload (p-Counter.value bs) bs)
      (5*Counter.value bs+7*bs.length+16) := by
  have h := Reflection.hoare (seek_hoare (fun j => payload (-j)) (-p) bs)
    (fun i : Fin 3 => i = 0)
  apply h.consequence
  · intro v hv
    refine ⟨bank (fun j => payload (-j)) (-p) bs,rfl,?_⟩
    rw [reflect_bank]
    simpa only [neg_neg] using hv
  · rintro v ⟨original,rfl,hv⟩
    rw [reflect_bank] at hv
    simpa only [neg_neg,neg_add_rev,sub_eq_add_neg,add_comm] using hv
  · rfl

end IntegerMultBounds.Machine.CountedSeek
