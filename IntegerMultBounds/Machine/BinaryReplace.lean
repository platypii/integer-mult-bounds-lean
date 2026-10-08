import IntegerMultBounds.Machine.CountedLoopReuse
import IntegerMultBounds.Machine.GrowingCounterData

/-! Physically replace a sentinel-marked binary descriptor from a second tape.
Erase the old word, copy the supplied replacement, and rewind both equal words.
The supplied replacement tape is preserved exactly, including its head. -/

namespace IntegerMultBounds.Machine.BinaryReplace

open CountedCopyReuse (empty binary)
open CountedLoopReuse (controls)

/-- Destination then immutable physical source, both heads at the first bit. -/
def bank (old next : List Bool) : Tapes 2 0 := controls (binary old) (binary next) 1 1

private theorem bits_word (f : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
    putBits f p bs = putWord f p (bs.map bitSymbol) := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih => simp only [putBits,putWord,List.map_cons,ih]

private theorem copy_controls (source dest : ℤ → Fin 4) (p r : ℤ) :
    (Copy.tapes source dest p r).reindex (Equiv.swap 0 1) = controls dest source r p := by
  unfold Copy.tapes Copy.cfg Config.tapes Tapes.reindex controls
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem copy_hoare (bs : List Bool) :
    HoareTime CountedLoopReuse.copyProgram
      (fun v => v = controls empty (binary bs) 1 1)
      (fun v => v = controls (binary bs) (binary bs) (1+bs.length) (1+bs.length)) bs.length := by
  have hbits : ∀ b ∈ bs.map bitSymbol, b ≠ (blank : Fin 4) := by
    intro b hb
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hb
    cases x <;> decide
  have hh := Copy.copy_hoare blank false empty empty 1 1 (bs.map bitSymbol) hbits
    (by simp [empty,show (1 : ℤ)+bs.length ≠ 0 by omega])
  have hret : (Copy.retained false : Fin 4 → Fin 4) = id := rfl
  simp only [hret,List.map_id,List.length_map,← bits_word] at hh
  have he := hh.reindex (Equiv.swap 0 (1 : Fin 2))
  apply he.consequence _ _ le_rfl
  · intro v hv
    exact ⟨_,rfl,by simpa only [copy_controls,binary] using hv⟩
  · rintro v ⟨w,rfl,hv⟩
    simpa only [copy_controls,binary] using hv

private theorem binary_marker (bs : List Bool) : binary bs 0 = separator := by
  rw [binary,putBits_outside _ _ _ _ (Or.inl (by omega))]
  rfl

private theorem binary_ne_marker (bs : List Bool) (j : ℤ) (hj : 0 < j) :
    binary bs j ≠ separator := by
  by_cases hh : j < 1+bs.length
  · exact putBits_ne_separator empty 1 j bs (by omega) hh
  · rw [binary,putBits_outside _ _ _ _ (Or.inr (by omega))]
    simp [empty,ne_of_gt hj,blank,separator]

/-- The copied words are identical, so both heads rewind simultaneously. -/
def rewindProgram : Program 2 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols => if s = 0 then
    if symbols 0 = separator then some (1,fun i => (symbols i,Move.right))
    else some (0,fun i => (symbols i,Move.left)) else none

private def cfg (bs : List Bool) (p : ℤ) (s : Fin 2) : Config 2 2 0 :=
  ⟨s,fun _ => p,fun _ => binary bs⟩

private theorem rewind_step (bs : List Bool) (p : ℤ) (hp : 0 < p) :
    step rewindProgram (cfg bs p 0) = some (cfg bs (p-1) 0) := by
  simp only [step,rewindProgram,cfg,ite_true,binary_ne_marker bs p hp,ite_false,Move.offset]
  congr 1
  congr 1
  funext i z
  by_cases hz : z = p <;> simp [hz]

private theorem rewind_run (bs : List Bool) (n : ℕ) :
    run rewindProgram n (cfg bs n 0) = some (cfg bs 0 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run,Nat.cast_add,Nat.cast_one,rewind_step bs (n+1) (by omega)]
    simpa using ih

private theorem rewind_hoare (bs : List Bool) :
    HoareTime rewindProgram
      (fun v => v = controls (binary bs) (binary bs) (1+bs.length) (1+bs.length))
      (fun v => v = bank bs bs) (bs.length+2) := by
  have hs : step rewindProgram (cfg bs 0 0) = some (cfg bs 1 1) := by
    simp only [step,rewindProgram,cfg,ite_true,binary_marker,Move.offset,zero_add]
    congr 1
    congr 1
    funext i z
    by_cases hz : z = 0 <;> simp [hz,binary_marker]
  have hr : run rewindProgram (bs.length+2) (cfg bs (bs.length+1) 0) = some (cfg bs 1 1) := by
    have h := rewind_run bs (bs.length+1)
    rw [Nat.cast_add,Nat.cast_one] at h
    rw [show bs.length+2 = (bs.length+1)+1 by omega,run_add,h]
    simp only [Option.bind_some,run_one,hs]
  intro v hv
  subst v
  refine ⟨bs.length+2,cfg bs 1 1,le_rfl,?_,?_,?_⟩
  · convert hr using 1; simp [Tapes.start,controls,cfg,rewindProgram,add_comm]
  · simp [step,rewindProgram,cfg]
  · simp [Config.tapes,cfg,bank,controls]

/-- Seven fixed control states, independent of either descriptor's width. -/
def program : Program 2 7 0 :=
  seq CountedLoopReuse.cleanControls (seq CountedLoopReuse.copyProgram rewindProgram)

/-- Whole-bank restoration, including removal of any stale longer suffix. -/
theorem replace_hoare (old next : List Bool) :
    HoareTime program (fun v => v = bank old next) (fun v => v = bank next next)
      (2*old.length+2*next.length+8) := by
  have hc := CountedLoopReuse.clean_controls_hoare old next
  have hp := (copy_hoare next).seq (rewind_hoare next)
  exact (hc.seq hp).consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- Numeric correctness follows from the literal copied descriptor. -/
theorem replace_value (old next : List Bool) (a : ℕ) (ha : Counter.value next = a)
    (hcanonical : GrowingCounterData.Canonical next) :
    HoareTime program (fun v => v = bank old next)
      (fun v => v = bank next next ∧ Counter.value next = a ∧ GrowingCounterData.Canonical next)
      (2*old.length+2*next.length+8) :=
  (replace_hoare old next).consequence (fun _ h => h) (fun _ h => ⟨h,ha,hcanonical⟩) le_rfl

end IntegerMultBounds.Machine.BinaryReplace
