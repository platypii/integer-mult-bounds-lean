import IntegerMultBounds.Machine.RadixRationalBinary

/-! Replace a stale marked radix word from one physical shared source. The old
copy is actually erased, source digits copied, and both heads returned to one.
The shared source is preserved cell-for-cell; no supplied fresh copy is assumed. -/
namespace IntegerMultBounds.Machine.MarkedRadixRefresh

open RadixDigits
open MarkedWordCleanup (marked empty one)
variable {q : ℕ}

def source (xs : List (Fin q)) := marked (xs.map digitSymbol)
def bank (xs ys : List (Fin q)) : Tapes 2 q := Copy.tapes (source xs) (source ys) 1 1

private theorem nonblank (xs : List (Fin q)) : ∀ x ∈ xs.map digitSymbol, x ≠ (blank : Fin (q+4)) := by
  intro x hx
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
  simp [digitSymbol,blank,Fin.ext_iff]

private def rightProgram : Program 1 2 q where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols => if s = 0 then some (1,fun i => (symbols i,Move.right)) else none

private theorem right_hoare (f : ℤ → Fin (q+4)) (p : ℤ) :
    HoareTime rightProgram (fun v => v = one f p) (fun v => v = one f (p+1)) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,fun _ => p+1,fun _ => f⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,rightProgram,one,Tapes.start,ite_true,Move.offset]
    congr 1
    congr 1
    funext i z
    by_cases hz : z = p <;> simp [hz]
  · simp [step,rightProgram]

/-- Clear every stale digit and return to the retained sentinel. -/
def clearProgram : Program 1 4 q :=
  seq (seq MarkedWordCleanup.clearProgram (Rewind.program separator)) rightProgram

theorem clear_hoare (xs : List (Fin q)) :
    HoareTime clearProgram (fun v => v = one (source xs) 1) (fun v => v = one (source []) 1) (2*xs.length+4) := by
  have hc := MarkedWordCleanup.clear_hoare (xs.map digitSymbol) (nonblank xs)
  simp only [List.length_map] at hc
  have hr := Rewind.rewind_hoare (separator : Fin (q+4)) empty (xs.length+1) (xs.length+1)
    (by intro j hj; simp [empty,show (xs.length:ℤ)+1-j ≠ 0 by omega,blank,separator,Fin.ext_iff])
    (by simp [empty])
  have hr' : HoareTime (Rewind.program (separator : Fin (q+4)))
      (fun v => v = one empty (1+xs.length)) (fun v => v = one empty 0) (xs.length+1) := by
    simpa only [Rewind.cfg,Config.tapes,one,sub_self,Nat.cast_add,Nat.cast_one,add_comm] using hr
  exact ((hc.seq hr').seq (right_hoare empty 0)).consequence (fun _ h => h) (fun _ h => h) (by omega)

private def clearDestination : Program 2 4 q := Placement.placed (u := 1) clearProgram (Equiv.swap 0 1)

private theorem clear_destination (xs old : List (Fin q)) :
    HoareTime clearDestination (fun v => v = bank xs old) (fun v => v = bank xs []) (2*old.length+4) := by
  let wire : Fin (1+1) ≃ Fin 2 := Equiv.swap 0 1
  have ha : Placement.active wire (bank xs old) = one (source old) 1 := by
    unfold Placement.active wire bank Copy.tapes Copy.cfg Config.tapes one
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  have hf : Placement.active wire (bank xs []) = one (source []) 1 := by
    unfold Placement.active wire bank Copy.tapes Copy.cfg Config.tapes one
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  have he : Placement.extra wire (bank xs old) = Placement.extra wire (bank xs []) := by
    unfold Placement.extra wire bank Copy.tapes Copy.cfg Config.tapes
    congr 1
    funext i
    fin_cases i
    rfl
  apply (Placement.hoare_at (clear_hoare old) wire (bank xs old) ha).consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

private theorem copy_hoare (xs : List (Fin q)) :
    HoareTime (Copy.program blank false) (fun v => v = bank xs [])
      (fun v => v = Copy.tapes (source xs) (source xs) (1+xs.length) (1+xs.length)) xs.length := by
  have hh := Copy.copy_hoare (blank : Fin (q+4)) false empty empty 1 1 (xs.map digitSymbol) (nonblank xs)
    (by simp only [empty,List.length_map]; rw [ite_eq_right (by omega)])
  have hr : (Copy.retained false : Fin (q+4) → Fin (q+4)) = id := by funext x; rfl
  simpa only [hr,List.map_id,List.length_map,bank,source,marked,List.map_nil,putWord] using hh

private theorem marker (xs : List (Fin q)) : source xs 0 = separator := by
  rw [source,marked,putWord_outside _ _ _ _ (Or.inl (by omega))]
  rfl

private theorem no_marker (xs : List (Fin q)) (z : ℤ) (hz : 0 < z) : source xs z ≠ separator := by
  by_cases hi : z < 1+xs.length
  · have hm := ReturnOrigin.putWord_mem empty 1 (xs.map digitSymbol) z ⟨by omega,by simpa using hi⟩
    obtain ⟨y,_,hy⟩ := List.mem_map.mp hm
    change putWord empty 1 (xs.map digitSymbol) z ≠ separator
    rw [← hy]
    simp [digitSymbol,separator,Fin.ext_iff]
  · rw [source,marked,putWord_outside _ _ _ _ (Or.inr (by simpa using le_of_not_gt hi))]
    simp [empty,show z ≠ 0 by omega,blank,separator,Fin.ext_iff]

private def resetProgram : Program 2 2 q where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols => if s = 0 then
    if symbols 0 = separator then some (1,fun i => (symbols i,Move.right))
    else some (0,fun i => (symbols i,Move.left)) else none

private def resetCfg (xs : List (Fin q)) (p : ℤ) : Config 2 2 q :=
  ⟨0,(Copy.tapes (source xs) (source xs) p p).head,(Copy.tapes (source xs) (source xs) p p).tape⟩

private theorem reset_step (xs : List (Fin q)) (p : ℤ) (hp : 0 < p) :
    step resetProgram (resetCfg xs p) = some (resetCfg xs (p-1)) := by
  simp only [step,resetProgram,resetCfg,Copy.tapes,Copy.cfg,Config.tapes,ite_true,no_marker xs p hp,ite_false,Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i z; fin_cases i <;> by_cases hz : z = p <;> simp [hz]

private theorem reset_run (xs : List (Fin q)) (n : ℕ) :
    run resetProgram n (resetCfg xs n) = some (resetCfg xs 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run,Nat.cast_add,Nat.cast_one,reset_step xs (n+1) (by omega)]
    simpa using ih

private theorem reset_hoare (xs : List (Fin q)) :
    HoareTime resetProgram (fun v => v = Copy.tapes (source xs) (source xs) (1+xs.length) (1+xs.length))
      (fun v => v = bank xs xs) (xs.length+2) := by
  let last : Config 2 2 q := ⟨1,(bank xs xs).head,(bank xs xs).tape⟩
  have hs : step resetProgram (resetCfg xs 0) = some last := by
    simp only [step,resetProgram,resetCfg,Copy.tapes,Copy.cfg,Config.tapes,ite_true,marker,Move.offset]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z; fin_cases i <;> by_cases hz : z = 0 <;> simp [bank,Copy.tapes,Copy.cfg,Config.tapes,hz]
  have hr := reset_run xs (xs.length+1)
  rw [Nat.cast_add,Nat.cast_one] at hr
  rintro v rfl
  refine ⟨xs.length+2,last,le_rfl,?_,?_,rfl⟩
  · rw [show xs.length+2 = (xs.length+1)+1 by omega,run_add]
    have hstart : (Copy.tapes (source xs) (source xs) (1+xs.length) (1+xs.length)).start resetProgram =
        resetCfg xs (xs.length+1) := by simp [Tapes.start,resetCfg,resetProgram,add_comm]
    rw [hstart,hr]
    simp only [Option.bind_some,run_one,hs]
  · simp [last,step,resetProgram]

/-- Seven states, two tapes, no width in the transition table. -/
def program : Program 2 7 q := seq (seq clearDestination (Copy.program blank false)) resetProgram

theorem refresh_hoare (xs old : List (Fin q)) :
    HoareTime program (fun v => v = bank xs old) (fun v => v = bank xs xs)
      (2*old.length+2*xs.length+8) := by
  exact (((clear_destination xs old).seq (copy_hoare xs)).seq (reset_hoare xs)).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.MarkedRadixRefresh
