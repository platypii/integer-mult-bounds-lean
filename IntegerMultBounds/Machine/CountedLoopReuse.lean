import IntegerMultBounds.Machine.CountedLoop
import IntegerMultBounds.Machine.CountedCopyReuse
import IntegerMultBounds.Machine.Placement

/-! Reusable outer countdown loops. The immutable descriptor is physically
copied to a clean mutable clock, both control heads are reset, and the actual
counted body loop runs. Cleanup erases the exhausted clock and resets its head.
All descriptor preparation, joins, head movements, and cleanup are charged. -/

namespace IntegerMultBounds.Machine.CountedLoopReuse

open CountedCopyReuse (empty binary rightProgram resetProgram clearProgram)
open Placement (ExactRun exact_seq)
variable {t q : ℕ}

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

def controls (clock descriptor : ℤ → Fin 4) (r s : ℤ) : Tapes 2 0 :=
  ⟨fun i => if i = 0 then r else s,fun i => if i = 0 then clock else descriptor⟩

private def atControl {k : ℕ} (M : Program 1 k 0) (i : Fin 2) : Program 2 k 0 :=
  Placement.placed (u := 1) M (Equiv.swap 0 i)

private theorem active_clock (clock descriptor : ℤ → Fin 4) (r s : ℤ) :
    Placement.active (s := 1) (u := 1) (Equiv.swap 0 (0 : Fin 2)) (controls clock descriptor r s) = one clock r := by
  unfold Placement.active controls one
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem active_descriptor (clock descriptor : ℤ → Fin 4) (r s : ℤ) :
    Placement.active (s := 1) (u := 1) (Equiv.swap 0 (1 : Fin 2)) (controls clock descriptor r s) = one descriptor s := by
  unfold Placement.active controls one
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem replace_clock (clock descriptor newClock : ℤ → Fin 4) (r s r' : ℤ) :
    Placement.replace (u := 1) (Equiv.swap 0 (0 : Fin 2)) (controls clock descriptor r s) (one newClock r') =
      controls newClock descriptor r' s := by
  unfold Placement.replace Placement.combine Placement.extra controls one Tapes.reindex Tapes.append
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem replace_descriptor (clock descriptor newDescriptor : ℤ → Fin 4) (r s s' : ℤ) :
    Placement.replace (u := 1) (Equiv.swap 0 (1 : Fin 2)) (controls clock descriptor r s) (one newDescriptor s') =
      controls clock newDescriptor r s' := by
  unfold Placement.replace Placement.combine Placement.extra controls one Tapes.reindex Tapes.append
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem reset_clock (cs ds : List Bool) (s : ℤ) (n : ℕ) :
    ExactRun (atControl resetProgram 0) (n+2)
      (controls (binary cs) (binary ds) n s) (controls (binary cs) (binary ds) 1 s) := by
  have h := reset_exact cs n
  rw [← active_clock (binary cs) (binary ds) n s] at h
  simpa only [atControl,replace_clock] using
    Placement.placed_exact (u := 1) resetProgram (Equiv.swap 0 (0 : Fin 2)) _ _ h

private theorem reset_descriptor (cs ds : List Bool) (r : ℤ) (n : ℕ) :
    ExactRun (atControl resetProgram 1) (n+2)
      (controls (binary cs) (binary ds) r n) (controls (binary cs) (binary ds) r 1) := by
  have h := reset_exact ds n
  rw [← active_descriptor (binary cs) (binary ds) r n] at h
  simpa only [atControl,replace_descriptor] using
    Placement.placed_exact (u := 1) resetProgram (Equiv.swap 0 (1 : Fin 2)) _ _ h

private theorem clear_clock (cs ds : List Bool) :
    ExactRun (atControl clearProgram 0) cs.length
      (controls (binary cs) (binary ds) 1 1) (controls empty (binary ds) (1+cs.length) 1) := by
  have h := clear_exact cs
  rw [← active_clock (binary cs) (binary ds) 1 1] at h
  simpa only [atControl,replace_clock] using
    Placement.placed_exact (u := 1) clearProgram (Equiv.swap 0 (0 : Fin 2)) _ _ h

def copyProgram : Program 2 1 0 := reindex (Copy.program blank false) (Equiv.swap 0 1)

private theorem copy_controls (source dest : ℤ → Fin 4) (p r : ℤ) :
    (Copy.tapes source dest p r).reindex (Equiv.swap 0 1) = controls dest source r p := by
  unfold Copy.tapes Copy.cfg Config.tapes Tapes.reindex controls
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem copy_exact (bs : List Bool) :
    ExactRun copyProgram bs.length (controls empty (binary bs) 1 1)
      (controls (binary bs) (binary bs) (1+bs.length) (1+bs.length)) := by
  have hbits : ∀ b ∈ bs.map bitSymbol, b ≠ (blank : Fin 4) := by
    intro b hb
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hb
    cases x <;> decide
  obtain ⟨hr,hh⟩ := Copy.copy_exact blank false empty empty 1 1 (bs.map bitSymbol) hbits
    (by simp [empty,show (1 : ℤ)+bs.length ≠ 0 by omega])
  have hret : (Copy.retained false : Fin 4 → Fin 4) = id := rfl
  simp only [hret,List.map_id,List.length_map,← bits_word] at hr hh
  have hs := reindex_run (Copy.program blank false) (Equiv.swap 0 (1 : Fin 2)) hr
  have ht := reindex_halt (Copy.program blank false) (Equiv.swap 0 (1 : Fin 2)) hh
  have hb : (Copy.cfg (binary bs) empty 1 1).reindex (Equiv.swap 0 (1 : Fin 2)) =
      (controls empty (binary bs) 1 1).start copyProgram := by
    have hv := copy_controls (binary bs) empty 1 1
    unfold Config.reindex Tapes.start
    congr 1
    · exact congrArg Tapes.head hv
    · exact congrArg Tapes.tape hv
  change run copyProgram bs.length ((Copy.cfg (binary bs) empty 1 1).reindex (Equiv.swap 0 (1 : Fin 2))) = _ at hs
  rw [hb] at hs
  exact ⟨_,hs,ht,copy_controls _ _ _ _⟩

/-- Descriptor-to-clock copy followed by both physical head resets. -/
def prepareControls : Program 2 7 0 := seq (seq copyProgram (atControl resetProgram 1)) (atControl resetProgram 0)

private theorem prepare_exact (bs : List Bool) :
    ExactRun prepareControls (3*bs.length+8) (controls empty (binary bs) 1 1)
      (controls (binary bs) (binary bs) 1 1) := by
  have hd := reset_descriptor bs bs (1+bs.length) (bs.length+1)
  have hc := reset_clock bs bs 1 (bs.length+1)
  have hcast : ((bs.length+1 : ℕ) : ℤ) = 1+bs.length := by omega
  rw [hcast] at hd hc
  have hh := exact_seq (exact_seq (copy_exact bs) hd) hc
  simpa only [prepareControls,show bs.length+1+(bs.length+1+2)+1+(bs.length+1+2) =
    3*bs.length+8 by omega] using hh

/-- Erase the spent clock and restore its head, retaining its sentinel. -/
def cleanControls : Program 2 4 0 := seq (atControl clearProgram 0) (atControl resetProgram 0)

private theorem clean_exact (cs ds : List Bool) :
    ExactRun cleanControls (2*cs.length+4) (controls (binary cs) (binary ds) 1 1)
      (controls empty (binary ds) 1 1) := by
  have hr := reset_clock [] ds 1 (cs.length+1)
  simp only [binary,putBits] at hr
  have hcast : ((cs.length+1 : ℕ) : ℤ) = 1+cs.length := by omega
  rw [hcast] at hr
  have hh := exact_seq (clear_clock cs ds) hr
  simpa only [cleanControls,binary,show cs.length+1+(cs.length+1+2) = 2*cs.length+4 by omega] using hh

/-- Erase any finite binary metadata word and physically reset its head, while
preserving a second immutable descriptor. This contract includes both scans
and the sequential join, and allows padded/noncanonical metadata. -/
theorem clean_controls_hoare (cs ds : List Bool) :
    HoareTime cleanControls (fun v => v = controls (binary cs) (binary ds) 1 1)
      (fun v => v = controls empty (binary ds) 1 1) (2*cs.length+4) := by
  rintro v rfl
  obtain ⟨last,hr,hh,hf⟩ := clean_exact cs ds
  exact ⟨2*cs.length+4,last,le_rfl,hr,hh,hf⟩

/-- Body tapes come first; the dedicated clock and immutable descriptor follow. -/
def bank (v : Tapes t 0) (clock descriptor : ℤ → Fin 4) (r s : ℤ) : Tapes (t+2) 0 :=
  v.append (controls clock descriptor r s)

def controlsProgram {k : ℕ} (M : Program 2 k 0) (t : ℕ) : Program (t+2) k 0 :=
  Placement.placed M (finAddFlip : Fin (2+t) ≃ Fin (t+2))

private theorem active_controls (v : Tapes t 0) (w : Tapes 2 0) :
    Placement.active (finAddFlip : Fin (2+t) ≃ Fin (t+2)) (v.append w) = w := by
  cases w
  simp [Placement.active,Tapes.append,finAddFlip_apply_castAdd]

private theorem extra_controls (v : Tapes t 0) (w : Tapes 2 0) :
    Placement.extra (finAddFlip : Fin (2+t) ≃ Fin (t+2)) (v.append w) = v := by
  cases v
  simp [Placement.extra,Tapes.append,finAddFlip_apply_natAdd]

private theorem combine_controls (v : Tapes t 0) (w : Tapes 2 0) :
    Placement.combine (finAddFlip : Fin (2+t) ≃ Fin (t+2)) w v = v.append w := by
  have hv := Placement.view (finAddFlip : Fin (2+t) ≃ Fin (t+2)) (v.append w)
  simpa only [active_controls,extra_controls] using hv

private theorem replace_controls (v : Tapes t 0) (w w' : Tapes 2 0) :
    Placement.replace (finAddFlip : Fin (2+t) ≃ Fin (t+2)) (v.append w) w' = v.append w' := by
  rw [Placement.replace,extra_controls,combine_controls]

private theorem controls_exact {k n : ℕ} (M : Program 2 k 0) (v : Tapes t 0) (w w' : Tapes 2 0)
    (h : ExactRun M n w w') : ExactRun (controlsProgram M t) n (v.append w) (v.append w') := by
  rw [← active_controls v w] at h
  simpa only [controlsProgram,replace_controls] using
    Placement.placed_exact M (finAddFlip : Fin (2+t) ≃ Fin (t+2)) (v.append w) w' h

private theorem loop_bank (v : Tapes t 0) (cs ds : List Bool) :
    (CountedLoop.bank v empty cs).append (one (binary ds) 1) = bank v (binary cs) (binary ds) 1 1 := by
  have hl (i : Fin t) : Fin.castAdd 1 (Fin.castAdd 1 i) = Fin.castAdd 2 i := Fin.ext rfl
  have hc : Fin.castAdd 1 (Fin.natAdd t (0 : Fin 1)) = Fin.natAdd t (0 : Fin 2) := Fin.ext rfl
  have hd : Fin.natAdd (t+1) (0 : Fin 1) = Fin.natAdd t (1 : Fin 2) := Fin.ext (by simp)
  unfold CountedLoop.bank bank controls one Tapes.append binary
  congr 1
  · funext i
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i => simp only [Fin.addCases_left]; simp [hl]
      | right i => fin_cases i; simp only [Fin.addCases_left,Fin.addCases_right]; simp [hc]
    | right i => fin_cases i; simp only [Fin.addCases_right]; simp [hd]
  · funext i
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i => simp only [Fin.addCases_left]; simp [hl]
      | right i => fin_cases i; simp only [Fin.addCases_left,Fin.addCases_right]; simp [hc]
    | right i => fin_cases i; simp only [Fin.addCases_right]; simp [hd]

/-- The fixed outer program prepares, runs, and cleans its private counter. -/
def program (M : Program t q 0) : Program (t+2) (7+(q+5)+4) 0 :=
  seq (seq (controlsProgram prepareControls t) (extend (CountedLoop.program M) 1))
    (controlsProgram cleanControls t)

/-- Actual body-chain execution with all preparation, countdown, joining, and
cleanup costs. The immutable descriptor survives unchanged and both control
heads return to one; the mutable clock is blank again apart from its sentinel. -/
theorem loop_exact (M : Program t q 0) (bs : List Bool) (n : ℕ)
    (v : ℕ → Tapes t 0) (cost : ℕ → ℕ) (hcount : Counter.value bs = n)
    (hbody : ∀ i < n, HoareTime M (fun w => w = v i) (fun w => w = v (i+1)) (cost i)) :
    ∃ k c, k ≤ (∑ i ∈ Finset.range n, cost i)+6*n+7*bs.length+16 ∧
      run (program M) k ((bank (v 0) empty (binary bs) 1 1).start (program M)) = some c ∧
      step (program M) c = none ∧ c.tapes = bank (v n) empty (binary bs) 1 1 := by
  obtain ⟨k,c,hk,hr,hh,hc⟩ := CountedLoop.loop_exact M empty bs n v cost hcount rfl
    (by simp [empty,show (1 : ℤ)+bs.length ≠ 0 by omega]) hbody
  have hs := extend_run (CountedLoop.program M) (one (binary bs) 1) hr
  have ht := extend_halt (CountedLoop.program M) (one (binary bs) 1) hh
  have hb : ((CountedLoop.bank (v 0) empty bs).start (CountedLoop.program M)).extend (one (binary bs) 1) =
      (bank (v 0) (binary bs) (binary bs) 1 1).start (extend (CountedLoop.program M) 1) := by
    have hv := loop_bank (v 0) bs bs
    unfold Config.extend Tapes.start
    congr 1
    · exact congrArg Tapes.head hv
    · exact congrArg Tapes.tape hv
  rw [hb] at hs
  have hloop : ExactRun (extend (CountedLoop.program M) 1) k
      (bank (v 0) (binary bs) (binary bs) 1 1)
      (bank (v n) (binary (List.replicate bs.length true)) (binary bs) 1 1) := by
    refine ⟨_,hs,ht,?_⟩
    change c.tapes.append (one (binary bs) 1) = _
    rw [hc,loop_bank]
  have hp := controls_exact prepareControls (v 0) _ _ (prepare_exact bs)
  have he := controls_exact cleanControls (v n) _ _ (clean_exact (List.replicate bs.length true) bs)
  simp only [List.length_replicate] at he
  have hall := exact_seq (exact_seq hp hloop) he
  obtain ⟨last,hlast,hhalt,hfinal⟩ := hall
  exact ⟨3*bs.length+8+1+k+1+(2*bs.length+4),last,by omega,hlast,hhalt,hfinal⟩

theorem loop_hoare (M : Program t q 0) (bs : List Bool) (n : ℕ)
    (v : ℕ → Tapes t 0) (cost : ℕ → ℕ) (hcount : Counter.value bs = n)
    (hbody : ∀ i < n, HoareTime M (fun w => w = v i) (fun w => w = v (i+1)) (cost i)) :
    HoareTime (program M) (fun w => w = bank (v 0) empty (binary bs) 1 1)
      (fun w => w = bank (v n) empty (binary bs) 1 1)
      ((∑ i ∈ Finset.range n, cost i)+6*n+7*bs.length+16) := by
  rintro w rfl
  exact loop_exact M bs n v cost hcount hbody

end IntegerMultBounds.Machine.CountedLoopReuse
