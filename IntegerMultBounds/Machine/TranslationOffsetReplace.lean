import IntegerMultBounds.Machine.BinaryReplace
import IntegerMultBounds.Machine.TranslationPreparedFamily

/-! Physical installation of a supplied offset on translation's immutable-input
slot. A separate canonical binary source tape supplies the replacement; every
other translation tape and head is framed literally. -/

namespace IntegerMultBounds.Machine.TranslationOffsetReplace

open CountedCopyReuse (binary)

/-- A physical scheduler-output descriptor, sentinel at zero and head at one. -/
def supplied (next : List Bool) : Tapes 1 0 := ⟨fun _ => 1,fun _ => binary next⟩

def bank (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs old next : List Bool) : Tapes 13 0 :=
  (TranslationExecutionReuse.bank source dest p q bs qs old).append (supplied next)

/-- Offset slot eight, supplied descriptor slot twelve; all others are frames. -/
def placement : Fin (2+11) ≃ Fin 13 := (Equiv.swap 0 8).trans (Equiv.swap 1 12)

def program : Program 13 7 0 := Placement.placed BinaryReplace.program placement

private theorem active_bank (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs old next : List Bool) :
    Placement.active placement (bank source dest p q bs qs old next) = BinaryReplace.bank old next := by
  unfold Placement.active placement bank supplied TranslationExecutionReuse.bank
    TranslationPreparedExecution.bank TranslationDescriptors.bank BinaryReplace.bank
    CountedLoopReuse.controls Tapes.append
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem frame_bank (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs old next : List Bool) :
    Placement.extra placement (bank source dest p q bs qs old next) =
      Placement.extra placement (bank source dest p q bs qs next next) := by
  unfold Placement.extra placement bank supplied TranslationExecutionReuse.bank
    TranslationPreparedExecution.bank TranslationDescriptors.bank Tapes.append
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem replace_bank (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs old next : List Bool) :
    Placement.replace placement (bank source dest p q bs qs old next) (BinaryReplace.bank next next) =
      bank source dest p q bs qs next next := by
  rw [Placement.replace,frame_bank,← active_bank source dest p q bs qs next next]
  exact Placement.view _ _

/-- Replacing the actual offset descriptor preserves both payload tapes, all
clean synthesis workspace, Q/B descriptors, and the scheduler-output source. -/
theorem replace_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs old next : List Bool) :
    HoareTime program (fun v => v = bank source dest p q bs qs old next)
      (fun v => v = bank source dest p q bs qs next next)
      (2*old.length+2*next.length+8) := by
  have hh := Placement.hoare_at (BinaryReplace.replace_hoare old next) placement
    (bank source dest p q bs qs old next) (active_bank source dest p q bs qs old next)
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_bank source dest p q bs qs old next

/-- Arbitrary additional scheduler workspace survives complete descriptor replacement. -/
theorem replace_framed_hoare {s : ℕ} (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs old next : List Bool) (frame : Tapes s 0) :
    HoareTime (extend program s)
      (fun v => v = (bank source dest p q bs qs old next).append frame)
      (fun v => v = (bank source dest p q bs qs next next).append frame)
      (2*old.length+2*next.length+8) := by
  apply ((replace_hoare source dest p q bs qs old next).extend frame).consequence _ _ le_rfl
  · intro v hv; exact ⟨_,rfl,hv⟩
  · rintro v ⟨w,rfl,hv⟩; exact hv

private theorem regroup {s : ℕ} (v : Tapes 12 0) (w : Tapes 1 0) (frame : Tapes s 0) :
    ((v.append w).append frame).reindex (finCongr (Nat.add_assoc 12 1 s)) = v.append (w.append frame) := by
  unfold Tapes.reindex Tapes.append
  congr 1
  · funext i
    change Fin.append (Fin.append v.head w.head) frame.head _ = _
    rw [Fin.append_assoc]
    simp [Fin.append]
  · funext i
    change Fin.append (Fin.append v.tape w.tape) frame.tape _ = _
    rw [Fin.append_assoc]
    simp [Fin.append]

/-- Regroup the supplied descriptor with an arbitrary additional scheduler bank. -/
def framedProgram (s : ℕ) : Program (12+(1+s)) 7 0 :=
  reindex (extend program s) (finCongr (Nat.add_assoc 12 1 s))

theorem framed_hoare {s : ℕ} (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs old next : List Bool) (frame : Tapes s 0) :
    HoareTime (framedProgram s)
      (fun v => v = (TranslationExecutionReuse.bank source dest p q bs qs old).append ((supplied next).append frame))
      (fun v => v = (TranslationExecutionReuse.bank source dest p q bs qs next).append ((supplied next).append frame))
      (2*old.length+2*next.length+8) := by
  have hh := (replace_framed_hoare source dest p q bs qs old next frame).reindex (finCongr (Nat.add_assoc 12 1 s))
  apply hh.consequence _ _ le_rfl
  · intro v hv
    exact ⟨_,rfl,by simpa only [bank,regroup] using hv⟩
  · rintro v ⟨w,rfl,hv⟩
    simpa only [bank,regroup] using hv

/-- The scheduler bank stores its last physical output plus all other workspace. -/
def frame {s : ℕ} (as : ℕ → List Bool) (work : ℕ → Tapes s 0) (i : ℕ) : Tapes (1+s) 0 :=
  (supplied (as i)).append (work i)

/-- Exact post-state required of the scheduler: the new offset exists on its
output tape while the old translation offset still exists at slot eight. -/
def scheduled {s : ℕ} (offset : ℕ → ℕ) (Q B n : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs : List Bool) (as : ℕ → List Bool) (work : ℕ → Tapes s 0)
    (payload : ℕ → ℕ → List (Fin 4)) (i : ℕ) : Tapes (12+(1+s)) 0 :=
  (TranslationExecutionReuse.bank (putWord source p (TranslationStream.fibers Q n payload).flatten)
    (putWord dest q (TranslationPreparedFamily.outputPrefix offset Q i payload))
    (p+((i*(Q*B) : ℕ) : ℤ)) (q+((i*(Q*B) : ℕ) : ℤ)) bs qs (as i)).append (frame as work (i+1))

/-- An actual scheduler followed by the literal descriptor replacement. -/
def prepProgram {s m : ℕ} (scheduler : Program (12+(1+s)) m 0) : Program (12+(1+s)) (m+7) 0 :=
  seq scheduler (framedProgram s)

/-- Discharge the family preparation contract from a concrete scheduler that
writes a physical output tape, with every replacement scan charged. -/
theorem prep_hoare {s m Q B n i : ℕ} (scheduler : Program (12+(1+s)) m 0)
    (offset : ℕ → ℕ) (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs : List Bool)
    (as : ℕ → List Bool) (work : ℕ → Tapes s 0) (payload : ℕ → ℕ → List (Fin 4)) (cost : ℕ)
    (hscheduler : HoareTime scheduler
      (fun v => v = TranslationPreparedFamily.state offset Q B n source dest p q bs qs as (frame as work) payload i)
      (fun v => v = scheduled offset Q B n source dest p q bs qs as work payload i) cost) :
    HoareTime (prepProgram scheduler)
      (fun v => v = TranslationPreparedFamily.state offset Q B n source dest p q bs qs as (frame as work) payload i)
      (fun v => v = TranslationPreparedFamily.prepared offset Q B n source dest p q bs qs as (frame as work) payload i)
      (cost+1+(2*(as i).length+2*(as (i+1)).length+8)) := by
  exact hscheduler.seq (framed_hoare
    (putWord source p (TranslationStream.fibers Q n payload).flatten)
    (putWord dest q (TranslationPreparedFamily.outputPrefix offset Q i payload))
    (p+((i*(Q*B) : ℕ) : ℤ)) (q+((i*(Q*B) : ℕ) : ℤ)) bs qs (as i) (as (i+1)) (work (i+1)))

/-- Instantiation of the varying-offset family using a physical scheduler output.
The remaining premise is the actual scheduler's complete tape/time contract. -/
theorem family_hoare {s m Q B n : ℕ} (scheduler : Program (12+(1+s)) m 0)
    (offset : ℕ → ℕ) (hQ : 0 < Q) (ha : ∀ i < n, offset i ≤ Q) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool)
    (as : ℕ → List Bool) (work : ℕ → Tapes s 0)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (hn : Counter.value ns = n)
    (ha' : ∀ i < n, Counter.value (as (i+1)) = offset i)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) (ca : ∀ i < n, GrowingCounterData.Canonical (as (i+1)))
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B)
    (schedulerCost : ℕ → ℕ)
    (hscheduler : ∀ i < n, HoareTime scheduler
      (fun v => v = TranslationPreparedFamily.state offset Q B n source dest p q bs qs as (frame as work) payload i)
      (fun v => v = scheduled offset Q B n source dest p q bs qs as work payload i) (schedulerCost i)) :
    HoareTime (TranslationPreparedFamily.program (prepProgram scheduler))
      (fun v => v = CountedLoopReuse.bank
        (TranslationPreparedFamily.state offset Q B n source dest p q bs qs as (frame as work) payload 0)
        CountedCopyReuse.empty (binary ns) 1 1)
      (fun v => v = CountedLoopReuse.bank
        (TranslationPreparedFamily.state offset Q B n source dest p q bs qs as (frame as work) payload n)
        CountedCopyReuse.empty (binary ns) 1 1)
      ((∑ i ∈ Finset.range n, (schedulerCost i+1+(2*(as i).length+2*(as (i+1)).length+8)))+
        462*(TranslationStream.fibers Q n payload).flatten.length+23) := by
  exact TranslationPreparedFamily.family_hoare_linear (prepProgram scheduler) offset hQ ha hB source dest p q
    bs qs ns as (frame as work) hb hq hn ha' cb cq cn ca payload hwidth
    (fun i => schedulerCost i+1+(2*(as i).length+2*(as (i+1)).length+8))
    (fun i hi => prep_hoare scheduler offset source dest p q bs qs as work payload (schedulerCost i) (hscheduler i hi))

end IntegerMultBounds.Machine.TranslationOffsetReplace
