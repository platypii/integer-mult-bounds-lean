import IntegerMultBounds.Machine.ActivePrefixDirtyControlLoadHeaders

/-! Actual four-mode offset production, original-row repetition and full-array
rotation. Every mode shares fifty-one clean private tapes. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlLoadRun
noncomputable section
open ActivePrefixDirtyControlLoadData
open ActivePrefixDirtyControlLoadHeaders (bank pad15)
open ActivePrefixDirtyControlLoadProducer (Mode Shape values width word)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ} {m : Mode}

theorem pad4 (v : Tapes 14 a) :
    (CleanSubbank.bank (s := 4) v).append (SharedBank.empty 47 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem pad12 (v : Tapes 14 a) :
    (PackedOffsetPayloadPlaced.input v).append (SharedBank.empty 39 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def produce (m : Mode) := ActivePrefixDirtyControlLoadProducer.program (a := a) m producerFocus (by decide)
def repeatProgram := extend (ActivePrefixOffsetRepeatPlaced.program (a := a) repeatFocus (by decide)) 47
def rotate := extend (PackedOffsetPayloadPlaced.program a rotateFocus (by decide)) 39
def program (m : Mode) := seq (seq (seq (produce (a := a) m) (ActivePrefixDirtyControlLoadHeaders.program m))
    repeatProgram) rotate
def cost (s : Shape m) (rows B : ℕ) :=
  ActivePrefixDirtyControlLoadProducer.constant*ActivePrefixDirtyControl.volume s+
  ActivePrefixDirtyControlLoadHeaders.cost s rows+
  54*(rows*(word s).length+1)+ActiveTargetRotation.constant*volume s rows B+3

theorem produce_runs (s : Shape m) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (produce (a := a) m) (fun v => v=bank (base s rows B hs rs bs x))
      (fun v => v=bank (produced (base s rows B hs rs bs x) s))
      (ActivePrefixDirtyControlLoadProducer.constant*ActivePrefixDirtyControl.volume s) :=
  ActivePrefixDirtyControlLoadProducer.produces m _ _ (by decide) s hs
    (producer_sources s rows B hs rs bs x) hv hc

theorem repeat_runs (s : Shape m) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs) :
    HoareTime (repeatProgram (a := a)) (fun v => v=bank (dimensions (base s rows B hs rs bs x) s rows))
      (fun v => v=bank (repeated (base s rows B hs rs bs x) s rows))
      (54*(rows*(word s).length+1)) := by
  have h := ActivePrefixOffsetRepeatPlaced.repeats (dimensions (base (a := a) s rows B hs rs bs x) s rows)
    repeatFocus (by decide) (word s) rs rows (repeat_sources s rows B hs rs bs x) hr cr
  simpa only [repeatProgram,pad4,repeated] using hoare_extend_eq h (SharedBank.empty 47 a)

theorem rotate_runs (s : Shape m) (rows B : ℕ) (hrows : 0<rows) (hB : 0<B)
    (hs : Fin 6 → List Bool) (rs bs : List Bool) (x : Array s rows B)
    (hb : Counter.value bs=B) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (rotate (a := a)) (fun v => v=bank (repeated (base s rows B hs rs bs x) s rows))
      (fun v => v=bank (rotated (base s rows B hs rs bs x) s rows B x))
      (ActiveTargetRotation.constant*volume s rows B) := by
  have h := ActiveTargetRotation.runs (repeated (base (a := a) s rows B hs rs bs x) s rows)
    rotateFocus (by decide) (offsets s rows) (width s) (prefixCount s rows) B (offsets_length s rows)
    (by unfold prefixCount; positivity) hB bs (bits (prefixCount s rows)) (bits (width s)) hb
    (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_value _) cb
    (RecursiveChildQuotientsConstant.bits_canonical _) (RecursiveChildQuotientsConstant.bits_canonical _) x
    (rotation_tapes s rows B hs rs bs x) (rotation_heads s rows B hs rs bs x)
  simpa only [rotate,pad12,rotated,volume] using hoare_extend_eq h (SharedBank.empty 39 a)

theorem runs (s : Shape m) (rows B : ℕ) (hrows : 0<rows) (hB : 0<B)
    (hs : Fin 6 → List Bool) (rs bs : List Bool) (x : Array s rows B)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs)
    (hb : Counter.value bs=B) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (program (a := a) m) (fun v => v=bank (base s rows B hs rs bs x))
      (fun v => v=bank (rotated (base s rows B hs rs bs x) s rows B x)) (cost s rows B) := by
  exact (((produce_runs s rows B hs rs bs x hv hc).seq
    (ActivePrefixDirtyControlLoadHeaders.runs s rows B hs rs bs x hv hc hr cr)).seq
    (repeat_runs s rows B hs rs bs x hr cr)).seq
    (rotate_runs s rows B hrows hB hs rs bs x hb cb) |>.consequence (fun _ h => h) (fun _ h => h)
      (by unfold cost; omega)

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlLoadRun
