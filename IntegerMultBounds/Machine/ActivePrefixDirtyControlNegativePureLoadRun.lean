import IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativePureLoadData

/-! Actual four-mode offset production, original-row repetition and full-array
rotation. Every mode shares fifty-one clean private tapes. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativePureLoadRun
noncomputable section
open ActivePrefixDirtyControlLoadData (Array base volume prefixCount dimensions)
open ActivePrefixDirtyControlNegativePureLoadData
open ActivePrefixDirtyControlNegativePureData (negative)
open ActivePrefixDirtyControlLoadHeaders (bank pad15)
open ActivePrefixDirtyControlLoadProducer (values width)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

theorem pad4 (v : Tapes 14 a) :
    (CleanSubbank.bank (s := 4) v).append (SharedBank.empty 47 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem pad12 (v : Tapes 14 a) :
    (PackedOffsetPayloadPlaced.input v).append (SharedBank.empty 39 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def negate := extend (ActivePrefixParityNegativeNegate.program (a := a) negateFocus (by decide)) 10
def repeatProgram := extend (ActivePrefixOffsetRepeatPlaced.program (a := a) repeatFocus (by decide)) 47
def rotate := extend (PackedOffsetPayloadPlaced.program a rotateFocus (by decide)) 39
def program := seq (seq (seq (seq (ActivePrefixDirtyControlLoadRun.produce (a := a) .pure)
  (ActivePrefixDirtyControlLoadHeaders.program .pure)) negate) repeatProgram) rotate

def cost (s : Shape) (rows B : ℕ) := ActivePrefixDirtyControlLoadProducer.constant*ActivePrefixDirtyControl.volume s+
  ActivePrefixDirtyControlLoadHeaders.cost s rows+120*(2^s.W*(width s+1))+
  54*(rows*(negative s).length+1)+ActiveTargetRotation.constant*volume s rows B+4

theorem pad41 (v : Tapes 14 a) :
    (CleanSubbank.bank (s := 41) v).append (SharedBank.empty 10 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem negate_runs (s : Shape) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) :
    HoareTime (negate (a := a)) (fun v => v=bank (dimensions (base s rows B hs rs bs x) s rows))
      (fun v => v=bank (negated (base s rows B hs rs bs x) s rows)) (120*(2^s.W*(width s+1))) := by
  have h := ActivePrefixParityNegativeNegate.runs (dimensions (base (a := a) s rows B hs rs bs x) s rows)
    negateFocus (by decide) (ActivePrefixDirtyControlNegativePureData.rows s) (width s)
    (ActivePrefixDirtyControlNegativePureData.rows_uniform s) (bits (width s)) (bits (2^s.W))
    (RecursiveChildQuotientsConstant.bits_value _)
    (by rw [RecursiveChildQuotientsConstant.bits_value,ActivePrefixDirtyControlNegativePureData.rows_length s])
    (negate_sources s rows B hs rs bs x)
  have ht := BinaryParityXorOffsetNegate.cost_linear (width s) (2^s.W) (bits (width s)) (bits (2^s.W))
    (by positivity) (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_canonical _) (RecursiveChildQuotientsConstant.bits_canonical _)
  rw [ActivePrefixDirtyControlNegativePureData.rows_length s] at h
  have he := hoare_extend_eq (h.consequence (fun _ h => h) (fun _ h => h) ht) (SharedBank.empty 10 a)
  simpa only [negate,pad41,negated,ActivePrefixDirtyControlNegativePureData.negative] using he

theorem repeat_runs (s : Shape) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs) :
    HoareTime (repeatProgram (a := a)) (fun v => v=bank (negated (base s rows B hs rs bs x) s rows))
      (fun v => v=bank (repeated (base s rows B hs rs bs x) s rows))
      (54*(rows*(negative s).length+1)) := by
  have h := ActivePrefixOffsetRepeatPlaced.repeats (negated (base (a := a) s rows B hs rs bs x) s rows)
    repeatFocus (by decide) (negative s) rs rows (repeat_sources s rows B hs rs bs x) hr cr
  simpa only [repeatProgram,pad4,repeated] using hoare_extend_eq h (SharedBank.empty 47 a)

theorem rotate_runs (s : Shape) (rows B : ℕ) (hrows : 0<rows) (hB : 0<B)
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

theorem runs (s : Shape) (rows B : ℕ) (hrows : 0<rows) (hB : 0<B)
    (hs : Fin 6 → List Bool) (rs bs : List Bool) (x : Array s rows B)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs)
    (hb : Counter.value bs=B) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (program (a := a)) (fun v => v=bank (base s rows B hs rs bs x))
      (fun v => v=bank (rotated (base s rows B hs rs bs x) s rows B x)) (cost s rows B) := by
  exact ((((ActivePrefixDirtyControlLoadRun.produce_runs s rows B hs rs bs x hv hc).seq
    (ActivePrefixDirtyControlLoadHeaders.runs s rows B hs rs bs x hv hc hr cr)).seq
    (negate_runs s rows B hs rs bs x)).seq (repeat_runs s rows B hs rs bs x hr cr)).seq
    (rotate_runs s rows B hrows hB hs rs bs x hb cb) |>.consequence (fun _ h => h) (fun _ h => h)
      (by unfold cost; omega)

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativePureLoadRun
