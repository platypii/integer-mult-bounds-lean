import IntegerMultBounds.Machine.ActivePrefixCorrectionLoadHeaders

/-! Actual original-input correction offset production, original-row repetition
and containing-target rotation, without supplied derived descriptors or tables.
All stages reuse the same fixed blank fifty-seven-tape workspace. -/
namespace IntegerMultBounds.Machine.ActivePrefixCorrectionLoadRun
noncomputable section
open ActivePrefixCorrectionLoadData
open ActivePrefixCorrectionLoadHeaders (bank pad15)
open ActivePrefixSelectedOffsetBank (Shape values)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

theorem pad4 (v : Tapes 19 a) :
    (CleanSubbank.bank (s := 4) v).append (SharedBank.empty 53 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem pad12 (v : Tapes 19 a) :
    (PackedOffsetPayloadPlaced.input v).append (SharedBank.empty 45 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def produce := ActivePrefixCorrectionOffsetPlaced.program (a := a) producerFocus producer_injective
def repeatProgram := extend (ActivePrefixOffsetRepeatPlaced.program (a := a) repeatFocus repeat_injective) 53
def rotate := extend (PackedOffsetPayloadPlaced.program a rotateFocus rotate_injective) 45
def program := seq (seq (seq (seq (produce (a := a)) (ActivePrefixCorrectionLoadHeaders.setup (a := a)))
    (ActivePrefixCorrectionLoadHeaders.product (a := a))) (repeatProgram (a := a))) (rotate (a := a))
def cost (s : Shape) (rows B : ℕ) :=
  ActivePrefixCorrectionOffset.constant*(2^s.W*(s.W+1))+
  ActivePrefixCorrectionLoadHeaders.cost s rows+
  54*(rows*(offsetWord s).length+1)+ActiveTargetRotation.constant*volume s rows B+3

theorem produce_runs (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (produce (a := a)) (fun v => v=bank (base s rows B hs rs bs x))
      (fun v => v=bank (produced (base s rows B hs rs bs x) s))
      (ActivePrefixCorrectionOffset.constant*(2^s.W*(s.W+1))) :=
  ActivePrefixCorrectionOffsetPlaced.produces _ _ producer_injective s hs
    (producer_sources s rows B hs rs bs x) hv hc

theorem repeat_runs (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs) :
    HoareTime (repeatProgram (a := a)) (fun v => v=bank (dimensions (base s rows B hs rs bs x) s rows))
      (fun v => v=bank (repeated (base s rows B hs rs bs x) s rows))
      (54*(rows*(offsetWord s).length+1)) := by
  have h := ActivePrefixOffsetRepeatPlaced.repeats (dimensions (base (a := a) s rows B hs rs bs x) s rows)
    repeatFocus repeat_injective (offsetWord s) rs rows (repeat_sources s rows B hs rs bs x) hr cr
  simpa only [repeatProgram,pad4,repeated] using hoare_extend_eq h (SharedBank.empty 53 a)

theorem rotate_runs (s : Shape) (rows B : ℕ) (hrows : 0<rows) (hB : 0<B)
    (hs : Fin 8 → List Bool) (rs bs : List Bool) (x : Array s rows B)
    (hb : Counter.value bs=B) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (rotate (a := a)) (fun v => v=bank (repeated (base s rows B hs rs bs x) s rows))
      (fun v => v=bank (rotated (base s rows B hs rs bs x) s rows B x))
      (ActiveTargetRotation.constant*volume s rows B) := by
  have h := ActiveTargetRotation.runs (repeated (base (a := a) s rows B hs rs bs x) s rows)
    rotateFocus rotate_injective (offsets s rows) (width s) (prefixCount s rows) B (offsets_length s rows)
    (by unfold prefixCount; positivity) hB bs (bits (prefixCount s rows)) (bits (width s)) hb
    (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_value _) cb
    (RecursiveChildQuotientsConstant.bits_canonical _) (RecursiveChildQuotientsConstant.bits_canonical _) x
    (rotation_tapes s rows B hs rs bs x) (rotation_heads s rows B hs rs bs x)
  simpa only [rotate,pad12,rotated,volume] using hoare_extend_eq h (SharedBank.empty 45 a)

theorem runs (s : Shape) (rows B : ℕ) (hrows : 0<rows) (hB : 0<B)
    (hs : Fin 8 → List Bool) (rs bs : List Bool) (x : Array s rows B)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs)
    (hb : Counter.value bs=B) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (program (a := a)) (fun v => v=bank (base s rows B hs rs bs x))
      (fun v => v=bank (rotated (base s rows B hs rs bs x) s rows B x)) (cost s rows B) := by
  exact ((((produce_runs s rows B hs rs bs x hv hc).seq
    (ActivePrefixCorrectionLoadHeaders.setup_runs s rows B hs rs bs x hv hc)).seq
    (ActivePrefixCorrectionLoadHeaders.product_runs s rows B hs rs bs x hr cr)).seq
    (repeat_runs s rows B hs rs bs x hr cr)).seq
    (rotate_runs s rows B hrows hB hs rs bs x hb cb) |>.consequence (fun _ h => h) (fun _ h => h)
      (by unfold cost ActivePrefixCorrectionLoadHeaders.cost; omega)

end
end IntegerMultBounds.Machine.ActivePrefixCorrectionLoadRun
