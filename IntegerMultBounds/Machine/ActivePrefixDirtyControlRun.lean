import IntegerMultBounds.Machine.ActivePrefixDirtyControlBank

/-! Original descriptors physically produce three prefix projections, compact
U parities and the selected/control/parity-XOR offsets. No intermediate stream
or synthetic wide source is an input to this machine. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlRun
noncomputable section
open ActivePrefixDirtyControlData ActivePrefixDirtyControlBank
open ActivePrefixDirtyControlHeaders (bank)
open BinaryVaryingOffsetGatherPlaced (Kind sourceWidth)
variable {a : ℕ} {k : Kind}

theorem pad19 (v : Tapes 15 a) :
    (CleanSubbank.bank (s := 19) v).append (SharedBank.empty 5 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
theorem pad20 (v : Tapes 15 a) :
    (CleanSubbank.bank (s := 20) v).append (SharedBank.empty 4 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def projectT (k : Kind) := BinaryPrefixFieldTablePlaced.program (a := a) (tempFocus k) temp_injective
def projectU := BinaryPrefixFieldTablePlaced.program (a := a) sourceFocus (by decide)
def projectClock := BinaryPrefixFieldTablePlaced.program (a := a) clockFocus (by decide)
def extract := extend (ActivePrefixDirtyControlParityPlaced.program (a := a) parityFocus (by decide)) 5
def gather (k : Kind) := extend (BinaryVaryingOffsetGatherPlaced.program (a := a) k gatherFocus (by decide)) 4
def program (k : Kind) := seq (seq (seq (seq (seq (ActivePrefixDirtyControlHeaders.program (a := a))
  (projectT k)) projectU) projectClock) extract) (gather k)

def cost (s : Shape k) := ActivePrefixDirtyControlHeaders.cost s+
  3*(BinaryPrefixFieldTableRun.constant*(2^s.W*(s.W+1)))+
  330*(((clockWord s).length+1)*(s.b+2))+320*(((controlWord s).length+1)*(s.q+s.b+1))+5

theorem projectT_runs (s : Shape k) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (projectT (a := a) k) (fun v => v=bank (headers s hs)) (fun v => v=bank (tempReady s hs))
      (BinaryPrefixFieldTableRun.constant*(2^s.W*(s.W+1))) := by
  apply BinaryPrefixFieldTablePlaced.constructs _ _ temp_injective (tempHeaders s hs)
    s.W s.startT (tempWidth s) s.tempFits (temp_sources s hs)
  · intro i; fin_cases i
    · exact hv 0
    · exact hv 1
    · cases k
      · exact RecursiveChildQuotientsConstant.bits_value _
      · simpa [tempHeaders,tempWidthWord,tempWidth,sourceWidth,values,
          BinaryPrefixFieldTableGather.values] using hv 5
      · exact RecursiveChildQuotientsConstant.bits_value _
  · intro i; fin_cases i
    · exact hc 0
    · exact hc 1
    · cases k
      · exact RecursiveChildQuotientsConstant.bits_canonical _
      · exact hc 5
      · exact RecursiveChildQuotientsConstant.bits_canonical _

theorem projectU_runs (s : Shape k) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (projectU (a := a)) (fun v => v=bank (tempReady s hs)) (fun v => v=bank (sourceReady s hs))
      (BinaryPrefixFieldTableRun.constant*(2^s.W*(s.W+1))) := by
  exact BinaryPrefixFieldTablePlaced.constructs _ _ (by decide) (sourceHeaders s hs)
    s.W s.startU (s.n*s.b) s.controlFits (source_sources s hs)
    (by intro i; fin_cases i; exact hv 0; exact hv 2; exact RecursiveChildQuotientsConstant.bits_value _)
    (by intro i; fin_cases i; exact hc 0; exact hc 2; exact RecursiveChildQuotientsConstant.bits_canonical _)

theorem projectClock_runs (s : Shape k) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (projectClock (a := a)) (fun v => v=bank (sourceReady s hs)) (fun v => v=bank (clockReady s hs))
      (BinaryPrefixFieldTableRun.constant*(2^s.W*(s.W+1))) := by
  exact BinaryPrefixFieldTablePlaced.constructs _ _ (by decide) (clockHeaders hs)
    s.W s.startU s.n (clockFits s) (clock_sources s hs)
    (by intro i; fin_cases i; exact hv 0; exact hv 2; exact hv 5)
    (by intro i; fin_cases i; exact hc 0; exact hc 2; exact hc 5)

theorem extract_runs (s : Shape k) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (extract (a := a)) (fun v => v=bank (clockReady s hs)) (fun v => v=bank (controlReady s hs))
      (330*(((clockWord s).length+1)*(s.b+2))) := by
  have h := ActivePrefixDirtyControlParityPlaced.runs (clockReady (a := a) s hs) parityFocus (by decide)
    s.b s.hb (sourceWord s) (clockWord s) (parityHeaders s hs) (parity_sources s hs)
    (by
      intro i; fin_cases i
      · exact hv 4
      · simp [parityHeaders,CountedPackedParityHeaders.originalValues,RecursiveChildQuotientsConstant.bits_value,clockWord,Nat.mul_comm])
    (by intro i; fin_cases i; exact hc 4; exact RecursiveChildQuotientsConstant.bits_canonical _)
    (by simp [sourceWord,clockWord,Nat.mul_assoc])
  simpa only [extract,pad19,controlReady] using hoare_extend_eq h (SharedBank.empty 5 a)

theorem gather_runs (s : Shape k) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (gather (a := a) k) (fun v => v=bank (controlReady s hs)) (fun v => v=bank (gathered s hs))
      (320*(((controlWord s).length+1)*(s.q+s.b+1))) := by
  obtain ⟨ht,hx,hz⟩ := gather_tapes (a := a) s hs
  obtain ⟨hh,hp,hr,ho⟩ := gather_heads (a := a) s hs
  have h := BinaryVaryingOffsetGatherPlaced.runs k (controlReady (a := a) s hs) gatherFocus (by decide)
    s.q s.b s.hb s.hbq (tempWord s) (controlWord s) 0 0 0 (gatherHeaders s hs)
    (by intro i; fin_cases i; exact hv 3; exact hv 4
        change Counter.value (RecursiveChildQuotientsConstant.bits (s.n*2^s.W))=(controlWord s).length
        rw [RecursiveChildQuotientsConstant.bits_value,control_length,Nat.mul_comm])
    (by intro i; fin_cases i; exact hc 3; exact hc 4; exact RecursiveChildQuotientsConstant.bits_canonical _)
    ht hh (by simp [tempWord,tempWidth,Nat.mul_assoc]) hx hz hp hr ho
  simpa only [gather,BinaryVaryingOffsetGatherPlaced.input,pad20,gathered] using hoare_extend_eq h (SharedBank.empty 4 a)

theorem runs (s : Shape k) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a) k) (fun v => v=bank (base hs)) (fun v => v=bank (gathered s hs)) (cost s) := by
  exact (((((ActivePrefixDirtyControlHeaders.runs s hs hv hc).seq (projectT_runs s hs hv hc)).seq
    (projectU_runs s hs hv hc)).seq (projectClock_runs s hs hv hc)).seq (extract_runs s hs hv hc)).seq
    (gather_runs s hs hv hc) |>.consequence (fun _ h => h) (fun _ h => h)
      (by unfold cost; omega)

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlRun
