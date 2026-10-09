import IntegerMultBounds.Machine.ActivePrefixParityOffsetBank

/-! Actual original-header setup, both generated prefix projections, batch
source-bit extraction and parity-XOR gather share one unchanged caller bank and
twenty-four blank private tapes. No intermediate stream is a stage input. -/
namespace IntegerMultBounds.Machine.ActivePrefixParityOffsetRun
noncomputable section
open ActivePrefixParityOffsetBank
variable {a : ℕ}

def bank (v : Tapes 17 a) := CleanSubbank.bank (s := 24) v

theorem pad15 (v : Tapes 17 a) :
    (CompactGadgetReservationHeadersCore.bank v).append (SharedBank.empty 9 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
theorem pad11 (v : Tapes 17 a) :
    (CleanSubbank.bank (s := 11) v).append (SharedBank.empty 13 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
theorem pad20 (v : Tapes 17 a) :
    (CleanSubbank.bank (s := 20) v).append (SharedBank.empty 4 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def setup := extend (ActivePrefixOffsetHeadersRun.program (a := a) headerFocus header_injective) 9
def projectT := BinaryPrefixFieldTablePlaced.program (a := a) tempFocus temp_injective
def projectX := BinaryPrefixFieldTablePlaced.program (a := a) sourceFocus source_injective
def extract := extend (SelectedSourceBitsStreamPlaced.program (a := a) extractFocus extract_injective) 13
def gather := extend (BinaryVaryingOffsetGatherPlaced.program (a := a) .parity gatherFocus gather_injective) 4
def program := seq (seq (seq (seq (setup (a := a)) projectT) projectX) extract) gather

def cost (s : Shape) :=
  ActivePrefixOffsetHeadersBudget.constant*(2^s.W*(s.W+1))+
  2*(BinaryPrefixFieldTableRun.constant*(2^s.W*(s.W+1)))+
  400*((sourceWord s).length+1)+320*(((controlWord s).length+1)*(s.q+s.b+1))+4

theorem setup_runs (s : Shape) (hs : Fin 8 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (setup (a := a)) (fun v => v=bank (base hs)) (fun v => v=bank (headers s hs))
      (ActivePrefixOffsetHeadersBudget.constant*(2^s.W*(s.W+1))) := by
  have h := ActivePrefixOffsetHeadersBudget.constructs (base (a := a) hs) headerFocus header_injective
    (headerWords hs) s.W s.q s.b s.n s.f (original_sources hs)
    (by intro i; fin_cases i <;> first | exact hv 0 | exact hv 3 | exact hv 4 | exact hv 5 | exact hv 7)
    (by intro i; fin_cases i <;> first | exact hc 0 | exact hc 3 | exact hc 4 | exact hc 5 | exact hc 7)
    s.hb s.hbq s.hnf (by have := s.sourceFits; omega) (by
      have hmul := Nat.mul_le_mul_left s.n (show s.b≤s.q by have := s.hbq; omega)
      have := s.tempFits
      omega)
  simpa only [setup,pad15,headers,ActivePrefixOffsetHeadersBudget.volume] using
    hoare_extend_eq h (SharedBank.empty 9 a)

theorem projectT_runs (s : Shape) (hs : Fin 8 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (projectT (a := a)) (fun v => v=bank (headers s hs)) (fun v => v=bank (tempReady s hs))
      (BinaryPrefixFieldTableRun.constant*(2^s.W*(s.W+1))) := by
  exact BinaryPrefixFieldTablePlaced.constructs _ _ temp_injective (tempHeaders s hs)
    s.W s.startT (s.n*s.q) s.tempFits (temp_sources s hs)
    (by intro i; fin_cases i; exact hv 0; exact hv 1; exact RecursiveChildQuotientsConstant.bits_value _)
    (by intro i; fin_cases i; exact hc 0; exact hc 1; exact RecursiveChildQuotientsConstant.bits_canonical _)

theorem projectX_runs (s : Shape) (hs : Fin 8 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (projectX (a := a)) (fun v => v=bank (tempReady s hs)) (fun v => v=bank (sourceReady s hs))
      (BinaryPrefixFieldTableRun.constant*(2^s.W*(s.W+1))) := by
  exact BinaryPrefixFieldTablePlaced.constructs _ _ source_injective (sourceHeaders s hs)
    s.W s.startX (s.f*s.q) s.sourceFits (source_sources s hs)
    (by intro i; fin_cases i; exact hv 0; exact hv 2; exact RecursiveChildQuotientsConstant.bits_value _)
    (by intro i; fin_cases i; exact hc 0; exact hc 2; exact RecursiveChildQuotientsConstant.bits_canonical _)

theorem extract_runs (s : Shape) (hs : Fin 8 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (extract (a := a)) (fun v => v=bank (sourceReady s hs)) (fun v => v=bank (controlReady s hs))
      (400*((sourceWord s).length+1)) := by
  have h := SelectedSourceBitsStreamPlaced.runs (sourceReady (a := a) s hs) extractFocus extract_injective
    (sourceWord s) (extractHeaders s hs) s.q s.rho s.n s.f (2^s.W) (extract_sources s hs)
    (BinaryPrefixFieldTableData.word_length _ _ _ _) s.hnf s.hr
    (by intro i; fin_cases i; exact hv 3; exact hv 5; exact hv 6; exact hv 7; exact RecursiveChildQuotientsConstant.bits_value _)
    (by intro i; fin_cases i; exact hc 3; exact hc 5; exact hc 6; exact hc 7; exact RecursiveChildQuotientsConstant.bits_canonical _)
  simpa only [extract,pad11,controlReady] using hoare_extend_eq h (SharedBank.empty 13 a)

theorem gather_runs (s : Shape) (hs : Fin 8 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (gather (a := a)) (fun v => v=bank (controlReady s hs)) (fun v => v=bank (gathered s hs))
      (320*(((controlWord s).length+1)*(s.q+s.b+1))) := by
  obtain ⟨ht,hx,hz⟩ := gather_tapes (a := a) s hs
  obtain ⟨hh,hp,hr,ho⟩ := gather_heads (a := a) s hs
  have h := BinaryVaryingOffsetGatherPlaced.runs .parity (controlReady (a := a) s hs) gatherFocus gather_injective
    s.q s.b s.hb s.hbq (tempWord s) (controlWord s) 0 0 0 (gatherHeaders s hs)
    (by intro i; fin_cases i; exact hv 3; exact hv 4;
        change Counter.value (RecursiveChildQuotientsConstant.bits (s.n*2^s.W))=(controlWord s).length
        rw [RecursiveChildQuotientsConstant.bits_value]
        simp [controlWord,Nat.mul_comm])
    (by intro i; fin_cases i; exact hc 3; exact hc 4; exact RecursiveChildQuotientsConstant.bits_canonical _)
    ht hh (by simp [controlWord,tempWord,BinaryVaryingOffsetGatherPlaced.sourceWidth,Nat.mul_assoc]) hx hz hp hr ho
  simpa only [gather,BinaryVaryingOffsetGatherPlaced.input,pad20,gathered] using hoare_extend_eq h (SharedBank.empty 4 a)

/-- The actual emitted offsets use source controls computed afresh at each
prefix address. The machine shape and finite control contain no dimensions. -/
theorem runs (s : Shape) (hs : Fin 8 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun v => v=bank (base hs)) (fun v => v=bank (gathered s hs)) (cost s) := by
  exact ((((setup_runs s hs hv hc).seq (projectT_runs s hs hv hc)).seq (projectX_runs s hs hv hc)).seq
    (extract_runs s hs hv hc)).seq (gather_runs s hs hv hc) |>.consequence
      (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.ActivePrefixParityOffsetRun
