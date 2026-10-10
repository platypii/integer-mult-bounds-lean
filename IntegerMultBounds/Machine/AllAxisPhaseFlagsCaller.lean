import IntegerMultBounds.Machine.AllAxisPhaseHeadersBudget
import IntegerMultBounds.Machine.SparsePhaseFlagsCaller
import IntegerMultBounds.Machine.RepeatedWeightedPhaseHeader

/-! All-axis phase flags from original numeric geometry. Extraction clocks
are reused for the runtime-axis scanner only after extraction restores them;
both scanner clocks are physically initialized and completely erased. -/
namespace IntegerMultBounds.Machine.AllAxisPhaseFlagsCaller
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open ActiveRepairRankHeadersCommands (bank)
open AllAxisPhaseHeadersData (offset)
open MarkedWordCleanup (one)
open UnitPhaseNumerator (flags)
variable {s : Shape}

def headers (v : Stage s) (m : ℕ) : Fin 3 → List Bool :=
  fun i => RecursiveChildQuotientsConstant.bits (AllAxisPhaseHeadersData.values v m i)
def controls (v : Stage s) (m : ℕ) (addr : List Bool) :=
  SelectedSourceBitsData.selected addr s.chunk (offset v m) (m*v.f)
def phase (v : Stage s) (m : ℕ) (ws : List (ZMod 4)) (addr : List Bool) :=
  RepeatedWeightedPhaseAccumulator.accumulate 0 ws (fun i => (controls v m addr).getD i false) v.f

def input (order : Order) (v : Stage s) (rows : ℕ) (addr : List Bool) (tail : Tapes 6 2) :=
  (bank (AllAxisPhaseHeadersData.initial order v rows)).append (SparsePhaseFlagsCaller.privateInput addr tail)
def prepared (order : Order) (v : Stage s) (rows m : ℕ) (addr : List Bool) (tail : Tapes 6 2) :=
  (bank (AllAxisPhaseHeadersData.finished order v rows m)).append (SparsePhaseFlagsCaller.privateInput addr tail)
def privateFlags (addr : List Bool) (tail : Tapes 6 2) : Tapes 13 2 :=
  (one (SelectedSourceBitsScan.word addr) 0).append
    ((SharedBank.empty 4 2).append ((flags 0).append tail))
def flagged (order : Order) (v : Stage s) (rows m : ℕ) (addr : List Bool) (tail : Tapes 6 2) :=
  (bank (AllAxisPhaseHeadersData.finished order v rows m)).append (privateFlags addr tail)
def privateExtracted (v : Stage s) (m : ℕ) (addr : List Bool) (tail : Tapes 6 2) : Tapes 13 2 :=
  (one (SelectedSourceBitsScan.word addr) 0).append
    ((one (SelectedSourceBitsScan.word (controls v m addr)) 0).append
      ((SharedBank.empty 3 2).append ((flags 0).append tail)))
def extracted (order : Order) (v : Stage s) (rows m : ℕ) (addr : List Bool) (tail : Tapes 6 2) :=
  (bank (AllAxisPhaseHeadersData.finished order v rows m)).append (privateExtracted v m addr tail)

def scanSlots : Fin 6 → Fin 56 := ![48,49,44,7,45,46]
theorem scanInjective : Function.Injective scanSlots := by decide +kernel
def scanPlacement := InjectivePlacement.placement scanSlots scanInjective (by decide : 6+50=56)
def derive (m : ℕ) := extend (CompactChildHeadersArithmetic.compile (a := 2) (AllAxisPhaseHeadersData.schedule m)).2 13
def flagInit := Placement.placed (extend SparsePhaseFlags.prepare 6) SparsePhaseFlagsCaller.placement
def addressExtract := Placement.placed (extend SparsePhaseFlags.extractor 6) SparsePhaseFlagsCaller.placement
def extract := seq flagInit addressExtract
def scan (ws : List (ZMod 4)) := Placement.placed (RepeatedWeightedPhaseHeader.program ws) scanPlacement
def program (m : ℕ) (ws : List (ZMod 4)) := seq (seq (derive m) extract) (scan ws)
def output (order : Order) (v : Stage s) (rows m : ℕ) (ws : List (ZMod 4))
    (addr : List Bool) (tail : Tapes 6 2) :=
  Placement.replace scanPlacement (extracted order v rows m addr tail)
    (RepeatedWeightedPhaseHeader.boundary (phase v m ws addr)
      (SelectedSourceBitsScan.word (controls v m addr)) (m*v.f)
      (RecursiveChildQuotientsConstant.bits v.f))

private theorem binary_encoded (bs : List Bool) :
    RadixZeroFill.encodedBinary (q := 2) bs=CountedLoopReuseAlphabet.binary bs :=
  CountedLoopReuseAlphabet.encoding_binary bs

private theorem extra_index (i : Fin 40) :
    ∃ j : Fin 43,SparsePhaseFlagsCaller.placement (Fin.natAdd 16 i)=Fin.castAdd 13 j := by
  have h : (SparsePhaseFlagsCaller.placement (Fin.natAdd 16 i)).val<43 := by fin_cases i <;> decide
  exact ⟨⟨(SparsePhaseFlagsCaller.placement (Fin.natAdd 16 i)).val,h⟩,by apply Fin.ext; rfl⟩
private theorem extra_frame (b : Tapes 43 2) (x y : Tapes 13 2) :
    Placement.extra SparsePhaseFlagsCaller.placement (b.append x)=
      Placement.extra SparsePhaseFlagsCaller.placement (b.append y) := by
  apply congrArg₂ Tapes.mk
  · funext i
    obtain ⟨j,hj⟩ := extra_index i
    change (b.append x).head (SparsePhaseFlagsCaller.placement (Fin.natAdd 16 i))=
      (b.append y).head (SparsePhaseFlagsCaller.placement (Fin.natAdd 16 i))
    rw [hj]
    simp only [Tapes.append,Fin.addCases_left]
  · funext i
    obtain ⟨j,hj⟩ := extra_index i
    change (b.append x).tape (SparsePhaseFlagsCaller.placement (Fin.natAdd 16 i))=
      (b.append y).tape (SparsePhaseFlagsCaller.placement (Fin.natAdd 16 i))
    rw [hj]
    simp only [Tapes.append,Fin.addCases_left]

private theorem exactPlaced {t u n q B : ℕ} (M : Program t q 2) (e : Fin (t+u) ≃ Fin n)
    (v w : Tapes t 2) (before after : Tapes n 2) (h : HoareTime M (fun x => x=v) (fun x => x=w) B)
    (hb : Placement.active e before=v) (ha : Placement.active e after=w)
    (hf : Placement.extra e before=Placement.extra e after) :
    HoareTime (Placement.placed M e) (fun x => x=before) (fun x => x=after) B := by
  apply (Placement.hoare_at h e before hb).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨small,rfl,rfl⟩
  rw [Placement.replace,hf]
  exact (congrArg (fun z => Placement.combine e z (Placement.extra e after)) ha.symm).trans (Placement.view e after)

theorem extract_runs (order : Order) (v : Stage s) (rows m : ℕ) (hm : 0<m)
    (addr : List Bool) (tail : Tapes 6 2)
    (hspan : offset v m+(m*v.f-1)*s.chunk<addr.length) :
    HoareTime extract (fun z => z=prepared order v rows m addr tail)
      (fun z => z=extracted order v rows m addr tail) (400*(addr.length+1)+2) := by
  have hq : 1≤s.chunk := by have := v.selectedFits; omega
  have hmf : 0<m*v.f := Nat.mul_pos hm v.positiveWidth
  have hp := SparsePhaseFlags.prepare_runs addr (headers v m)
  have hx := SparsePhaseFlags.extractor_runs addr (headers v m) s.chunk (offset v m) (m*v.f-1)
    hspan hq (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_value _)
    (fun i => RecursiveChildQuotientsConstant.bits_canonical _)
  have hpSmall := hoare_extend_eq hp tail
  have hxSmall := hoare_extend_eq hx tail
  have ha : Placement.active SparsePhaseFlagsCaller.placement (prepared order v rows m addr tail)=
      (SparsePhaseFlags.initial addr (headers v m)).append tail := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals first | rfl | exact binary_encoded _
  have hf0 : Placement.active SparsePhaseFlagsCaller.placement (flagged order v rows m addr tail)=
      (SparsePhaseFlags.input addr (headers v m)).append tail := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals first | rfl | exact binary_encoded _
  have hb : Placement.active SparsePhaseFlagsCaller.placement (extracted order v rows m addr tail)=
      (SparsePhaseFlags.extracted addr (headers v m) s.chunk (offset v m) (m*v.f-1)).append tail := by
    have he : m*v.f-1+1=m*v.f := by omega
    simp only [SparsePhaseFlags.extracted,SparseSourceBitsRun.output,he]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals first | rfl | exact binary_encoded _
  have hprep := exactPlaced (extend SparsePhaseFlags.prepare 6) SparsePhaseFlagsCaller.placement
    _ _ (prepared order v rows m addr tail) (flagged order v rows m addr tail)
    hpSmall ha hf0 (extra_frame _ _ _)
  have hext := exactPlaced (extend SparsePhaseFlags.extractor 6) SparsePhaseFlagsCaller.placement
    _ _ (flagged order v rows m addr tail) (extracted order v rows m addr tail)
    hxSmall hf0 hb (extra_frame _ _ _)
  exact (hprep.seq hext).consequence (fun _ h => h) (fun _ h => h) (by omega)

private theorem scan_active (order : Order) (v : Stage s) (rows m : ℕ)
    (addr : List Bool) (tail : Tapes 6 2) :
    Placement.active scanPlacement (extracted order v rows m addr tail)=
      RepeatedWeightedPhaseHeader.boundary 0 (SelectedSourceBitsScan.word (controls v m addr)) 0
        (RecursiveChildQuotientsConstant.bits v.f) := by
  rw [scanPlacement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals rfl

theorem scan_runs (order : Order) (v : Stage s) (rows m : ℕ) (ws : List (ZMod 4))
    (hl : m=ws.length) (addr : List Bool) (tail : Tapes 6 2) :
    HoareTime (scan ws) (fun z => z=extracted order v rows m addr tail)
      (fun z => z=output order v rows m ws addr tail)
      (ws.length*(7*v.f+11*(RecursiveChildQuotientsConstant.bits v.f).length+36)) := by
  let bs := controls v m addr
  have hb : ∀ i<ws.length*v.f,(SelectedSourceBitsScan.word bs : ℤ → Fin 6) (0+i)=bitSymbol (bs.getD i false) := by
    intro i hi
    have hi' : i<bs.length := by simpa only [bs,controls,SelectedSourceBitsData.selected_length,hl] using hi
    change putWord (fun _ => blank) 0 (bs.map bitSymbol) (0+i)=_
    rw [Gather.putWord_getD _ _ _ _ (by simpa using hi')]
  have hr := RepeatedWeightedPhaseHeader.runs 0 ws (fun i => bs.getD i false)
    (SelectedSourceBitsScan.word bs) 0 (RecursiveChildQuotientsConstant.bits v.f) v.f
    (RecursiveChildQuotientsConstant.bits_value _) hb
  simp only [zero_add] at hr
  have hout : (ws.length : ℤ)*(v.f : ℤ)=(m*v.f : ℕ) := by rw [hl,Nat.cast_mul]
  rw [hout] at hr
  apply (Placement.hoare_at hr scanPlacement (extracted order v rows m addr tail)
    (scan_active order v rows m addr tail)).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  rfl

theorem runs (order : Order) (v : Stage s) (rows m : ℕ) (ws : List (ZMod 4))
    (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (addr : List Bool) (tail : Tapes 6 2) (ha : addr.length=s.bits)
    (hspan : offset v m+(m*v.f-1)*s.chunk<s.bits) :
    HoareTime (program m ws) (fun z => z=input order v rows addr tail)
      (fun z => z=output order v rows m ws addr tail)
      (10400*(s.bits+1)+ws.length*(7*v.f+11*(RecursiveChildQuotientsConstant.bits v.f).length+36)+4) := by
  have hd := hoare_extend_eq (AllAxisPhaseHeadersData.runs (a := 2) order v rows m hm hslots)
    (SparsePhaseFlagsCaller.privateInput addr tail)
  have hx := extract_runs order v rows m hm addr tail (by simpa only [ha] using hspan)
  have hs := scan_runs order v rows m ws hl addr tail
  have hb := AllAxisPhaseHeadersBudget.cost_bound order v rows m hm hslots
  apply ((hd.seq hx).seq hs).consequence (fun _ h => h) (fun _ h => h) _
  rw [ha]
  omega

end
end IntegerMultBounds.Machine.AllAxisPhaseFlagsCaller
