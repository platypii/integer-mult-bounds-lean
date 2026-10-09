import IntegerMultBounds.Machine.SparsePhaseFlags
import IntegerMultBounds.Machine.RepeatedWeightedPhaseAccumulator

/-! A single full-address extraction followed by a runtime-axis weighted scan.
The resulting phase flags are retained for all coefficients at that address;
no coefficient traversal is repeated for each coordinate axis. -/
namespace IntegerMultBounds.Machine.SparseRepeatedPhaseFlags
noncomputable section
open UnitPhaseNumerator (flags)
open SelectedSourceBitsCore (payload)
open SelectedSourceBitsScan (word)
open SelectedSourceBitsBank (raw)
open CountedLoopReuseAlphabet (empty binary controls)
open RepeatedWeightedPhaseAccumulator (accumulate)

def clock (ds : List Bool) : Tapes 2 2 := controls empty (binary ds) 1 1

def initial (addr : List Bool) (hs : Fin 3 → List Bool) (ds : List Bool) : Tapes 12 2 :=
  (SparsePhaseFlags.initial addr hs).append (clock ds)
def input (addr : List Bool) (hs : Fin 3 → List Bool) (ds : List Bool) : Tapes 12 2 :=
  (SparsePhaseFlags.input addr hs).append (clock ds)
def extracted (addr : List Bool) (hs : Fin 3 → List Bool) (ds : List Bool)
    (q rho n : ℕ) : Tapes 12 2 :=
  (SparsePhaseFlags.extracted addr hs q rho n).append (clock ds)
def output (ws : List (ZMod 4)) (addr : List Bool) (hs : Fin 3 → List Bool)
    (ds : List Bool) (q rho f : ℕ) : Tapes 12 2 :=
  let bs := SelectedSourceBitsData.selected addr q rho (ws.length*f)
  ((raw (payload (word addr) (word bs) 0 bs.length) hs).append
    (flags (accumulate 0 ws (fun i => bs.getD i false) f))).append (clock ds)

def placement : Fin (5+7) ≃ Fin 12 where
  toFun := ![8,9,1,10,11,0,2,3,4,5,6,7]
  invFun := ![5,2,6,7,8,9,10,11,0,1,3,4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def accumulator (ws : List (ZMod 4)) :=
  Placement.placed (RepeatedWeightedPhaseAccumulator.program ws) placement
def program (ws : List (ZMod 4)) :=
  seq (seq (extend SparsePhaseFlags.prepare 2) (extend SparsePhaseFlags.extractor 2))
    (accumulator ws)

private theorem placed {t u n q B : ℕ} (M : Program t q 2) (e : Fin (t+u) ≃ Fin n)
    (v w : Tapes t 2) (before after : Tapes n 2) (h : HoareTime M (fun x => x=v) (fun x => x=w) B)
    (hb : Placement.active e before=v) (ha : Placement.active e after=w)
    (hf : Placement.extra e before=Placement.extra e after) :
    HoareTime (Placement.placed M e) (fun x => x=before) (fun x => x=after) B := by
  apply (Placement.hoare_at h e before hb).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨small,rfl,rfl⟩
  rw [Placement.replace,hf]
  exact (congrArg (fun z => Placement.combine e z (Placement.extra e after)) ha.symm).trans (Placement.view e after)

private theorem active_extracted (ws : List (ZMod 4)) (addr : List Bool)
    (hs : Fin 3 → List Bool) (ds : List Bool) (q rho f : ℕ) (hm : 0<ws.length*f) :
    Placement.active placement (extracted addr hs ds q rho (ws.length*f-1))=
      RepeatedWeightedPhaseAccumulator.boundary 0
        (word (SelectedSourceBitsData.selected addr q rho (ws.length*f))) 0 ds := by
  have he : ws.length*f-1+1=ws.length*f := by omega
  simp only [extracted,SparsePhaseFlags.extracted,SparseSourceBitsRun.output,he]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem active_output (ws : List (ZMod 4)) (addr : List Bool)
    (hs : Fin 3 → List Bool) (ds : List Bool) (q rho f : ℕ) :
    let bs := SelectedSourceBitsData.selected addr q rho (ws.length*f)
    Placement.active placement (output ws addr hs ds q rho f)=
      RepeatedWeightedPhaseAccumulator.boundary (accumulate 0 ws (fun i => bs.getD i false) f)
        (word bs) (ws.length*f) ds := by
  simp only [output,SelectedSourceBitsData.selected_length]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem extra_model_head (addr bs cs : List Bool) (hs : Fin 3 → List Bool)
    (ds : List Bool) (p r : Fin 4) (i j : ℤ) :
    (Placement.extra placement (((raw (payload (word addr) (word bs) 0 i) hs).append (flags p)).append (clock ds))).head=
    (Placement.extra placement (((raw (payload (word addr) (word cs) 0 j) hs).append (flags r)).append (clock ds))).head := by
  funext k
  fin_cases k <;> rfl

private theorem extra_model_tape (addr bs cs : List Bool) (hs : Fin 3 → List Bool)
    (ds : List Bool) (p r : Fin 4) (i j : ℤ) :
    (Placement.extra placement (((raw (payload (word addr) (word bs) 0 i) hs).append (flags p)).append (clock ds))).tape=
    (Placement.extra placement (((raw (payload (word addr) (word cs) 0 j) hs).append (flags r)).append (clock ds))).tape := by
  funext k
  fin_cases k <;> rfl

private theorem extra_model (addr bs cs : List Bool) (hs : Fin 3 → List Bool)
    (ds : List Bool) (p r : Fin 4) (i j : ℤ) :
    Placement.extra placement (((raw (payload (word addr) (word bs) 0 i) hs).append (flags p)).append (clock ds))=
    Placement.extra placement (((raw (payload (word addr) (word cs) 0 j) hs).append (flags r)).append (clock ds)) := by
  exact congrArg₂ Tapes.mk (extra_model_head addr bs cs hs ds p r i j)
    (extra_model_tape addr bs cs hs ds p r i j)

private theorem extra_preserved (ws : List (ZMod 4)) (addr : List Bool)
    (hs : Fin 3 → List Bool) (ds : List Bool) (q rho f : ℕ) :
    Placement.extra placement (extracted addr hs ds q rho (ws.length*f-1))=
      Placement.extra placement (output ws addr hs ds q rho f) := by
  exact extra_model _ _ _ _ _ _ _ _ _

private theorem word_read (bs : List Bool) (i : ℕ) (hi : i<bs.length) :
    (word bs : ℤ → Fin 6) (0+i)=bitSymbol (bs.getD i false) := by
  change putWord (fun _ => blank) 0 (bs.map bitSymbol) (0+i)=_
  rw [Gather.putWord_getD _ _ _ _ (by simpa using hi)]

theorem accumulator_runs (ws : List (ZMod 4)) (addr : List Bool) (hs : Fin 3 → List Bool)
    (ds : List Bool) (q rho f : ℕ) (hm : 0<ws.length*f) (hf : Counter.value ds=f) :
    HoareTime (accumulator ws)
      (fun z => z=extracted addr hs ds q rho (ws.length*f-1))
      (fun z => z=output ws addr hs ds q rho f)
      (ws.length*(7*f+7*ds.length+17)) := by
  let bs := SelectedSourceBitsData.selected addr q rho (ws.length*f)
  have hb : ∀ i<ws.length*f,(word bs : ℤ → Fin 6) (0+i)=bitSymbol (bs.getD i false) := by
    intro i hi
    exact word_read bs i (by simpa [bs] using hi)
  have hr := RepeatedWeightedPhaseAccumulator.runs 0 ws (fun i => bs.getD i false)
    (word bs) 0 ds f hf hb
  simp only [zero_add] at hr
  exact placed _ _ _ _ _ _ hr (active_extracted ws addr hs ds q rho f hm)
    (active_output ws addr hs ds q rho f) (extra_preserved ws addr hs ds q rho f)

theorem runs (ws : List (ZMod 4)) (addr : List Bool) (hs : Fin 3 → List Bool)
    (ds : List Bool) (q rho f : ℕ) (hm : 0<ws.length*f)
    (hspan : rho+(ws.length*f-1)*q<addr.length) (hpos : 1≤q)
    (hq : Counter.value (hs 0)=q) (hn : Counter.value (hs 1)=ws.length*f-1)
    (hr : Counter.value (hs 2)=rho) (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (hf : Counter.value ds=f) :
    HoareTime (program ws) (fun z => z=initial addr hs ds)
      (fun z => z=output ws addr hs ds q rho f)
      (400*(addr.length+1)+ws.length*(7*f+7*ds.length+17)+3) := by
  have hp := hoare_extend_eq (SparsePhaseFlags.prepare_runs addr hs) (clock ds)
  have hx := hoare_extend_eq (SparsePhaseFlags.extractor_runs addr hs q rho
    (ws.length*f-1) hspan hpos hq hn hr hc) (clock ds)
  exact ((hp.seq hx).seq (accumulator_runs ws addr hs ds q rho f hm hf)).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.SparseRepeatedPhaseFlags
