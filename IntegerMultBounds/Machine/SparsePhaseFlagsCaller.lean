import IntegerMultBounds.Machine.SparsePhaseHeadersBudget
import IntegerMultBounds.Machine.SparsePhaseFlags
import IntegerMultBounds.Machine.SparsePhaseUnitCaller

/-! The physical sparse header outputs are shared directly with the complete
address-to-phase kernel. No stride, offset, control word or phase flag is
supplied to this fifty-six-tape caller. -/
namespace IntegerMultBounds.Machine.SparsePhaseFlagsCaller
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open SparsePhaseHeadersData (values offset)
open ActiveRepairRankHeadersCommands (bank)
open MarkedWordCleanup (one)
open UnitPhaseNumerator (flags)
variable {s : Shape}

def headers (v : Stage s) (axis : Fin v.f) (m : ℕ) : Fin 3 → List Bool :=
  fun i => RecursiveChildQuotientsConstant.bits (values v axis m i)
def privateInput (addr : List Bool) (tail : Tapes 6 2) : Tapes 13 2 :=
  (one (SelectedSourceBitsScan.word addr) 0).append
    ((SharedBank.empty 4 2).append ((SharedBank.empty 2 2).append tail))
def privateOutput (ws : List (ZMod 4)) (addr : List Bool) (q rho n : ℕ)
    (tail : Tapes 6 2) : Tapes 13 2 :=
  let bs := SparseWeightedUnitPhase.selected addr q rho n
  let p := WeightedPhaseAccumulator.accumulate 0 ws bs
  (one (SelectedSourceBitsScan.word addr) 0).append
    ((one (SelectedSourceBitsScan.word bs) bs.length).append
      ((SharedBank.empty 3 2).append ((flags p).append tail)))
def input (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f)
    (addr : List Bool) (tail : Tapes 6 2) :=
  (bank (SparsePhaseHeadersData.initial order v rows axis)).append (privateInput addr tail)
def prepared (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (addr : List Bool) (tail : Tapes 6 2) :=
  (bank (SparsePhaseHeadersData.finished order v rows axis m)).append (privateInput addr tail)
def output (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (tail : Tapes 6 2) :=
  (bank (SparsePhaseHeadersData.finished order v rows axis m)).append
    (privateOutput ws addr (v.f*s.chunk) (offset v axis m) (m-1) tail)

def placement : Fin (16+40) ≃ Fin 56 where
  toFun := ![43,44,45,22,46,23,47,24,48,49,50,51,52,53,54,55,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42]
  invFun := ![16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,3,5,7,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,0,1,2,4,6,8,9,10,11,12,13,14,15]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def derive (m : ℕ) := extend (CompactChildHeadersArithmetic.compile (a := 2) (SparsePhaseHeadersData.schedule m)).2 13
def multiplier (ws : List (ZMod 4)) := Placement.placed (extend (SparsePhaseFlags.program ws) 6) placement
def program (m : ℕ) (ws : List (ZMod 4)) := seq (derive m) (multiplier ws)

private theorem extra_index (i : Fin 40) :
    ∃ j : Fin 43,placement (Fin.natAdd 16 i)=Fin.castAdd 13 j := by
  have h : (placement (Fin.natAdd 16 i)).val<43 := by fin_cases i <;> decide
  exact ⟨⟨(placement (Fin.natAdd 16 i)).val,h⟩,by apply Fin.ext; rfl⟩

private theorem extra_frame (b : Tapes 43 2) (x y : Tapes 13 2) :
    Placement.extra placement (b.append x)=Placement.extra placement (b.append y) := by
  apply congrArg₂ Tapes.mk
  · funext i
    obtain ⟨j,hj⟩ := extra_index i
    change (b.append x).head (placement (Fin.natAdd 16 i))=(b.append y).head (placement (Fin.natAdd 16 i))
    rw [hj]
    simp only [Tapes.append,Fin.addCases_left]
  · funext i
    obtain ⟨j,hj⟩ := extra_index i
    change (b.append x).tape (placement (Fin.natAdd 16 i))=(b.append y).tape (placement (Fin.natAdd 16 i))
    rw [hj]
    simp only [Tapes.append,Fin.addCases_left]

private theorem binary_encoded (bs : List Bool) :
    RadixZeroFill.encodedBinary (q := 2) bs=CountedLoopReuseAlphabet.binary bs :=
  CountedLoopReuseAlphabet.encoding_binary bs

theorem multiplier_runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hl : m=ws.length)
    (addr : List Bool) (tail : Tapes 6 2)
    (hspan : offset v axis m+(m-1)*(v.f*s.chunk)<addr.length) :
    HoareTime (multiplier ws) (fun z => z=prepared order v rows axis m addr tail)
      (fun z => z=output order v rows axis m ws addr tail)
      (400*(addr.length+1)+2*ws.length+3) := by
  have hq : 1≤v.f*s.chunk := Nat.mul_pos v.positiveWidth (by have := v.selectedFits; omega)
  have hsmall := hoare_extend_eq (SparsePhaseFlags.runs ws addr (headers v axis m) (v.f*s.chunk) (offset v axis m) (m-1)
    (by omega) hspan hq (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_value _)
    (fun i => RecursiveChildQuotientsConstant.bits_canonical _)) tail
  have ha : Placement.active placement (prepared order v rows axis m addr tail)=
      (SparsePhaseFlags.initial addr (headers v axis m)).append tail := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals first | rfl | exact binary_encoded _
  have hb : Placement.active placement (output order v rows axis m ws addr tail)=
      (SparsePhaseFlags.output ws addr (headers v axis m) (v.f*s.chunk) (offset v axis m) (m-1)).append tail := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals first | rfl | exact binary_encoded _
  have hf : Placement.extra placement (prepared order v rows axis m addr tail)=
      Placement.extra placement (output order v rows axis m ws addr tail) := by
    exact extra_frame _ _ _
  apply (Placement.hoare_at hsmall placement (prepared order v rows axis m addr tail) ha).consequence
    (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  rw [Placement.replace,hf]
  exact (congrArg (fun x => Placement.combine placement x
    (Placement.extra placement (output order v rows axis m ws addr tail))) hb.symm).trans
      (Placement.view placement (output order v rows axis m ws addr tail))

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (addr : List Bool) (tail : Tapes 6 2)
    (hspan : offset v axis m+(m-1)*(v.f*s.chunk)<addr.length)
    (ha : addr.length=s.bits) :
    HoareTime (program m ws) (fun z => z=input order v rows axis addr tail)
      (fun z => z=output order v rows axis m ws addr tail)
      (10400*(s.bits+1)+2*m+4) := by
  have h0 := hoare_extend_eq (SparsePhaseHeadersData.runs (a := 2) order v rows axis m hm hslots)
    (privateInput addr tail)
  have h1 := multiplier_runs order v rows axis m ws hm hl addr tail hspan
  have hd := SparsePhaseHeadersBudget.cost_bound order v rows axis m hm hslots
  apply (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) _
  rw [ha,←hl]
  omega

end
end IntegerMultBounds.Machine.SparsePhaseFlagsCaller
