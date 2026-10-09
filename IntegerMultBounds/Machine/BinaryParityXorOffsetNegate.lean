import IntegerMultBounds.Machine.BinaryParityXorOffsetLoop
import IntegerMultBounds.Machine.BinaryAddressOffsetRepeat

/-! Complete unary rowwise modular negation with blank initial workspace.
The input table is consumed and erased, the output is rewound, both loop
clocks are physically initialized/erased, and width/count headers survive. -/
namespace IntegerMultBounds.Machine.BinaryParityXorOffsetNegate
open SharedPlacementAlphabet (setTape)
open CountedCopyReuse (empty binary)
open BinaryParityXorOffsetRow (word)
open BinaryParityXorOffsetLoop (result)
noncomputable section

def raw (f g : ℤ → Fin 4) (p q : ℤ) (ws ns : List Bool) : Tapes 7 0 :=
  ⟨![p,q,0,0,1,0,1],![f,g,(fun _ => blank),(fun _ => blank),binary ws,(fun _ => blank),binary ns]⟩
def bank (f g : ℤ → Fin 4) (p q : ℤ) (ws ns : List Bool) := BinaryParityXorOffsetLoop.bank f g p q ws ns

def oneInit (slot : Fin 7) := Placement.placed (RecursiveChildQuotientsConstant.program (a := 0) 0)
  (FiniteReturnStackAt.placement slot)
def setup := seq (oneInit 3) (oneInit 5)
def clocks : List (Fin 7) := [3,5]
def clearClocks := BinaryDescriptorCleanupList.program (a := 0) (by decide : 0<7) clocks
def eraseSource := Placement.placed (EraseBack.program (a := 0)) (FiniteReturnStackAt.placement (0 : Fin 7))
def rewind := Placement.placed (ReturnOrigin.program (a := 0)) (FiniteReturnStackAt.placement (1 : Fin 7))
def program := seq (seq (seq (seq setup BinaryParityXorOffsetLoop.program) clearClocks) eraseSource) rewind

theorem init_hoare (slot : Fin 7) (v : Tapes 7 0) (ht : v.tape slot=fun _ => blank) (hh : v.head slot=0) :
    HoareTime (oneInit slot) (fun z => z=v) (fun z => z=setTape v slot empty 1) 6 := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := 0) 0)
    (FiniteReturnStackAt.placement slot) v (by rw [FiniteReturnStackAt.active_bank,ht,hh])
  apply h.consequence (fun _ h => h) _ (by decide)
  rintro z ⟨small,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

theorem setup_hoare (f g : ℤ → Fin 4) (p q : ℤ) (ws ns : List Bool) :
    HoareTime setup (fun z => z=raw f g p q ws ns) (fun z => z=bank f g p q ws ns) 13 := by
  have h0 := init_hoare 3 (raw f g p q ws ns) rfl rfl
  have h1 := init_hoare 5 (setTape (raw f g p q ws ns) 3 empty 1) rfl rfl
  have he : setTape (setTape (raw f g p q ws ns) 3 empty 1) 5 empty 1=bank f g p q ws ns := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h1
  exact h0.seq h1

theorem clear_clocks (f g : ℤ → Fin 4) (p q : ℤ) (ws ns : List Bool) :
    HoareTime clearClocks (fun z => z=bank f g p q ws ns) (fun z => z=raw f g p q ws ns) 10 := by
  have h := BinaryDescriptorCleanupList.cleanup_hoare (by decide : 0<7) clocks (by decide)
    (fun _ => []) (bank f g p q ws ns) (by
      intro i hi
      simp only [clocks,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl <;> exact ⟨rfl,rfl⟩)
  have he : BinaryDescriptorCleanupList.cleared clocks (bank f g p q ws ns)=raw f g p q ws ns := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  simpa only [he,clearClocks,show BinaryDescriptorCleanupList.cost clocks (fun _ => [])=10 by decide] using h
theorem erases (xs : List Bool) (g : ℤ → Fin 4) (q : ℤ) (ws ns : List Bool) :
    HoareTime eraseSource (fun z => z=raw (word xs) g xs.length q ws ns)
      (fun z => z=raw (fun _ => blank) g 0 q ws ns) (xs.length+2) := by
  have h := EraseBack.erase_hoare (fun _ => (blank : Fin 4)) 0 (xs.map bitSymbol)
    (ReturnOrigin.bits_nonblank xs) rfl (by intros; rfl)
  simp only [List.length_map,zero_add] at h
  have ha : Placement.active (FiniteReturnStackAt.placement (0 : Fin 7)) (raw (word xs) g xs.length q ws ns)=
      (EraseBack.cfg (word xs) xs.length 0).tapes := by rw [FiniteReturnStackAt.active_bank]; rfl
  apply (Placement.hoare_at h _ _ ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (fun _ => blank) 0)=_
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
theorem rewinds (xs : List Bool) (f : ℤ → Fin 4) (p : ℤ) (ws ns : List Bool) :
    HoareTime rewind (fun z => z=raw f (word xs) p xs.length ws ns)
      (fun z => z=raw f (word xs) p 0 ws ns) (xs.length+2) := by
  have h := ReturnOrigin.return_hoare_at (fun _ => (blank : Fin 4)) 0 (xs.map bitSymbol)
    (ReturnOrigin.bits_nonblank xs) rfl
  simp only [List.length_map,zero_add] at h
  have ha : Placement.active (FiniteReturnStackAt.placement (1 : Fin 7)) (raw f (word xs) p xs.length ws ns)=
      (ReturnOrigin.cfg (word xs) xs.length 0).tapes := by rw [FiniteReturnStackAt.active_bank]; rfl
  apply (Placement.hoare_at h _ _ ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (word xs) 0)=_
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def cost (W N : ℕ) (ws ns : List Bool) := BinaryParityXorOffsetLoop.cost W N ws ns+2*(N*W)+31

theorem runs (blocks : List (List Bool)) (W : ℕ) (hu : BlockRotationData.Uniform W blocks) (ws ns : List Bool)
    (hw : Counter.value ws=W) (hn : Counter.value ns=blocks.length) :
    HoareTime program (fun z => z=raw (word blocks.flatten) (fun _ => blank) 0 0 ws ns)
      (fun z => z=raw (fun _ => blank) (word (result blocks)) 0 0 ws ns) (cost W blocks.length ws ns) := by
  have hsource := BlockRotationData.uniform_volume W blocks hu
  have hout := BinaryParityXorOffsetLoop.result_length W blocks hu
  have h0 := setup_hoare (word blocks.flatten) (fun _ => blank) 0 0 ws ns
  have h1 := BinaryParityXorOffsetLoop.runs blocks W hu (fun _ => blank) (fun _ => blank) 0 0 ws ns hw hn
  simp only [zero_add] at h1
  have h2 := clear_clocks (word blocks.flatten) (word (result blocks)) (blocks.length*W) (blocks.length*W) ws ns
  have h3 := erases blocks.flatten (word (result blocks)) (blocks.length*W) ws ns
  have h4 := rewinds (result blocks) (fun _ => blank) 0 ws ns
  rw [hsource] at h3
  rw [hout] at h4
  exact ((((h0.seq h1).seq h2).seq h3).seq h4).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem cost_linear (W N : ℕ) (ws ns : List Bool) (hN : 0<N)
    (hw : Counter.value ws=W) (hn : Counter.value ns=N)
    (cw : GrowingCounterData.Canonical ws) (cn : GrowingCounterData.Canonical ns) :
    cost W N ws ns≤120*(N*(W+1)) := by
  have hlw := GrowingCounterData.canonical_width ws cw
  have hln := GrowingCounterData.canonical_width ns cn
  rw [hw] at hlw
  rw [hn] at hln
  have hwlog := Nat.log2_le_self W
  have hnlog := Nat.log2_le_self N
  have hcost : 12*W+7*ws.length+37≤19*W+44 := by omega
  have hmul := Nat.mul_le_mul_left N hcost
  unfold cost BinaryParityXorOffsetLoop.cost
  nlinarith

end
end IntegerMultBounds.Machine.BinaryParityXorOffsetNegate
