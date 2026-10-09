import IntegerMultBounds.Machine.ButterflyStreamOriginal
import IntegerMultBounds.Machine.CountedBankHeaderClean

/-! Exact normalized physical states for a paired butterfly scan. Old input
streams are explicitly erased; only the two computed output streams survive. -/
namespace IntegerMultBounds.Machine.ButterflyStreamCleanData
noncomputable section
open ButterflyStreamData
variable {n : ℕ}

def headers (bs ls : List Bool) : Tapes 2 2 :=
  ⟨fun _ => 1,![RadixZeroFill.encodedBinary bs,RadixZeroFill.encodedBinary ls]⟩
def original (v : Tapes 52 2) (bs ls : List Bool) := v.append (headers bs ls)
def bank (v : Tapes 52 2) (bs ls : List Bool) := CountedLoopHeaderClean.bank (original v bs ls)

def input (a b : Fin n → Coefficient) :=
  ButterflyStreamEndpoint.input (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0) a b

def scanned (a b : Fin n → Coefficient) (w : ℕ) :=
  ButterflyStreamEndpoint.output (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0) a b w

def ready (a b : Fin n → Coefficient) (w : ℕ) : Tapes 52 2 :=
  ⟨fun _ => 0,(scanned a b w).tape⟩

def output (a b : Fin n → Coefficient) : Tapes 52 2 :=
  (⟨fun _ => 0,![fun _ => 0,fun _ => 0,
    full (fun _ => 0) 0 (fun i => result (a i) (b i) 0),
    full (fun _ => 0) 0 (fun i => result (a i) (b i) 1)]⟩ : Tapes 4 2).append
      (RadixLinearCombinationBootstrap.empty 48)

def streams (i : Fin 54) : Bool := decide (i.val<4)
def sources (i : Fin 54) : Bool := decide (i.val<2)
def streamLength (n w : ℕ) := n*(2*(w+1))

theorem rewound (a b : Fin n → Coefficient) (w : ℕ) (bs ls : List Bool) :
    CountedBankReset.rewound streams (original (scanned a b w) bs ls) (streamLength n w)=
      original (ready a b w) bs ls := by
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using (Fin.addCases (m:=52) (n:=2)) with
    | left i =>
      induction i using (Fin.addCases (m:=4) (n:=48)) with
      | left i => fin_cases i <;>
          simp [streams,original,scanned,ready,streamLength,
            ButterflyStreamEndpoint.output,Tapes.append,Fin.addCases]
      | right i =>
          have hi : ¬(4+i.val<4) := by omega
          simp [streams,original,scanned,ready,
            ButterflyStreamEndpoint.output,Tapes.append,hi,RadixLinearCombinationBootstrap.empty]
    | right i =>
      have hi : ¬(52+i.val<4) := by omega
      simp [streams,original,ready,Tapes.append,hi]
  · rfl

theorem full_erased (a : Fin n → Coefficient) (w : ℕ)
    (ha : ∀ i,(a i).1.length=w ∧ (a i).2.length=w) :
    CountedBankReset.erased (full (fun _ => 0) 0 a) 0 (streamLength n w)=fun _ => 0 := by
  have hl := CyclicRowSplit.prefix_length (fun i => encoded (a i)) (2*(w+1))
    (fun i => DelimitedRadixRecord.complex_length _ _ _ (ha i).1 (ha i).2) n le_rfl
  rw [CyclicRowCycle.prefix_all] at hl
  unfold full streamLength
  rw [← hl]
  exact CountedBankReset.erased_word _ 0

theorem restored (a b : Fin n → Coefficient) (w : ℕ) (bs ls : List Bool)
    (ha : ∀ i,(a i).1.length=w ∧ (a i).2.length=w)
    (hb : ∀ i,(b i).1.length=w ∧ (b i).2.length=w) :
    CountedBankReset.restored sources (original (ready a b w) bs ls) (streamLength n w)=
      original (output a b) bs ls := by
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using (Fin.addCases (m:=52) (n:=2)) with
    | left i =>
      induction i using (Fin.addCases (m:=4) (n:=48)) with
      | left i => simp [original,ready,output,Tapes.append]
      | right i => simp [original,ready,output,Tapes.append,RadixLinearCombinationBootstrap.empty]
    | right i => simp [original,Tapes.append]
  · funext i
    induction i using (Fin.addCases (m:=52) (n:=2)) with
    | left i =>
      induction i using (Fin.addCases (m:=4) (n:=48)) with
      | left i => fin_cases i <;>
          simp [CountedBankReset.after,sources,original,scanned,ready,output,
            ButterflyStreamEndpoint.output,Tapes.append,Fin.addCases,full_erased a w ha,full_erased b w hb]
      | right i =>
          have hi : ¬(4+i.val≤1) := by omega
          simp [CountedBankReset.after,sources,original,scanned,ready,output,
            ButterflyStreamEndpoint.output,Tapes.append,hi]
    | right i =>
      have hi : ¬(52+i.val≤1) := by omega
      simp [CountedBankReset.after,sources,original,Tapes.append,hi]

end
end IntegerMultBounds.Machine.ButterflyStreamCleanData
