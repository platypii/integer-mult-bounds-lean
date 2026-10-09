import IntegerMultBounds.Machine.ActivePrefixParityOffsetCleanup

/-! Complete parity-XOR offset producer from original prefix/source/gadget
descriptors, including all tables, varying controls, arithmetic and cleanup.
Every derived word and temporary stream is physically generated and erased. -/
namespace IntegerMultBounds.Machine.ActivePrefixParityOffset
noncomputable section
open ActivePrefixParityOffsetBank
open ActivePrefixParityOffsetRun (bank)
open SharedPlacementAlphabet (setTape)
variable {a : ℕ}

def program := seq (ActivePrefixParityOffsetRun.program (a := a)) ActivePrefixParityOffsetCleanup.program
def input (hs : Fin 8 → List Bool) := bank (base (a := a) hs)
def output (s : Shape) (hs : Fin 8 → List Bool) := bank
  (setTape (base (a := a) hs) 16 (ActivePrefixOffsetStreamsCleanup.word (offsetWord s)) 0)
def cost (s : Shape) := ActivePrefixParityOffsetRun.cost s+1+ActivePrefixParityOffsetCleanup.cost s
def constant := ActivePrefixOffsetHeadersBudget.constant+2*BinaryPrefixFieldTableRun.constant+3000

theorem runs (s : Shape) (hs : Fin 8 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun v => v=input hs) (fun v => v=output s hs) (cost s) := by
  have h := (ActivePrefixParityOffsetRun.runs (a := a) s hs hv hc).seq
    (ActivePrefixParityOffsetCleanup.runs s hs)
  simpa only [program,input,output,cost,ActivePrefixParityOffsetCleanup.result_eq] using h

theorem cost_bound (s : Shape) : cost s≤constant*(2^s.W*(s.W+1)) := by
  let N := 2^s.W
  let V := N*(s.W+1)
  have hN : 1≤N := Nat.one_le_pow _ _ (by decide)
  have hV : 1≤V := Nat.mul_pos hN (by omega)
  have hsource : s.f*s.q≤s.W := by have := s.sourceFits; omega
  have htemp : s.n*s.b≤s.W := by
    have hm := Nat.mul_le_mul_left s.n (show s.b≤s.q by have := s.hbq; omega)
    have := s.tempFits
    omega
  have hf : 1≤s.f := by have := s.hnf; omega
  have hq : 1≤s.q := by have := s.hr; omega
  have hnq : s.n*s.q≤s.W :=
    (Nat.mul_le_mul_right s.q (by have := s.hnf; omega : s.n≤s.f)).trans hsource
  have hqW : s.q≤s.W := (Nat.le_mul_of_pos_left s.q hf).trans hsource
  have hbW : s.b≤s.W := by have := s.hbq; omega
  have hnW : s.n≤s.W := (Nat.le_mul_of_pos_right s.n hq).trans hnq
  have hW : s.W+1≤V := Nat.le_mul_of_pos_left _ hN
  have hs : N*(s.f*s.q)≤V := Nat.mul_le_mul_left N (by omega)
  have ht : N*(s.n*s.b)≤V := Nat.mul_le_mul_left N (by omega)
  have hn : N*s.n≤V := Nat.mul_le_mul_left N (by omega)
  have hv : N*(s.n*s.q)≤V := Nat.mul_le_mul_left N (by omega)
  have hstride : s.n*(s.q+s.b+1)≤3*s.W := by nlinarith
  have hsmall : s.q+s.b+1≤3*(s.W+1) := by omega
  have hlarge : (N*s.n+1)*(s.q+s.b+1)≤6*V := by
    have hm := Nat.mul_le_mul_left N hstride
    dsimp only [V] at hW ⊢
    nlinarith
  have hh := ActivePrefixOffsetHeadersCleanup.derived_cost s.W s.q s.b s.n s.f hq s.hnf hsource htemp
  change ActivePrefixOffsetHeadersCleanup.cost (ActivePrefixOffsetHeadersData.words s.W s.q s.b s.n s.f)≤44*V at hh
  unfold cost ActivePrefixParityOffsetRun.cost ActivePrefixParityOffsetCleanup.cost
    ActivePrefixParityOffsetCleanup.streamCost constant
  simp only [tempWord,sourceWord,controlWord,offsetWord,BinaryPrefixFieldTableData.word_length,
    SelectedSourceBitsStreamData.selected_length,ActivePrefixParityOffsetData.offsets_length]
  change ActivePrefixOffsetHeadersBudget.constant*V+2*(BinaryPrefixFieldTableRun.constant*V)+
    400*(N*(s.f*s.q)+1)+320*((N*s.n+1)*(s.q+s.b+1))+4+1+
    (N*(s.n*s.q)+N*s.n+2*(N*(s.f*s.q))+N*(s.n*s.b)+12+1+
      ActivePrefixOffsetHeadersCleanup.cost (ActivePrefixOffsetHeadersData.words s.W s.q s.b s.n s.f))≤
    (ActivePrefixOffsetHeadersBudget.constant+2*BinaryPrefixFieldTableRun.constant+3000)*V
  nlinarith

/-- One dimension-independent finite machine generates the exact parity-XOR load
offset word and restores all metadata/source streams in linear table volume. -/
theorem runs_linear (s : Shape) (hs : Fin 8 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun v => v=input hs) (fun v => v=output s hs)
      (constant*(2^s.W*(s.W+1))) :=
  (runs s hs hv hc).consequence (fun _ h => h) (fun _ h => h) (cost_bound s)

end
end IntegerMultBounds.Machine.ActivePrefixParityOffset
