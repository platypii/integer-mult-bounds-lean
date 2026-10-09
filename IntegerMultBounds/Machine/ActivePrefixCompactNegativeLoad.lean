import IntegerMultBounds.Machine.ActivePrefixCompactNegativeLoadCleanup

/-! Complete compact negative parity-XOR load from original prefix/gadget descriptors, original
rows and suffix width, and the original full array. Offset production, repeat,
rotation, all descriptor synthesis and all cleanup are real paid executions. -/
namespace IntegerMultBounds.Machine.ActivePrefixCompactNegativeLoad
noncomputable section
open ActivePrefixCompactNegativeLoadData
open ActivePrefixCompactNegativeLoadHeaders (bank)
open ActivePrefixParityOffsetBank (Shape values)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

def program := seq (ActivePrefixCompactNegativeLoadRun.program (a := a)) (ActivePrefixCompactNegativeLoadCleanup.program (a := a))
def cost (s : Shape) (rows B : ℕ) := ActivePrefixCompactNegativeLoadRun.cost s rows B+1+
  ActivePrefixCompactNegativeLoadCleanup.cost s rows
def result (s : Shape) (rows B : ℕ) (x : Array s rows B) : Array s rows B :=
  PackedOffsetPayloadArray.array (offsets s rows) (width s) (prefixCount s rows) B x

theorem runs (s : Shape) (rows B : ℕ) (hrows : 0<rows) (hB : 0<B)
    (hs : Fin 8 → List Bool) (rs bs : List Bool) (x : Array s rows B)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs)
    (hb : Counter.value bs=B) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (program (a := a)) (fun v => v=bank (base s rows B hs rs bs x))
      (fun v => v=bank (base s rows B hs rs bs (result s rows B x))) (cost s rows B) :=
  (ActivePrefixCompactNegativeLoadRun.runs s rows B hrows hB hs rs bs x hv hc hr cr hb cb).seq
    (ActivePrefixCompactNegativeLoadCleanup.runs s rows B hs rs bs x)

def constant := ActivePrefixParityNegative.constant+ActivePrefixOffsetHeadersBudget.constant+44+
  ActiveTargetRotation.constant+300

/-- Explicit geometry absorbs prefix-table construction into the full volume.
There is no bound on the target width and no positive-target-width premise. -/
theorem cost_bound (s : Shape) (rows B : ℕ) (hrows : 0<rows) (hB : 0<B)
    (habs : s.W+1≤2^width s*B) : cost s rows B≤constant*volume s rows B := by
  let T := 2^s.W*(s.W+1)
  let V := volume s rows B
  have hT : T≤V := by
    have h₁ := Nat.mul_le_mul_left (2^s.W) habs
    have h₂ := Nat.le_mul_of_pos_left (2^s.W*(2^width s*B)) hrows
    dsimp only [T,V]
    unfold volume prefixCount
    nlinarith only [h₁,h₂]
  have hV : 1≤V := by
    have hvpos : 0<V := by dsimp only [V]; unfold volume prefixCount; positivity
    omega
  have hP : prefixCount s rows≤V := by
    dsimp only [V]
    unfold volume
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hnq : width s≤s.W := by
    have hsource : s.f*s.q≤s.W := by have := s.sourceFits; omega
    have hn : s.n≤s.f := by have := s.hnf; omega
    exact (Nat.mul_le_mul_left s.n (show s.b≤s.q by have := s.hbq; omega)).trans
      ((Nat.mul_le_mul_right s.q hn).trans hsource)
  have hbase : (offsetWord s).length≤V := by
    have ht := Nat.mul_le_mul_left (2^s.W) (by omega : width s≤s.W+1)
    simp only [offsetWord,ActivePrefixParityNegativeData.negative_length]
    change 2^s.W*width s≤V
    dsimp only [T] at hT
    omega
  have hrepeated : (offsets s rows).length≤V := by
    rw [offsets_length]
    have hw : width s≤2^width s*B :=
      ((show width s<2^width s from Nat.lt_two_pow_self)).le.trans (Nat.le_mul_of_pos_right _ hB)
    exact Nat.mul_le_mul_left _ hw
  have hheaders := ActivePrefixOffsetHeadersCleanup.derived_cost s.W s.q s.b s.n s.f
    (by have := s.hr; omega) s.hnf (by have := s.sourceFits; omega) (by have := s.tempFits; have hm := Nat.mul_le_mul_left s.n (show s.b≤s.q by have := s.hbq; omega); omega)
  change ActivePrefixOffsetHeadersCleanup.cost (ActivePrefixOffsetHeadersData.words s.W s.q s.b s.n s.f)≤44*T at hheaders
  have hp : 0<prefixCount s rows := by unfold prefixCount; positivity
  have hbits : (bits (prefixCount s rows)).length≤2*prefixCount s rows := by
    have h := GrowingCounterData.canonical_width (bits (prefixCount s rows)) (RecursiveChildQuotientsConstant.bits_canonical _)
    rw [RecursiveChildQuotientsConstant.bits_value] at h
    have hl := Nat.log2_le_self (prefixCount s rows)
    omega
  have hC := Nat.mul_le_mul_left (ActivePrefixParityNegative.constant+ActivePrefixOffsetHeadersBudget.constant+44) hT
  have hrep : rows*(offsetWord s).length=(offsets s rows).length := by
    simp only [offsets,BinaryAddressOffsetRepeatData.copies_length]
  unfold cost ActivePrefixCompactNegativeLoadRun.cost ActivePrefixCompactNegativeLoadHeaders.cost
    ActivePrefixCompactNegativeLoadCleanup.cost constant
  rw [hrep]
  change ActivePrefixParityNegative.constant*T+
    (ActivePrefixOffsetHeadersBudget.constant*T+53*prefixCount s rows+29)+
    54*((offsets s rows).length+1)+ActiveTargetRotation.constant*V+3+1+
    (2*(offsetWord s).length+3+2*(offsets s rows).length+3+
      ActivePrefixOffsetHeadersCleanup.cost (ActivePrefixOffsetHeadersData.words s.W s.q s.b s.n s.f)+
      (2*(bits (prefixCount s rows)).length+4)+3)≤
    (ActivePrefixParityNegative.constant+ActivePrefixOffsetHeadersBudget.constant+44+
      ActiveTargetRotation.constant+300)*V
  nlinarith only [hC,hbase,hrepeated,hheaders,hbits,hP,hV]

/-- One fixed program consumes only original descriptors, retaining them and
restoring every auxiliary cell, in linear full-array volume under absorption. -/
theorem runs_linear (s : Shape) (rows B : ℕ) (hrows : 0<rows) (hB : 0<B)
    (habs : s.W+1≤2^width s*B)
    (hs : Fin 8 → List Bool) (rs bs : List Bool) (x : Array s rows B)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs)
    (hb : Counter.value bs=B) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (program (a := a)) (fun v => v=bank (base s rows B hs rs bs x))
      (fun v => v=bank (base s rows B hs rs bs (result s rows B x))) (constant*volume s rows B) :=
  (runs s rows B hrows hB hs rs bs x hv hc hr cr hb cb).consequence
    (fun _ h => h) (fun _ h => h) (cost_bound s rows B hrows hB habs)

theorem entry (s : Shape) (rows B : ℕ) (x : Array s rows B)
    (p : Fin (prefixCount s rows)) (v : Fin (2^width s)) (j : Fin B) :
    result s rows B x (FiberLayoutData.index p
      ⟨(v.val+PackedOffsetPayloadValue.offset (offsets s rows) (width s) p.val)%2^width s,
        Nat.mod_lt _ (by positivity)⟩ j)=x (FiberLayoutData.index p v j) :=
  ActiveTargetRotation.entry (offsets s rows) (width s) (prefixCount s rows) B (offsets_length s rows) x p v j

theorem result_frame (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) (i : Fin 75) (hi : i.val≠10) :
    (bank (base (a := a) s rows B hs rs bs (result s rows B x))).head i=
      (bank (base (a := a) s rows B hs rs bs x)).head i ∧
    (bank (base (a := a) s rows B hs rs bs (result s rows B x))).tape i=
      (bank (base (a := a) s rows B hs rs bs x)).tape i := by
  induction i using Fin.addCases (m := 19) (n := 56) with
  | left i =>
    change i.val≠10 at hi
    simp only [bank,CleanSubbank.bank,Tapes.append,Fin.addCases_left,base]
    simp only [hi,↓reduceIte]
    exact ⟨trivial,trivial⟩
  | right i =>
    simp only [bank,CleanSubbank.bank,Tapes.append,Fin.addCases_right]
    exact ⟨trivial,trivial⟩

theorem result_blank (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) (i : Fin 75) (hi : (11 : ℕ) ≤ i.val) :
    (bank (base (a := a) s rows B hs rs bs (result s rows B x))).head i=0 ∧
    (bank (base (a := a) s rows B hs rs bs (result s rows B x))).tape i=fun _ => blank := by
  induction i using Fin.addCases (m := 19) (n := 56) with
  | left i =>
    change 11 ≤ i.val at hi
    have h8 : ¬i.val<8 := by omega
    have h9 : i.val≠8 := by omega
    have h10 : i.val≠9 := by omega
    have h11 : i.val≠10 := by omega
    have hhead : ¬i.val<10 := by omega
    simp only [bank,CleanSubbank.bank,Tapes.append,Fin.addCases_left,base,h8,h9,h10,h11,hhead,↓reduceDIte,↓reduceIte]
    exact ⟨trivial,trivial⟩
  | right i =>
    simp only [bank,CleanSubbank.bank,Tapes.append,Fin.addCases_right,SharedBank.empty]
    exact ⟨trivial,trivial⟩

theorem result_payload (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) :
    (bank (base (a := a) s rows B hs rs bs (result s rows B x))).head (10 : Fin 75)=0 ∧
    (bank (base (a := a) s rows B hs rs bs (result s rows B x))).tape (10 : Fin 75)=
      ActiveTargetRotation.word (result s rows B x) := by
  exact ⟨rfl,rfl⟩

end
end IntegerMultBounds.Machine.ActivePrefixCompactNegativeLoad
