import IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativePureLoadCleanup

/-! Four complete dirty-U physical load modes. Only original layout, row and
suffix descriptors and the full array enter; all offset streams and dimensions
are physically produced and erased. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativePureLoad
noncomputable section
open ActivePrefixDirtyControlLoadProducer (values width)
open ActivePrefixDirtyControlNegativePureData (negative)
open ActivePrefixDirtyControlLoadData (Array base volume prefixCount)
open ActivePrefixDirtyControlNegativePureLoadData
open ActivePrefixDirtyControlLoadHeaders (bank)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

def program := seq (ActivePrefixDirtyControlNegativePureLoadRun.program (a := a)) ActivePrefixDirtyControlNegativePureLoadCleanup.program
def cost (s : Shape) (rows B : ℕ) := ActivePrefixDirtyControlNegativePureLoadRun.cost s rows B+1+
  ActivePrefixDirtyControlNegativePureLoadCleanup.cost s rows
def result (s : Shape) (rows B : ℕ) (x : Array s rows B) : Array s rows B :=
  PackedOffsetPayloadArray.array (offsets s rows) (width s) (prefixCount s rows) B x

theorem runs (s : Shape) (rows B : ℕ) (hrows : 0<rows) (hB : 0<B)
    (hs : Fin 6 → List Bool) (rs bs : List Bool) (x : Array s rows B)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs)
    (hb : Counter.value bs=B) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (program (a := a)) (fun v => v=bank (base s rows B hs rs bs x))
      (fun v => v=bank (base s rows B hs rs bs (result s rows B x))) (cost s rows B) :=
  (ActivePrefixDirtyControlNegativePureLoadRun.runs s rows B hrows hB hs rs bs x hv hc hr cr hb cb).seq
    (ActivePrefixDirtyControlNegativePureLoadCleanup.runs s rows B hs rs bs x)

def constant := ActivePrefixDirtyControlLoadProducer.constant+FixedBasePowerDescriptor.constant 2+
  ActiveTargetRotation.constant+800

theorem width_le (s : Shape) : width s≤s.n*s.q := ActivePrefixDirtyControlLoad.width_le s

/-- The table bound's wide-target term is retained explicitly in absorption;
compact source fit does not silently impose a wide source-padding requirement. -/
theorem cost_bound (s : Shape) (rows B : ℕ) (hrows : 0<rows) (hB : 0<B)
    (habs : s.W+s.n*s.q+s.q+s.b+1≤2^width s*B) : cost s rows B≤constant*volume s rows B := by
  let T := ActivePrefixDirtyControl.volume s
  let V := volume s rows B
  have hT : T≤V := by
    have h₁ := Nat.mul_le_mul_left (2^s.W) habs
    have h₂ := Nat.le_mul_of_pos_left (2^s.W*(2^width s*B)) hrows
    dsimp only [T,V]
    unfold ActivePrefixDirtyControl.volume volume prefixCount
    nlinarith only [h₁,h₂]
  have hV : 0<V := by dsimp only [V]; unfold volume prefixCount; positivity
  have hpow : 1≤2^s.W := Nat.one_le_pow _ _ (by decide)
  have hPT : 2^s.W≤T := Nat.le_mul_of_pos_right _ (by omega)
  have hPV : 2^s.W≤V := hPT.trans hT
  have hwT : 2^s.W*width s≤T := Nat.mul_le_mul_left _ (by have := width_le s; omega)
  have hwV : width s≤V := (Nat.le_mul_of_pos_left _ hpow).trans (hwT.trans hT)
  have hP : prefixCount s rows≤V := Nat.le_mul_of_pos_right _ (by positivity)
  have hbase : (negative s).length≤V := by rw [ActivePrefixDirtyControlNegativePureData.negative_length s]; exact hwT.trans hT
  have hrepeated : (offsets s rows).length≤V := by
    rw [offsets_length]
    have hw : width s≤2^width s*B :=
      (Nat.lt_two_pow_self (n := width s)).le.trans (Nat.le_mul_of_pos_right _ hB)
    exact Nat.mul_le_mul_left _ hw
  have hlP := CompactGadgetReservationHeadersCost.length_bound (bits (2^s.W))
    (RecursiveChildQuotientsConstant.bits_canonical _) V (by rw [RecursiveChildQuotientsConstant.bits_value]; exact hPV) hV
  have hlW := CompactGadgetReservationHeadersCost.length_bound (bits (width s))
    (RecursiveChildQuotientsConstant.bits_canonical _) V (by rw [RecursiveChildQuotientsConstant.bits_value]; exact hwV) hV
  have hlN := CompactGadgetReservationHeadersCost.length_bound (bits (prefixCount s rows))
    (RecursiveChildQuotientsConstant.bits_canonical _) V (by rw [RecursiveChildQuotientsConstant.bits_value]; exact hP) hV
  have hneg : 2^s.W*(width s+1)≤2*V := by nlinarith only [hwT,hPV,hT]
  have hproduce := Nat.mul_le_mul_left ActivePrefixDirtyControlLoadProducer.constant hT
  have hpower := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hPV
  have hrep : rows*(negative s).length=(offsets s rows).length := by simp only [offsets,BinaryAddressOffsetRepeatData.copies_length]
  unfold cost ActivePrefixDirtyControlNegativePureLoadRun.cost ActivePrefixDirtyControlLoadHeaders.cost
    ActivePrefixDirtyControlNegativePureLoadCleanup.cost constant
  rw [hrep]
  change ActivePrefixDirtyControlLoadProducer.constant*T+
    (FixedBasePowerDescriptor.constant 2*2^s.W+(53*width s+28)+(53*prefixCount s rows+28)+2)+
    120*(2^s.W*(width s+1))+54*((offsets s rows).length+1)+ActiveTargetRotation.constant*V+4+1+
    (2*(negative s).length+2*(offsets s rows).length+2*(bits (2^s.W)).length+
      2*(bits (width s)).length+2*(bits (prefixCount s rows)).length+22)≤
    (ActivePrefixDirtyControlLoadProducer.constant+FixedBasePowerDescriptor.constant 2+ActiveTargetRotation.constant+800)*V
  nlinarith only [hproduce,hpower,hbase,hrepeated,hlP,hlW,hlN,hP,hwV,hV,hneg]

theorem runs_linear (s : Shape) (rows B : ℕ) (hrows : 0<rows) (hB : 0<B)
    (habs : s.W+s.n*s.q+s.q+s.b+1≤2^width s*B)
    (hs : Fin 6 → List Bool) (rs bs : List Bool) (x : Array s rows B)
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

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativePureLoad
