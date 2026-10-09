import IntegerMultBounds.Machine.SliceExponentPowers
import IntegerMultBounds.Machine.ArbitraryWidthPieces
import IntegerMultBounds.Machine.RecursiveHeaderBounds

/-! Runtime construction of the enlarged spectator dimensions for an arbitrary
digit interval. All powers, differences and products are computed on tape;
the only retained new descriptors are the three actual slice dimensions. -/
namespace IntegerMultBounds.Machine.ArbitrarySliceDimensions
open RecursiveInterchangeLayout (Descriptor volume)
variable {q : ℕ} (hq : 2 ≤ q)
noncomputable section

def bank (hs : Fin 6 → List Bool) (ts bs : List Bool) (ds : Fin 6 → Option (List Bool)) : Tapes 17 q :=
  ⟨![1,1,1,1,1,1,1,1,RecursiveDimensionBank.head (ds 0),RecursiveDimensionBank.head (ds 1),
      RecursiveDimensionBank.head (ds 2),RecursiveDimensionBank.head (ds 3),
      RecursiveDimensionBank.head (ds 4),RecursiveDimensionBank.head (ds 5),0,0,0],
   ![RadixZeroFill.encodedBinary (hs 0),RadixZeroFill.encodedBinary (hs 1),
     RadixZeroFill.encodedBinary (hs 2),RadixZeroFill.encodedBinary (hs 3),
     RadixZeroFill.encodedBinary (hs 4),RadixZeroFill.encodedBinary (hs 5),
     RadixZeroFill.encodedBinary ts,RadixZeroFill.encodedBinary bs,
     RecursiveDimensionBank.tape (ds 0),RecursiveDimensionBank.tape (ds 1),
     RecursiveDimensionBank.tape (ds 2),RecursiveDimensionBank.tape (ds 3),
     RecursiveDimensionBank.tape (ds 4),RecursiveDimensionBank.tape (ds 5),
     fun _ => blank,fun _ => blank,fun _ => blank]⟩

def stage (hs : Fin 6 → List Bool) (ts bs : List Bool) (xs : Fin 6 → List Bool) (k : ℕ) : Tapes 17 q :=
  bank hs ts bs (fun i => if i.val < k then some (xs i) else none)

def input (hs : Fin 6 → List Bool) (ts bs : List Bool) : Tapes 17 q := bank hs ts bs (fun _ => none)

def beforeBits (v : Descriptor) (t : ℕ) := DimensionProductDescriptor.bits v.beforeH (q^t)
def middleBits (v : Descriptor) (t b : ℕ) := DimensionProductDescriptor.bits (q^(v.width-t-b)) v.between
def betweenBits (v : Descriptor) (t b : ℕ) := DimensionProductDescriptor.bits ((q^(v.width-t-b))*v.between) (q^t)
def afterBits (v : Descriptor) (t b : ℕ) := DimensionProductDescriptor.bits (q^(v.width-t-b)) v.afterD

def words (v : Descriptor) (t b : ℕ) : Fin 6 → List Bool :=
  ![RadixPowerDescriptor.bits hq t,RadixPowerDescriptor.bits hq (v.width-t-b),
    beforeBits (q := q) v t,middleBits (q := q) v t b,betweenBits (q := q) v t b,afterBits (q := q) v t b]

def output (hs : Fin 6 → List Bool) (ts bs : List Bool) (v : Descriptor) (t b : ℕ) : Tapes 17 q :=
  bank hs ts bs ![none,none,some (beforeBits (q := q) v t),none,
    some (betweenBits (q := q) v t b),some (afterBits (q := q) v t b)]

def powersPlacement : Fin (9+8) ≃ Fin 17 where
  toFun := ![3,6,7,10,11,8,9,14,15,0,1,2,4,5,12,13,16]
  invFun := ![9,10,11,0,12,13,1,2,5,6,3,4,14,15,7,8,16]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def powersProgram := Placement.placed (SliceExponentPowers.program hq) powersPlacement

def beforePlacement : Fin (6+11) ≃ Fin 17 where
  toFun := ![14,10,15,8,16,2,0,1,3,4,5,6,7,9,11,12,13]
  invFun := ![6,7,5,8,9,10,11,12,3,13,1,14,15,16,0,2,4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def beforeProgram := Placement.placed (DimensionProductDescriptor.program (q := q)) beforePlacement

def middlePlacement : Fin (6+11) ≃ Fin 17 where
  toFun := ![14,11,15,4,16,9,0,1,2,3,5,6,7,8,10,12,13]
  invFun := ![6,7,8,9,3,10,11,12,13,5,14,1,15,16,0,2,4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def middleProgram := Placement.placed (DimensionProductDescriptor.program (q := q)) middlePlacement

def betweenPlacement : Fin (6+11) ≃ Fin 17 where
  toFun := ![14,12,15,8,16,11,0,1,2,3,4,5,6,7,9,10,13]
  invFun := ![6,7,8,9,10,11,12,13,3,14,15,5,1,16,0,2,4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def betweenProgram := Placement.placed (DimensionProductDescriptor.program (q := q)) betweenPlacement

def afterPlacement : Fin (6+11) ≃ Fin 17 where
  toFun := ![14,13,15,5,16,9,0,1,2,3,4,6,7,8,10,11,12]
  invFun := ![6,7,8,9,10,3,11,12,13,5,14,15,16,1,0,2,4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def afterProgram := Placement.placed (DimensionProductDescriptor.program (q := q)) afterPlacement

private def cleanSlots : List (Fin 17) := [8,9,11]
def cleanProgram := BinaryDescriptorCleanupList.program (a := q) (by decide : 0 < 17) cleanSlots

def program := seq (seq (seq (seq (seq (powersProgram hq) beforeProgram) middleProgram) betweenProgram) afterProgram) cleanProgram

private theorem placed_exact {s u t r cost : ℕ} {M : Program s r q}
    (e : Fin (s+u) ≃ Fin t) (v w : Tapes t q) (small small' : Tapes s q)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

private theorem powers_hoare (hs : Fin 6 → List Bool) (ts bs : List Bool) (v : Descriptor) (t b V : ℕ)
    (he : Counter.value (hs 3) = v.width) (ht : Counter.value ts = t) (hb : Counter.value bs = b)
    (hfit : t+b ≤ v.width) (hV : 0 < V) (hQ : q^v.width ≤ V)
    (we : (hs 3).length ≤ 2*V) (wt : ts.length ≤ 2*V) (wb : bs.length ≤ 2*V) :
    HoareTime (powersProgram hq) (fun z => z = input hs ts bs)
      (fun z => z = stage hs ts bs (words hq v t b) 2) (300*V) := by
  apply placed_exact powersPlacement _ _ _ _ _ _ _
    (SliceExponentPowers.construct_hoare hq (hs 3) ts bs v.width t b V he ht hb hfit hV hQ we wt wb)
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [powersPlacement,input,stage,bank,words]

private theorem before_hoare (hs : Fin 6 → List Bool) (ts bs : List Bool) (xs : Fin 6 → List Bool)
    (N W : ℕ) (hn : Counter.value (hs 2) = N) (hw : Counter.value (xs 0) = W)
    (cn : GrowingCounterData.Canonical (hs 2)) (cw : GrowingCounterData.Canonical (xs 0)) (hW : 0 < W)
    (hx : xs 2 = DimensionProductDescriptor.bits N W) :
    HoareTime (beforeProgram (q := q)) (fun z => z = stage hs ts bs xs 2)
      (fun z => z = stage hs ts bs xs 3) (53*(N*W)+28) := by
  apply placed_exact beforePlacement _ _ _ _ _ _ _
    (DimensionProductDescriptor.construct_hoare (xs 0) (hs 2) N W hW hw hn cw cn)
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [beforePlacement,stage,bank,RecursiveDimensionBank.head,RecursiveDimensionBank.tape,hx]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [beforePlacement,stage,bank]

private theorem middle_hoare (hs : Fin 6 → List Bool) (ts bs : List Bool) (xs : Fin 6 → List Bool)
    (N W : ℕ) (hn : Counter.value (xs 1) = N) (hw : Counter.value (hs 4) = W)
    (cn : GrowingCounterData.Canonical (xs 1)) (cw : GrowingCounterData.Canonical (hs 4)) (hW : 0 < W)
    (hx : xs 3 = DimensionProductDescriptor.bits N W) :
    HoareTime (middleProgram (q := q)) (fun z => z = stage hs ts bs xs 3)
      (fun z => z = stage hs ts bs xs 4) (53*(N*W)+28) := by
  apply placed_exact middlePlacement _ _ _ _ _ _ _
    (DimensionProductDescriptor.construct_hoare (hs 4) (xs 1) N W hW hw hn cw cn)
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [middlePlacement,stage,bank,RecursiveDimensionBank.head,RecursiveDimensionBank.tape,hx]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [middlePlacement,stage,bank]

private theorem between_hoare (hs : Fin 6 → List Bool) (ts bs : List Bool) (xs : Fin 6 → List Bool)
    (N W : ℕ) (hn : Counter.value (xs 3) = N) (hw : Counter.value (xs 0) = W)
    (cn : GrowingCounterData.Canonical (xs 3)) (cw : GrowingCounterData.Canonical (xs 0)) (hW : 0 < W)
    (hx : xs 4 = DimensionProductDescriptor.bits N W) :
    HoareTime (betweenProgram (q := q)) (fun z => z = stage hs ts bs xs 4)
      (fun z => z = stage hs ts bs xs 5) (53*(N*W)+28) := by
  apply placed_exact betweenPlacement _ _ _ _ _ _ _
    (DimensionProductDescriptor.construct_hoare (xs 0) (xs 3) N W hW hw hn cw cn)
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [betweenPlacement,stage,bank,RecursiveDimensionBank.head,RecursiveDimensionBank.tape,hx]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [betweenPlacement,stage,bank]

private theorem after_hoare (hs : Fin 6 → List Bool) (ts bs : List Bool) (xs : Fin 6 → List Bool)
    (N W : ℕ) (hn : Counter.value (xs 1) = N) (hw : Counter.value (hs 5) = W)
    (cn : GrowingCounterData.Canonical (xs 1)) (cw : GrowingCounterData.Canonical (hs 5)) (hW : 0 < W)
    (hx : xs 5 = DimensionProductDescriptor.bits N W) :
    HoareTime (afterProgram (q := q)) (fun z => z = stage hs ts bs xs 5)
      (fun z => z = stage hs ts bs xs 6) (53*(N*W)+28) := by
  apply placed_exact afterPlacement _ _ _ _ _ _ _
    (DimensionProductDescriptor.construct_hoare (hs 5) (xs 1) N W hW hw hn cw cn)
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [afterPlacement,stage,bank,RecursiveDimensionBank.head,RecursiveDimensionBank.tape,hx]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [afterPlacement,stage,bank]

private theorem clean_hoare (hs : Fin 6 → List Bool) (ts bs : List Bool) (xs : Fin 6 → List Bool) :
    HoareTime (cleanProgram (q := q)) (fun z => z = stage hs ts bs xs 6)
      (fun z => z = bank hs ts bs ![none,none,some (xs 2),none,some (xs 4),some (xs 5)])
      (2*((xs 0).length+(xs 1).length+(xs 3).length)+15) := by
  let ws : Fin 17 → List Bool := fun i => if i = 8 then xs 0 else if i = 9 then xs 1 else xs 3
  have h := BinaryDescriptorCleanupList.cleanup_hoare (by decide : 0 < 17) cleanSlots (by decide)
    ws (stage (q := q) hs ts bs xs 6) (by
      intro i hi
      simp only [cleanSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl <;> constructor <;>
        first | rfl | simpa [ws,stage,bank,RecursiveDimensionBank.tape] using
          (BinaryDescriptorStackRoundtrip.descriptor_encoded (a := q) _).symm)
  apply h.consequence (fun _ h => h) _ _
  · rintro z rfl
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · simp [BinaryDescriptorCleanupList.cost,cleanSlots,ws]
    omega

private theorem length_le (xs : List Bool) (V : ℕ) (hV : 0 < V)
    (hc : GrowingCounterData.Canonical xs) (hv : Counter.value xs ≤ V) : xs.length ≤ 2*V := by
  have h := GrowingCounterData.canonical_width xs hc
  have l := Nat.log2_le_self (Counter.value xs)
  omega

/-- Values agree exactly with the semantic spectator view, in its original
multiplication order. The selected width remains on the original input tape. -/
theorem words_value (v : Descriptor) (t b : ℕ) :
    Counter.value (words hq v t b 0) = q^t ∧
    Counter.value (words hq v t b 1) = q^(v.width-t-b) ∧
    Counter.value (words hq v t b 2) = (ArbitraryWidthPieces.slice q v t b).beforeH ∧
    Counter.value (words hq v t b 3) = q^(v.width-t-b)*v.between ∧
    Counter.value (words hq v t b 4) = (ArbitraryWidthPieces.slice q v t b).between ∧
    Counter.value (words hq v t b 5) = (ArbitraryWidthPieces.slice q v t b).afterD := by
  exact ⟨RadixPowerDescriptor.bits_value _ _,RadixPowerDescriptor.bits_value _ _,
    DimensionProductDescriptor.bits_value _ _,DimensionProductDescriptor.bits_value _ _,
    DimensionProductDescriptor.bits_value _ _,DimensionProductDescriptor.bits_value _ _⟩

theorem words_canonical (v : Descriptor) (t b : ℕ) (i : Fin 6) :
    GrowingCounterData.Canonical (words hq v t b i) := by
  fin_cases i <;> first | exact RadixPowerDescriptor.bits_canonical _ _ | exact DimensionProductDescriptor.bits_canonical _ _

private theorem power_le (hq : 2 ≤ q) (v : Descriptor) (hp : v.Positive) : q^v.width ≤ volume q v := by
  have hQ : 0 < q^v.width := pow_pos (by omega) _
  have hpref : 0 < v.beforeRows*v.rows*v.beforeH := Nat.mul_pos (Nat.mul_pos hp.1 hp.2.1) hp.2.2.1
  have h := Nat.le_mul_of_pos_right (v.beforeRows*v.rows*v.beforeH*q^v.width)
    (Nat.mul_pos hp.2.2.2.1 (Nat.mul_pos hQ hp.2.2.2.2))
  have hn : v.beforeRows*v.rows*v.beforeH*q^v.width ≤ volume q v := by
    convert h using 1
    unfold volume
    ring
  exact (Nat.le_mul_of_pos_left _ hpref).trans hn

/-- Paid slice-header arithmetic from exactly eight original input descriptors.
No temporary powers, differences, intermediate products or markers survive. -/
theorem construct_hoare (hs : Fin 6 → List Bool) (ts bs : List Bool) (v : Descriptor) (t b : ℕ)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive)
    (ht : Counter.value ts = t) (hb : Counter.value bs = b)
    (ct : GrowingCounterData.Canonical ts) (cb : GrowingCounterData.Canonical bs)
    (hfit : t+b ≤ v.width) :
    HoareTime (program hq) (fun z => z = input hs ts bs)
      (fun z => z = output hs ts bs v t b) (700*volume q v) := by
  let V := volume q v
  let xs := words hq v t b
  have hQ := power_le hq v hp
  have hV : 0 < V := lt_of_lt_of_le (pow_pos (by omega : 0 < q) _) hQ
  have hw : v.width ≤ V := RecursiveHeaderBounds.values_le_volume hq v hp 3
  have hslen : (hs 3).length ≤ 2*V := length_le _ _ hV (hv.2 3) (by rw [hv.1 3]; exact hw)
  have htlen : ts.length ≤ 2*V := length_le _ _ hV ct (by omega)
  have hblen : bs.length ≤ 2*V := length_le _ _ hV cb (by omega)
  have hpt : 0 < q^t := pow_pos (by omega) _
  have hps : 0 < q^(v.width-t-b) := pow_pos (by omega) _
  obtain ⟨v0,v1,v2,v3,v4,v5⟩ := words_value hq v t b
  have hc (i : Fin 6) : GrowingCounterData.Canonical (xs i) := words_canonical hq v t b i
  have h := (((((powers_hoare hq hs ts bs v t b V (hv.1 3) ht hb hfit hV hQ hslen htlen hblen).seq
    (before_hoare hs ts bs xs v.beforeH (q^t) (hv.1 2) v0 (hv.2 2) (hc 0) hpt rfl)).seq
    (middle_hoare hs ts bs xs (q^(v.width-t-b)) v.between v1 (hv.1 4) (hc 1) (hv.2 4) hp.2.2.2.1 rfl)).seq
    (between_hoare hs ts bs xs (q^(v.width-t-b)*v.between) (q^t) v3 v0 (hc 3) (hc 0) hpt rfl)).seq
    (after_hoare hs ts bs xs (q^(v.width-t-b)) v.afterD v1 (hv.1 5) (hc 1) (hv.2 5) hp.2.2.2.2 rfl)).seq
    (clean_hoare hs ts bs xs)
  have hslice := ArbitraryWidthPieces.slice_positive q (by omega) v hp t b
  have hvol := ArbitraryWidthPieces.slice_volume q v t b hfit
  have hbefore : v.beforeH*q^t ≤ V := by
    have hh := RecursiveHeaderBounds.values_le_volume hq _ hslice 2
    rw [hvol] at hh
    exact hh
  have hbetween : q^(v.width-t-b)*v.between*q^t ≤ V := by
    have hh := RecursiveHeaderBounds.values_le_volume hq _ hslice 4
    rw [hvol] at hh
    exact hh
  have hafter : q^(v.width-t-b)*v.afterD ≤ V := by
    have hh := RecursiveHeaderBounds.values_le_volume hq _ hslice 5
    rw [hvol] at hh
    exact hh
  have hmid : q^(v.width-t-b)*v.between ≤ V :=
    (Nat.le_mul_of_pos_right _ hpt).trans hbetween
  have hp0 : q^t ≤ V := (Nat.pow_le_pow_right (by omega) (by omega : t ≤ v.width)).trans hQ
  have hp1 : q^(v.width-t-b) ≤ V :=
    (Nat.pow_le_pow_right (by omega) (by omega : v.width-t-b ≤ v.width)).trans hQ
  have w0 : (xs 0).length ≤ 2*V := length_le _ _ hV (hc 0) (v0.trans_le hp0)
  have w1 : (xs 1).length ≤ 2*V := length_le _ _ hV (hc 1) (v1.trans_le hp1)
  have w3 : (xs 3).length ≤ 2*V := length_le _ _ hV (hc 3) (v3.trans_le hmid)
  apply h.consequence (fun _ h => h) (fun _ h => h) _
  change _ ≤ 700*V
  omega

/-- Logical target for the separately charged header-installation wrapper. -/
def headers (hs : Fin 6 → List Bool) (bs : List Bool) (v : Descriptor) (t b : ℕ) : Fin 6 → List Bool :=
  ![hs 0,hs 1,beforeBits (q := q) v t,bs,betweenBits (q := q) v t b,afterBits (q := q) v t b]

theorem headers_valid (hs : Fin 6 → List Bool) (bs : List Bool) (v : Descriptor) (t b : ℕ)
    (hv : RecursiveDimensionBank.Headers v hs) (hb : Counter.value bs = b)
    (cb : GrowingCounterData.Canonical bs) :
    RecursiveDimensionBank.Headers (ArbitraryWidthPieces.slice q v t b) (headers (q := q) hs bs v t b) := by
  constructor
  · intro i
    fin_cases i
    · exact hv.1 0
    · exact hv.1 1
    · exact DimensionProductDescriptor.bits_value _ _
    · exact hb
    · exact DimensionProductDescriptor.bits_value _ _
    · exact DimensionProductDescriptor.bits_value _ _
  · intro i
    fin_cases i
    · exact hv.2 0
    · exact hv.2 1
    · exact DimensionProductDescriptor.bits_canonical _ _
    · exact cb
    · exact DimensionProductDescriptor.bits_canonical _ _
    · exact DimensionProductDescriptor.bits_canonical _ _

/-- Positions of the three newly synthesized descriptors. -/
theorem ready (hs : Fin 6 → List Bool) (ts bs : List Bool) (v : Descriptor) (t b : ℕ) :
    (output (q := q) hs ts bs v t b).head 10 = 1 ∧
    (output (q := q) hs ts bs v t b).tape 10 = RadixZeroFill.encodedBinary (beforeBits (q := q) v t) ∧
    (output (q := q) hs ts bs v t b).head 12 = 1 ∧
    (output (q := q) hs ts bs v t b).tape 12 = RadixZeroFill.encodedBinary (betweenBits (q := q) v t b) ∧
    (output (q := q) hs ts bs v t b).head 13 = 1 ∧
    (output (q := q) hs ts bs v t b).tape 13 = RadixZeroFill.encodedBinary (afterBits (q := q) v t b) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end IntegerMultBounds.Machine.ArbitrarySliceDimensions
