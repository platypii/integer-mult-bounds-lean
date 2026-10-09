import IntegerMultBounds.Machine.BinaryAddressOffsetHeaders
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Construct the repetition dimensions from six original descriptors q, b, n,
P, H, L. The four products, two powers, and temporary-header cleanup are actual
fixed-control tape programs. No derived dimension is supplied as an input. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetRepeatHeaders
open SharedPlacementAlphabet (setTape)
noncomputable section

def binary (xs : List Bool) := RadixZeroFill.encodedBinary (q := 0) xs
def widthBits (b n : ℕ) := DimensionProductDescriptor.bits n b
def sourceBits (q n : ℕ) := DimensionProductDescriptor.bits n q
def rangeBits (q n : ℕ) := FixedBasePowerStep.bits 2 (n*q)
def targetBits (b n : ℕ) := FixedBasePowerStep.bits 2 (n*b)
def prefixBits (P H : ℕ) := DimensionProductDescriptor.bits P H
def repeatBits (b n P H : ℕ) := DimensionProductDescriptor.bits (P*H) (2^(n*b))

def input (hs : Fin 6 → List Bool) : Tapes 18 0 :=
  ⟨fun i => if i.val<6 then 1 else 0,
    fun i => if h : i.val<6 then binary (hs ⟨i.val,h⟩) else fun _ => blank⟩
def widthBank (hs : Fin 6 → List Bool) (b n : ℕ) := setTape (input hs) 6 (binary (widthBits b n)) 1
def sourceBank (hs : Fin 6 → List Bool) (q b n : ℕ) := setTape (widthBank hs b n) 7 (binary (sourceBits q n)) 1
def rangeBank (hs : Fin 6 → List Bool) (q b n : ℕ) := setTape (sourceBank hs q b n) 8 (binary (rangeBits q n)) 1
def targetBank (hs : Fin 6 → List Bool) (q b n : ℕ) := setTape (rangeBank hs q b n) 9 (binary (targetBits b n)) 1
def prefixBank (hs : Fin 6 → List Bool) (q b n P H : ℕ) := setTape (targetBank hs q b n) 10 (binary (prefixBits P H)) 1
def repeatBank (hs : Fin 6 → List Bool) (q b n P H : ℕ) := setTape (prefixBank hs q b n P H) 11 (binary (repeatBits b n P H)) 1

def cleanupSlots : List (Fin 18) := [7,9,10]
def cleanupBits (q b n P H : ℕ) : Fin 18 → List Bool :=
  fun i => if i=7 then sourceBits q n else if i=9 then targetBits b n else if i=10 then prefixBits P H else []
def output (hs : Fin 6 → List Bool) (q b n P H : ℕ) :=
  BinaryDescriptorCleanupList.cleared cleanupSlots (repeatBank hs q b n P H)

def widthPlace : Fin (6+12) ≃ Fin 18 where
  toFun := ![12,6,13,1,14,2,0,3,4,5,7,8,9,10,11,15,16,17]
  invFun := ![6,3,5,7,8,9,1,10,11,12,13,14,0,2,4,15,16,17]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def widthProgram := Placement.placed (DimensionProductDescriptor.program (q := 0)) widthPlace

def sourcePlace : Fin (6+12) ≃ Fin 18 where
  toFun := ![12,7,13,0,14,2,1,3,4,5,6,8,9,10,11,15,16,17]
  invFun := ![3,6,5,7,8,9,10,1,11,12,13,14,0,2,4,15,16,17]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def sourceProgram := Placement.placed (DimensionProductDescriptor.program (q := 0)) sourcePlace

def rangePlace : Fin (8+10) ≃ Fin 18 where
  toFun := ![12,13,14,15,16,8,17,7,0,1,2,3,4,5,6,9,10,11]
  invFun := ![8,9,10,11,12,13,14,7,5,15,16,17,0,1,2,3,4,6]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def rangeProgram := Placement.placed (FixedBasePowerDescriptor.program (q := 0) 2) rangePlace

def targetPlace : Fin (8+10) ≃ Fin 18 where
  toFun := ![12,13,14,15,16,9,17,6,0,1,2,3,4,5,7,8,10,11]
  invFun := ![8,9,10,11,12,13,7,14,15,5,16,17,0,1,2,3,4,6]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def targetProgram := Placement.placed (FixedBasePowerDescriptor.program (q := 0) 2) targetPlace

def prefixPlace : Fin (6+12) ≃ Fin 18 where
  toFun := ![12,10,13,4,14,3,0,1,2,5,6,7,8,9,11,15,16,17]
  invFun := ![6,7,8,5,3,9,10,11,12,13,1,14,0,2,4,15,16,17]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def prefixProgram := Placement.placed (DimensionProductDescriptor.program (q := 0)) prefixPlace

def repeatPlace : Fin (6+12) ≃ Fin 18 where
  toFun := ![12,11,13,9,14,10,0,1,2,3,4,5,6,7,8,15,16,17]
  invFun := ![6,7,8,9,10,11,12,13,14,3,5,1,0,2,4,15,16,17]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def repeatProgram := Placement.placed (DimensionProductDescriptor.program (q := 0)) repeatPlace

def cleanupProgram := BinaryDescriptorCleanupList.program (a := 0) (by decide : 0<18) cleanupSlots
def program := seq (seq (seq (seq (seq (seq widthProgram sourceProgram) rangeProgram) targetProgram) prefixProgram) repeatProgram) cleanupProgram

private theorem product_hoare {u : ℕ} (e : Fin (6+u) ≃ Fin 18) (v : Tapes 18 0)
    (ws ns : List Bool) (N W : ℕ) (hW : 0<W)
    (hw : Counter.value ws=W) (hn : Counter.value ns=N)
    (cw : GrowingCounterData.Canonical ws) (cn : GrowingCounterData.Canonical ns)
    (ha : Placement.active e v=DimensionProductDescriptor.input ws ns) :
    HoareTime (Placement.placed (DimensionProductDescriptor.program (q := 0)) e)
      (fun z => z=v) (fun z => z=setTape v (e (Fin.castAdd u (1 : Fin 6)))
        (binary (DimensionProductDescriptor.bits N W)) 1) (53*(N*W)+28) := by
  have hh := Placement.hoare_at (DimensionProductDescriptor.construct_hoare ws ns N W hW hw hn cw cn) e v ha
  have he : DimensionProductDescriptor.output (q := 0) ws ns N W=
      setTape (DimensionProductDescriptor.input ws ns) (1 : Fin 6) (binary (DimensionProductDescriptor.bits N W)) 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  rw [he,←ha,PlacedDescriptorConstruction.replace_setTape]

theorem width_hoare (hs : Fin 6 → List Bool) (b n : ℕ) (hb : 0<b)
    (hvb : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime widthProgram (fun z => z=input hs) (fun z => z=widthBank hs b n) (53*((n)*(b))+28) := by
  have ha : Placement.active widthPlace (input hs)=DimensionProductDescriptor.input (hs 1) (hs 2) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  exact product_hoare widthPlace (input hs) (hs 1) (hs 2) (n) (b) (hb)
    (hvb) (hvn) (hc 1) (hc 2) ha

theorem source_hoare (hs : Fin 6 → List Bool) (q b n : ℕ) (hq : 0<q)
    (hvq : Counter.value (hs 0)=q) (hvn : Counter.value (hs 2)=n)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime sourceProgram (fun z => z=widthBank hs b n) (fun z => z=sourceBank hs q b n) (53*((n)*(q))+28) := by
  have ha : Placement.active sourcePlace (widthBank hs b n)=DimensionProductDescriptor.input (hs 0) (hs 2) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  exact product_hoare sourcePlace (widthBank hs b n) (hs 0) (hs 2) (n) (q) (hq)
    (hvq) (hvn) (hc 0) (hc 2) ha

theorem prefix_hoare (hs : Fin 6 → List Bool) (q b n P H : ℕ) (hH : 0<H)
    (hvP : Counter.value (hs 3)=P) (hvH : Counter.value (hs 4)=H)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime prefixProgram (fun z => z=targetBank hs q b n) (fun z => z=prefixBank hs q b n P H) (53*((P)*(H))+28) := by
  have ha : Placement.active prefixPlace (targetBank hs q b n)=DimensionProductDescriptor.input (hs 4) (hs 3) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  exact product_hoare prefixPlace (targetBank hs q b n) (hs 4) (hs 3) (P) (H) (hH)
    (hvH) (hvP) (hc 4) (hc 3) ha

theorem repeat_hoare (hs : Fin 6 → List Bool) (q b n P H : ℕ) :
    HoareTime repeatProgram (fun z => z=prefixBank hs q b n P H) (fun z => z=repeatBank hs q b n P H) (53*((P*H)*(2^(n*b)))+28) := by
  have ha : Placement.active repeatPlace (prefixBank hs q b n P H)=DimensionProductDescriptor.input (targetBits b n) (prefixBits P H) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  exact product_hoare repeatPlace (prefixBank hs q b n P H) (targetBits b n) (prefixBits P H) (P*H) (2^(n*b)) (by positivity)
    (FixedBasePowerDescriptor.result_value 2 (n*b)) (DimensionProductDescriptor.bits_value P H) (FixedBasePowerDescriptor.result_canonical 2 (n*b)) (DimensionProductDescriptor.bits_canonical P H) ha

theorem range_hoare (hs : Fin 6 → List Bool) (q b n : ℕ) :
    HoareTime rangeProgram (fun z => z=sourceBank hs q b n) (fun z => z=rangeBank hs q b n)
      (FixedBasePowerDescriptor.constant 2*2^(n*q)) := by
  have ha : Placement.active rangePlace (sourceBank hs q b n)=FixedBasePowerDescriptor.input (sourceBits q n) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _
  exact PlacedDescriptorConstruction.power_hoare rangePlace (sourceBank hs q b n) 2 (n*q) (by decide)
    (sourceBits q n) (DimensionProductDescriptor.bits_value n q) (DimensionProductDescriptor.bits_canonical n q) ha

theorem target_hoare (hs : Fin 6 → List Bool) (q b n : ℕ) :
    HoareTime targetProgram (fun z => z=rangeBank hs q b n) (fun z => z=targetBank hs q b n)
      (FixedBasePowerDescriptor.constant 2*2^(n*b)) := by
  have ha : Placement.active targetPlace (rangeBank hs q b n)=FixedBasePowerDescriptor.input (widthBits b n) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _
  exact PlacedDescriptorConstruction.power_hoare targetPlace (rangeBank hs q b n) 2 (n*b) (by decide)
    (widthBits b n) (DimensionProductDescriptor.bits_value n b) (DimensionProductDescriptor.bits_canonical n b) ha

theorem cleanup_hoare (hs : Fin 6 → List Bool) (q b n P H : ℕ) :
    HoareTime cleanupProgram (fun z => z=repeatBank hs q b n P H)
      (fun z => z=output hs q b n P H)
      (BinaryDescriptorCleanupList.cost cleanupSlots (cleanupBits q b n P H)) := by
  apply BinaryDescriptorCleanupList.cleanup_hoare (by decide) cleanupSlots (by decide)
  intro i hi
  simp only [cleanupSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl <;> constructor <;> first | rfl |
    exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm

def cost (q b n P H : ℕ) :=
  (53*(n*b)+28)+(53*(n*q)+28)+FixedBasePowerDescriptor.constant 2*2^(n*q)+
  FixedBasePowerDescriptor.constant 2*2^(n*b)+(53*(P*H)+28)+(53*((P*H)*2^(n*b))+28)+
  BinaryDescriptorCleanupList.cost cleanupSlots (cleanupBits q b n P H)+6

theorem constructs (hs : Fin 6 → List Bool) (q b n P H : ℕ)
    (hb : 0<b) (hq : 0<q) (hH : 0<H)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b)
    (hvn : Counter.value (hs 2)=n) (hvP : Counter.value (hs 3)=P) (hvH : Counter.value (hs 4)=H)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun z => z=input hs) (fun z => z=output hs q b n P H) (cost q b n P H) := by
  have h0 := (width_hoare hs b n hb hvb hvn hc).seq (source_hoare hs q b n hq hvq hvn hc)
  have h1 := h0.seq (range_hoare hs q b n)
  have h2 := h1.seq (target_hoare hs q b n)
  have h3 := h2.seq (prefix_hoare hs q b n P H hH hvP hvH hc)
  have h4 := h3.seq (repeat_hoare hs q b n P H)
  have h5 := h4.seq (cleanup_hoare hs q b n P H)
  exact h5.consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.BinaryAddressOffsetRepeatHeaders
