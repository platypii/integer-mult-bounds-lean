import IntegerMultBounds.Machine.RowPaddingSpanCounts

/-! Physically compute the powers used by a selected digit slice. Exponent
subtractions may retain high zero bits; every such scanned bit is charged. -/
namespace IntegerMultBounds.Machine.SliceExponentPowers
variable {q : ℕ} (hq : 2 ≤ q)
noncomputable section

private def hd : Option (List Bool) → ℤ | none => 0 | some _ => 1
private def tp : Option (List Bool) → ℤ → Fin (q+4)
  | none => fun _ => blank
  | some xs => RadixZeroFill.encodedBinary xs

/-- Original e,t,b at0,1,2; differences3,4; output powers5,6; scratch7,8. -/
def bank (es ts bs : List Bool) (ds : Fin 4 → Option (List Bool)) : Tapes 9 q :=
  ⟨![1,1,1,hd (ds 0),hd (ds 1),hd (ds 2),hd (ds 3),0,0],
   ![RadixZeroFill.encodedBinary es,RadixZeroFill.encodedBinary ts,RadixZeroFill.encodedBinary bs,
     tp (ds 0),tp (ds 1),tp (ds 2),tp (ds 3),fun _ => blank,fun _ => blank]⟩

def stage (es ts bs : List Bool) (xs : Fin 4 → List Bool) (k : ℕ) : Tapes 9 q :=
  bank es ts bs (fun i => if i.val < k then some (xs i) else none)

def input (es ts bs : List Bool) : Tapes 9 q := bank es ts bs (fun _ => none)
def tail (e t b : ℕ) := e-t-b
def first (es ts : List Bool) := BinarySubReuse.difference es ts
def second (es ts bs : List Bool) := BinarySubReuse.difference (first es ts) bs

def words (es ts bs : List Bool) (e t b : ℕ) : Fin 4 → List Bool :=
  ![first es ts,second es ts bs,RadixPowerDescriptor.bits hq t,RadixPowerDescriptor.bits hq (tail e t b)]

def output (es ts bs : List Bool) (e t b : ℕ) : Tapes 9 q :=
  bank es ts bs ![none,none,some (RadixPowerDescriptor.bits hq t),some (RadixPowerDescriptor.bits hq (tail e t b))]

def sub0Placement : Fin (3+6) ≃ Fin 9 where
  toFun := ![0,1,3,2,4,5,6,7,8]
  invFun := ![0,1,3,2,4,5,6,7,8]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def sub1Placement : Fin (3+6) ≃ Fin 9 where
  toFun := ![3,2,4,0,1,5,6,7,8]
  invFun := ![3,4,1,0,2,5,6,7,8]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def power0Placement : Fin (4+5) ≃ Fin 9 where
  toFun := ![7,8,1,5,0,2,3,4,6]
  invFun := ![4,2,5,6,7,3,8,0,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def power1Placement : Fin (4+5) ≃ Fin 9 where
  toFun := ![7,8,4,6,0,1,2,3,5]
  invFun := ![4,5,6,7,2,8,3,0,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def sub0Program := Placement.placed (Alphabet.program (RadixToBinary.binaryEncoding (q := q)) BinarySubReuse.program) sub0Placement

def sub1Program := Placement.placed (Alphabet.program (RadixToBinary.binaryEncoding (q := q)) BinarySubReuse.program) sub1Placement

def power0Program := Placement.placed (RadixPowerDescriptor.program hq) power0Placement

def power1Program := Placement.placed (RadixPowerDescriptor.program hq) power1Placement

private def cleanSlots : List (Fin 9) := [3,4]
def cleanProgram := BinaryDescriptorCleanupList.program (a := q) (by decide : 0 < 9) cleanSlots

def program := seq (seq (seq (seq (sub0Program (q := q)) sub1Program) (power0Program hq)) (power1Program hq)) cleanProgram

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

private theorem sub0_hoare (es ts bs : List Bool) (xs : Fin 4 → List Bool)
    (hx : xs 0 = BinarySubReuse.difference es ts) :
    HoareTime (sub0Program (q := q)) (fun v => v = stage es ts bs xs 0)
      (fun v => v = stage es ts bs xs 1) (4*BinarySubReuse.width es ts+14) := by
  have h := Alphabet.map_hoare (RadixToBinary.binaryEncoding (q := q))
    (BinarySubReuse.sub_hoare es ts)
  have hh : HoareTime (Alphabet.program (RadixToBinary.binaryEncoding (q := q)) BinarySubReuse.program)
      (fun v => v = Alphabet.mapTapes RadixToBinary.binaryEncoding
        (BinarySubReuse.bank es ts (fun _ => blank) 1 1 0))
      (fun v => v = Alphabet.mapTapes RadixToBinary.binaryEncoding
        (BinarySubReuse.bank es ts (CountedCopyReuse.binary (xs 0)) 1 1 1))
      (4*BinarySubReuse.width es ts+14) := by
    rw [hx]
    exact h.consequence (fun _ h => ⟨_,rfl,h⟩) (by rintro v ⟨w,rfl,h⟩; exact h) le_rfl
  apply placed_exact sub0Placement _ _ _ _ _ _ _ hh
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [sub0Placement,stage,bank]

private theorem sub1_hoare (es ts bs : List Bool) (xs : Fin 4 → List Bool)
    (hx : xs 1 = BinarySubReuse.difference (xs 0) bs) :
    HoareTime (sub1Program (q := q)) (fun v => v = stage es ts bs xs 1)
      (fun v => v = stage es ts bs xs 2) (4*BinarySubReuse.width (xs 0) bs+14) := by
  have h := Alphabet.map_hoare (RadixToBinary.binaryEncoding (q := q))
    (BinarySubReuse.sub_hoare (xs 0) bs)
  have hh : HoareTime (Alphabet.program (RadixToBinary.binaryEncoding (q := q)) BinarySubReuse.program)
      (fun v => v = Alphabet.mapTapes RadixToBinary.binaryEncoding
        (BinarySubReuse.bank (xs 0) bs (fun _ => blank) 1 1 0))
      (fun v => v = Alphabet.mapTapes RadixToBinary.binaryEncoding
        (BinarySubReuse.bank (xs 0) bs (CountedCopyReuse.binary (xs 1)) 1 1 1))
      (4*BinarySubReuse.width (xs 0) bs+14) := by
    rw [hx]
    exact h.consequence (fun _ h => ⟨_,rfl,h⟩) (by rintro v ⟨w,rfl,h⟩; exact h) le_rfl
  apply placed_exact sub1Placement _ _ _ _ _ _ _ hh
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [sub1Placement,stage,bank]

private theorem power0_hoare (es ts bs : List Bool) (xs : Fin 4 → List Bool) (n : ℕ)
    (hv : Counter.value ts = n) (hx : xs 2 = RadixPowerDescriptor.bits hq n) :
    HoareTime (power0Program hq) (fun v => v = stage es ts bs xs 2)
      (fun v => v = stage es ts bs xs 3) (10*q^n+18*n+7*ts.length+57) := by
  apply placed_exact power0Placement _ _ _ _ _ _ _ (RadixPowerDescriptor.construct_hoare hq ts n hv)
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [power0Placement,stage,bank,tp,hd,hx]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [power0Placement,stage,bank]

private theorem power1_hoare (es ts bs : List Bool) (xs : Fin 4 → List Bool) (n : ℕ)
    (hv : Counter.value (xs 1) = n) (hx : xs 3 = RadixPowerDescriptor.bits hq n) :
    HoareTime (power1Program hq) (fun v => v = stage es ts bs xs 3)
      (fun v => v = stage es ts bs xs 4) (10*q^n+18*n+7*(xs 1).length+57) := by
  apply placed_exact power1Placement _ _ _ _ _ _ _ (RadixPowerDescriptor.construct_hoare hq (xs 1) n hv)
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [power1Placement,stage,bank,tp,hd,hx]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [power1Placement,stage,bank]

private theorem clean_hoare (es ts bs : List Bool) (xs : Fin 4 → List Bool) :
    HoareTime (cleanProgram (q := q)) (fun v => v = stage es ts bs xs 4)
      (fun v => v = bank es ts bs ![none,none,some (xs 2),some (xs 3)])
      (2*(xs 0).length+2*(xs 1).length+10) := by
  let ws : Fin 9 → List Bool := fun i => if i = 3 then xs 0 else xs 1
  have h := BinaryDescriptorCleanupList.cleanup_hoare (by decide : 0 < 9) cleanSlots (by decide)
    ws (stage (q := q) es ts bs xs 4) (by
      intro i hi
      simp only [cleanSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl <;> constructor <;>
        first | rfl | simpa [ws,stage,bank,tp] using (BinaryDescriptorStackRoundtrip.descriptor_encoded (a := q) _).symm)
  apply h.consequence (fun _ h => h) _ _
  · rintro v rfl
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · simp [BinaryDescriptorCleanupList.cost,cleanSlots,ws]
    omega

/-- No canonicality of the temporary differences is needed for either power. -/
theorem construct_hoare (es ts bs : List Bool) (e t b V : ℕ)
    (he : Counter.value es = e) (ht : Counter.value ts = t) (hb : Counter.value bs = b)
    (hfit : t+b ≤ e) (hV : 0 < V) (hQ : q^e ≤ V)
    (we : es.length ≤ 2*V) (wt : ts.length ≤ 2*V) (wb : bs.length ≤ 2*V) :
    HoareTime (program hq) (fun v => v = input es ts bs)
      (fun v => v = output hq es ts bs e t b) (300*V) := by
  let xs := words hq es ts bs e t b
  have hf : Counter.value (first es ts) = e-t := by
    rw [first,BinarySubReuse.difference_value _ _ (by omega),he,ht]
  have hs : Counter.value (second es ts bs) = tail e t b := by
    rw [second,BinarySubReuse.difference_value _ _ (by omega),hf,hb]
    rfl
  have h := ((((sub0_hoare (q := q) es ts bs xs rfl).seq (sub1_hoare es ts bs xs rfl)).seq
    (power0_hoare hq es ts bs xs t ht rfl)).seq
    (power1_hoare hq es ts bs xs (tail e t b) hs rfl)).seq (clean_hoare es ts bs xs)
  apply h.consequence (fun _ h => h) (fun _ h => h) _
  have w0 : (first es ts).length ≤ 2*V := by rw [first,BinarySubReuse.difference_length]; omega
  have w1 : (second es ts bs).length ≤ 2*V := by rw [second,BinarySubReuse.difference_length]; omega
  have h0 : q^t ≤ V := (Nat.pow_le_pow_right (by omega) (by omega : t ≤ e)).trans hQ
  have h1 : q^(tail e t b) ≤ V :=
    (Nat.pow_le_pow_right (by omega) (by unfold tail; omega : tail e t b ≤ e)).trans hQ
  have hev : e ≤ V := (RadixToBinaryData.width_le_power hq e).trans hQ
  dsimp [xs,words,BinarySubReuse.width]
  dsimp [tail] at h1 ⊢
  omega

theorem ready (es ts bs : List Bool) (e t b : ℕ) :
    (output hq es ts bs e t b).head 5 = 1 ∧
    (output hq es ts bs e t b).tape 5 = RadixZeroFill.encodedBinary (RadixPowerDescriptor.bits hq t) ∧
    (output hq es ts bs e t b).head 6 = 1 ∧
    (output hq es ts bs e t b).tape 6 = RadixZeroFill.encodedBinary (RadixPowerDescriptor.bits hq (tail e t b)) :=
  ⟨rfl,rfl,rfl,rfl⟩

end
end IntegerMultBounds.Machine.SliceExponentPowers
