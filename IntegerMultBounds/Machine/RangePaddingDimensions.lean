import IntegerMultBounds.Machine.BoundedProductDescriptor
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Physical four-product dimensions for rectangular range padding. Payload
tapes are complete spectators; the five original descriptors are preserved.
All product markers are initialized on blank tape, and workspace is cleaned. -/
namespace IntegerMultBounds.Machine.RangePaddingDimensions
variable {q : ℕ}
noncomputable section

private def hd : Option (List Bool) → ℤ | none => 0 | some _ => 1
private def tp : Option (List Bool) → ℤ → Fin (q+4)
  | none => fun _ => blank
  | some xs => RadixZeroFill.encodedBinary xs

/-- Payload0/1 at head0; P,N,G,B,M2–6; PN,PNG,GM,GMB7–10;
six wholly blank work tapes11–16. Present descriptors start at head1. -/
def bank (source destination : ℤ → Fin (q+4)) (hs : Fin 5 → List Bool)
    (dims : Fin 4 → Option (List Bool)) : Tapes 17 q :=
  ⟨(fun i => match i.val with
    | 0 => 0
    | 1 => 0
    | 2 => 1
    | 3 => 1
    | 4 => 1
    | 5 => 1
    | 6 => 1
    | 7 => hd (dims 0)
    | 8 => hd (dims 1)
    | 9 => hd (dims 2)
    | 10 => hd (dims 3)
    | 11 => 0
    | 12 => 0
    | 13 => 0
    | 14 => 0
    | 15 => 0
    | _ => 0),
   (fun i => match i.val with
    | 0 => source
    | 1 => destination
    | 2 => RadixZeroFill.encodedBinary (hs 0)
    | 3 => RadixZeroFill.encodedBinary (hs 1)
    | 4 => RadixZeroFill.encodedBinary (hs 2)
    | 5 => RadixZeroFill.encodedBinary (hs 3)
    | 6 => RadixZeroFill.encodedBinary (hs 4)
    | 7 => tp (dims 0)
    | 8 => tp (dims 1)
    | 9 => tp (dims 2)
    | 10 => tp (dims 3)
    | 11 => fun _ => blank
    | 12 => fun _ => blank
    | 13 => fun _ => blank
    | 14 => fun _ => blank
    | 15 => fun _ => blank
    | _ => fun _ => blank)⟩

def input (source destination : ℤ → Fin (q+4)) (hs : Fin 5 → List Bool) :=
  bank source destination hs (fun _ => none)

def stage (source destination : ℤ → Fin (q+4)) (hs : Fin 5 → List Bool)
    (xs : Fin 4 → List Bool) (k : ℕ) := bank source destination hs (fun i => if i.val < k then some (xs i) else none)

def pnBits (P N : ℕ) := BoundedProductDescriptor.bits N P
def pngBits (P N G : ℕ) := BoundedProductDescriptor.bits (P*N) G
def gmBits (G M : ℕ) := BoundedProductDescriptor.bits M G
def gmbBits (G M B : ℕ) := BoundedProductDescriptor.bits (G*M) B

def words (P N G B M : ℕ) : Fin 4 → List Bool := ![pnBits P N,pngBits P N G,gmBits G M,gmbBits G M B]
def values (P N G B M : ℕ) : Fin 5 → ℕ := ![P,N,G,B,M]
def volume (P G B M : ℕ) := P*G*M*B

def ready (source destination : ℤ → Fin (q+4)) (hs : Fin 5 → List Bool) (P N G B M : ℕ) :=
  bank source destination hs (fun i => some (words P N G B M i))

def pnPlacement : Fin (6+11) ≃ Fin 17 where
  toFun i := match i.val with
    | 0 => 11
    | 1 => 7
    | 2 => 12
    | 3 => 2
    | 4 => 13
    | 5 => 3
    | 6 => 0
    | 7 => 1
    | 8 => 4
    | 9 => 5
    | 10 => 6
    | 11 => 8
    | 12 => 9
    | 13 => 10
    | 14 => 14
    | 15 => 15
    | _ => 16
  invFun i := match i.val with
    | 0 => 6
    | 1 => 7
    | 2 => 3
    | 3 => 5
    | 4 => 8
    | 5 => 9
    | 6 => 10
    | 7 => 1
    | 8 => 11
    | 9 => 12
    | 10 => 13
    | 11 => 0
    | 12 => 2
    | 13 => 4
    | 14 => 14
    | 15 => 15
    | _ => 16
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def pnProgram := Placement.placed (BoundedProductDescriptor.program (q := q)) pnPlacement

def pngPlacement : Fin (6+11) ≃ Fin 17 where
  toFun i := match i.val with
    | 0 => 11
    | 1 => 8
    | 2 => 12
    | 3 => 4
    | 4 => 13
    | 5 => 7
    | 6 => 0
    | 7 => 1
    | 8 => 2
    | 9 => 3
    | 10 => 5
    | 11 => 6
    | 12 => 9
    | 13 => 10
    | 14 => 14
    | 15 => 15
    | _ => 16
  invFun i := match i.val with
    | 0 => 6
    | 1 => 7
    | 2 => 8
    | 3 => 9
    | 4 => 3
    | 5 => 10
    | 6 => 11
    | 7 => 5
    | 8 => 1
    | 9 => 12
    | 10 => 13
    | 11 => 0
    | 12 => 2
    | 13 => 4
    | 14 => 14
    | 15 => 15
    | _ => 16
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def pngProgram := Placement.placed (BoundedProductDescriptor.program (q := q)) pngPlacement

def gmPlacement : Fin (6+11) ≃ Fin 17 where
  toFun i := match i.val with
    | 0 => 11
    | 1 => 9
    | 2 => 12
    | 3 => 4
    | 4 => 13
    | 5 => 6
    | 6 => 0
    | 7 => 1
    | 8 => 2
    | 9 => 3
    | 10 => 5
    | 11 => 7
    | 12 => 8
    | 13 => 10
    | 14 => 14
    | 15 => 15
    | _ => 16
  invFun i := match i.val with
    | 0 => 6
    | 1 => 7
    | 2 => 8
    | 3 => 9
    | 4 => 3
    | 5 => 10
    | 6 => 5
    | 7 => 11
    | 8 => 12
    | 9 => 1
    | 10 => 13
    | 11 => 0
    | 12 => 2
    | 13 => 4
    | 14 => 14
    | 15 => 15
    | _ => 16
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def gmProgram := Placement.placed (BoundedProductDescriptor.program (q := q)) gmPlacement

def gmbPlacement : Fin (6+11) ≃ Fin 17 where
  toFun i := match i.val with
    | 0 => 11
    | 1 => 10
    | 2 => 12
    | 3 => 5
    | 4 => 13
    | 5 => 9
    | 6 => 0
    | 7 => 1
    | 8 => 2
    | 9 => 3
    | 10 => 4
    | 11 => 6
    | 12 => 7
    | 13 => 8
    | 14 => 14
    | 15 => 15
    | _ => 16
  invFun i := match i.val with
    | 0 => 6
    | 1 => 7
    | 2 => 8
    | 3 => 9
    | 4 => 10
    | 5 => 3
    | 6 => 11
    | 7 => 12
    | 8 => 13
    | 9 => 5
    | 10 => 1
    | 11 => 0
    | 12 => 2
    | 13 => 4
    | 14 => 14
    | 15 => 15
    | _ => 16
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def gmbProgram := Placement.placed (BoundedProductDescriptor.program (q := q)) gmbPlacement

def program := seq (seq (seq (pnProgram (q := q)) pngProgram) gmProgram) gmbProgram

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

private theorem bounded_product (ns ws : List Bool) (N W : ℕ)
    (hn : Counter.value ns = N) (hw : Counter.value ws = W)
    (cn : GrowingCounterData.Canonical ns) (cw : GrowingCounterData.Canonical ws) (hW : 0 < W) :
    HoareTime (BoundedProductDescriptor.program (q := q)) (fun z => z = BoundedProductDescriptor.input ws ns)
      (fun z => z = BoundedProductDescriptor.output ws ns N W) (53*(N*W)+28) := by
  have wn := GrowingCounterData.canonical_width ns cn
  have ww := GrowingCounterData.canonical_width ws cw
  have ln := Nat.log2_le_self (Counter.value ns)
  have lw := Nat.log2_le_self (Counter.value ws)
  rw [hn] at wn ln
  rw [hw] at ww lw
  exact BoundedProductDescriptor.construct_hoare ws ns N W N hW hw hn le_rfl (by omega) (by omega)

private theorem pn_hoare (source destination : ℤ → Fin (q+4)) (hs : Fin 5 → List Bool)
    (xs : Fin 4 → List Bool) (N W : ℕ)
    (hn : Counter.value (hs 1) = N) (hw : Counter.value (hs 0) = W)
    (cn : GrowingCounterData.Canonical (hs 1)) (cw : GrowingCounterData.Canonical (hs 0)) (hW : 0 < W)
    (hx : xs 0 = BoundedProductDescriptor.bits N W) :
    HoareTime (pnProgram (q := q)) (fun z => z = stage source destination hs xs 0)
      (fun z => z = stage source destination hs xs 1) (53*(N*W)+28) := by
  apply placed_exact pnPlacement _ _ _ _ _ _ _ (bounded_product (hs 1) (hs 0) N W hn hw cn cw hW)
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [pnPlacement,stage,bank,tp,hd,hx]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem png_hoare (source destination : ℤ → Fin (q+4)) (hs : Fin 5 → List Bool)
    (xs : Fin 4 → List Bool) (N W : ℕ)
    (hn : Counter.value (xs 0) = N) (hw : Counter.value (hs 2) = W)
    (cn : GrowingCounterData.Canonical (xs 0)) (cw : GrowingCounterData.Canonical (hs 2)) (hW : 0 < W)
    (hx : xs 1 = BoundedProductDescriptor.bits N W) :
    HoareTime (pngProgram (q := q)) (fun z => z = stage source destination hs xs 1)
      (fun z => z = stage source destination hs xs 2) (53*(N*W)+28) := by
  apply placed_exact pngPlacement _ _ _ _ _ _ _ (bounded_product (xs 0) (hs 2) N W hn hw cn cw hW)
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [pngPlacement,stage,bank,tp,hd,hx]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem gm_hoare (source destination : ℤ → Fin (q+4)) (hs : Fin 5 → List Bool)
    (xs : Fin 4 → List Bool) (N W : ℕ)
    (hn : Counter.value (hs 4) = N) (hw : Counter.value (hs 2) = W)
    (cn : GrowingCounterData.Canonical (hs 4)) (cw : GrowingCounterData.Canonical (hs 2)) (hW : 0 < W)
    (hx : xs 2 = BoundedProductDescriptor.bits N W) :
    HoareTime (gmProgram (q := q)) (fun z => z = stage source destination hs xs 2)
      (fun z => z = stage source destination hs xs 3) (53*(N*W)+28) := by
  apply placed_exact gmPlacement _ _ _ _ _ _ _ (bounded_product (hs 4) (hs 2) N W hn hw cn cw hW)
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [gmPlacement,stage,bank,tp,hd,hx]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem gmb_hoare (source destination : ℤ → Fin (q+4)) (hs : Fin 5 → List Bool)
    (xs : Fin 4 → List Bool) (N W : ℕ)
    (hn : Counter.value (xs 2) = N) (hw : Counter.value (hs 3) = W)
    (cn : GrowingCounterData.Canonical (xs 2)) (cw : GrowingCounterData.Canonical (hs 3)) (hW : 0 < W)
    (hx : xs 3 = BoundedProductDescriptor.bits N W) :
    HoareTime (gmbProgram (q := q)) (fun z => z = stage source destination hs xs 3)
      (fun z => z = stage source destination hs xs 4) (53*(N*W)+28) := by
  apply placed_exact gmbPlacement _ _ _ _ _ _ _ (bounded_product (xs 2) (hs 3) N W hn hw cn cw hW)
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [gmbPlacement,stage,bank,tp,hd,hx]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem words_value (P N G B M : ℕ) :
    Counter.value (words P N G B M 0) = P*N ∧
    Counter.value (words P N G B M 1) = P*N*G ∧
    Counter.value (words P N G B M 2) = G*M ∧
    Counter.value (words P N G B M 3) = G*M*B := by
  refine ⟨?_,BoundedProductDescriptor.bits_value _ _,?_,BoundedProductDescriptor.bits_value _ _⟩
  · exact (BoundedProductDescriptor.bits_value N P).trans (Nat.mul_comm _ _)
  · exact (BoundedProductDescriptor.bits_value M G).trans (Nat.mul_comm _ _)

theorem words_canonical (P N G B M : ℕ) (i : Fin 4) : GrowingCounterData.Canonical (words P N G B M i) := by
  fin_cases i <;> exact BoundedProductDescriptor.bits_canonical _ _

theorem volume_positive (P G B M : ℕ) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hM : 0 < M) :
    0 < volume P G B M := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hP hG) hM) hB

theorem products_le (P N G B M : ℕ) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hNM : N ≤ M) :
    P*N ≤ volume P G B M ∧ P*N*G ≤ volume P G B M ∧
    G*M ≤ volume P G B M ∧ G*M*B ≤ volume P G B M := by
  have hpn := Nat.mul_le_mul_left P hNM
  have hpng := Nat.mul_le_mul_right G hpn
  have hgm := Nat.le_mul_of_pos_left (G*M) hP
  refine ⟨?_,?_,?_,?_⟩
  · have h := hpn.trans (Nat.le_mul_of_pos_right (P*M) (Nat.mul_pos hG hB))
    convert h using 1
    unfold volume
    ring
  · have h := hpng.trans (Nat.le_mul_of_pos_right (P*M*G) hB)
    convert h using 1
    unfold volume
    ring
  · have h := hgm.trans (Nat.le_mul_of_pos_right (P*(G*M)) hB)
    convert h using 1
    unfold volume
    ring
  · have h := Nat.le_mul_of_pos_left (G*M*B) hP
    convert h using 1
    unfold volume
    ring

/-- Four real product constructors. N may be zero; all positive spectator
factors and N≤M are explicit, and both payload tapes are preserved literally. -/
theorem construct_hoare (source destination : ℤ → Fin (q+4)) (hs : Fin 5 → List Bool)
    (P N G B M : ℕ) (hv : ∀ i, Counter.value (hs i) = values P N G B M i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hM : 0 < M) (hNM : N ≤ M) :
    HoareTime (program (q := q)) (fun z => z = input source destination hs)
      (fun z => z = ready source destination hs P N G B M) (330*volume P G B M) := by
  let xs := words P N G B M
  obtain ⟨v0,v1,v2,v3⟩ := words_value P N G B M
  have hcanon (i : Fin 4) : GrowingCounterData.Canonical (xs i) := words_canonical P N G B M i
  have h := (((pn_hoare source destination hs xs N P (hv 1) (hv 0) (hc 1) (hc 0) hP rfl).seq
    (png_hoare source destination hs xs (P*N) G v0 (hv 2) (hcanon 0) (hc 2) hG rfl)).seq
    (gm_hoare source destination hs xs M G (hv 4) (hv 2) (hc 4) (hc 2) hG rfl)).seq
    (gmb_hoare source destination hs xs (G*M) B v2 (hv 3) (hcanon 2) (hc 3) hB rfl)
  have hout : stage source destination hs xs 4 = ready source destination hs P N G B M := by
    apply congrArg (bank source destination hs)
    funext i
    simp only [show i.val < 4 from i.isLt,ite_true]
    rfl
  apply h.consequence (fun _ h => h) (fun _ h => h.trans hout) _
  obtain ⟨h0,h1,h2,h3⟩ := products_le P N G B M hP hG hB hNM
  have hV := volume_positive P G B M hP hG hB hM
  rw [Nat.mul_comm N P,Nat.mul_comm M G]
  omega

private def slots : List (Fin 17) := [7,8,9,10]
def cleanupProgram := BinaryDescriptorCleanupList.program (a := q) (by decide : 0 < 17) slots

private theorem cleanup_words (source destination : ℤ → Fin (q+4)) (hs : Fin 5 → List Bool)
    (xs : Fin 4 → List Bool) :
    HoareTime (cleanupProgram (q := q)) (fun z => z = bank source destination hs (fun i => some (xs i)))
      (fun z => z = input source destination hs)
      (2*((xs 0).length+(xs 1).length+(xs 2).length+(xs 3).length)+20) := by
  let ws : Fin 17 → List Bool := fun i => if i = 7 then xs 0 else if i = 8 then xs 1 else if i = 9 then xs 2 else xs 3
  have h := BinaryDescriptorCleanupList.cleanup_hoare (by decide : 0 < 17) slots (by decide)
    ws (bank source destination hs (fun i => some (xs i))) (by
      intro i hi
      simp only [slots,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> constructor <;>
        first | rfl | simpa [ws,bank,tp] using (BinaryDescriptorStackRoundtrip.descriptor_encoded (a := q) _).symm)
  apply h.consequence (fun _ h => h) _ _
  · rintro z rfl
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · simp [BinaryDescriptorCleanupList.cost,slots,ws]
    omega

/-- Cleanup is separately reusable after padding has changed either payload.
It erases all four generated descriptors and returns their heads to zero. -/
theorem cleanup_hoare (source destination : ℤ → Fin (q+4)) (hs : Fin 5 → List Bool)
    (P N G B M : ℕ) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hM : 0 < M) (hNM : N ≤ M) :
    HoareTime (cleanupProgram (q := q)) (fun z => z = ready source destination hs P N G B M)
      (fun z => z = input source destination hs) (40*volume P G B M) := by
  have hV := volume_positive P G B M hP hG hB hM
  obtain ⟨h0,h1,h2,h3⟩ := products_le P N G B M hP hG hB hNM
  obtain ⟨v0,v1,v2,v3⟩ := words_value P N G B M
  have hw (i : Fin 4) : (words P N G B M i).length ≤ 2*volume P G B M := by
    have hc := GrowingCounterData.canonical_width _ (words_canonical P N G B M i)
    have hl := Nat.log2_le_self (Counter.value (words P N G B M i))
    have hv : Counter.value (words P N G B M i) ≤ volume P G B M := by
      fin_cases i
      · exact v0.trans_le h0
      · exact v1.trans_le h1
      · exact v2.trans_le h2
      · exact v3.trans_le h3
    omega
  exact (cleanup_words source destination hs (words P N G B M)).consequence
    (fun _ h => h) (fun _ h => h) (by have := hw 0; have := hw 1; have := hw 2; have := hw 3; omega)

/-- The tighter construction volume is bounded by the full padded rectangle. -/
theorem volume_le_padded (P G B M : ℕ) (hM : 0 < M) : volume P G B M ≤ P*M*G*M*B := by
  have h := Nat.le_mul_of_pos_right (volume P G B M) hM
  convert h using 1
  unfold volume
  ring

def generatedSlot (i : Fin 4) : Fin 17 := ⟨7+i.val,by omega⟩

theorem descriptor_ready (source destination : ℤ → Fin (q+4)) (hs : Fin 5 → List Bool)
    (P N G B M : ℕ) (i : Fin 4) :
    (ready source destination hs P N G B M).head (generatedSlot i) = 1 ∧
    (ready source destination hs P N G B M).tape (generatedSlot i) =
      RadixZeroFill.encodedBinary (words P N G B M i) := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

end
end IntegerMultBounds.Machine.RangePaddingDimensions
