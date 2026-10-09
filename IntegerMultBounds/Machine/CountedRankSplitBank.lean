import IntegerMultBounds.Machine.CountedRankSplitPosition
import IntegerMultBounds.Machine.DimensionProductDescriptor

/-! A fixed twelve-tape splitter bank. Counter/V/W, original q/b/n, generated
nq/nb and one clock plus three product-work tapes. -/
namespace IntegerMultBounds.Machine.CountedRankSplitBank
noncomputable section
variable {a : ℕ}

private def hd : Option (List Bool) → ℤ | none => 0 | some _ => 1
private def tp : Option (List Bool) → ℤ → Fin (a+4)
  | none => fun _ => blank
  | some bs => RadixZeroFill.encodedBinary bs

def values (q b n : ℕ) : Fin 3 → ℕ := ![q,b,n]
def bank (f g h : ℤ → Fin (a+4)) (p v w : ℤ) (hs : Fin 3 → List Bool)
    (nq nb : Option (List Bool)) : Tapes 12 a :=
  ⟨![p,v,w,1,1,1,hd nq,hd nb,0,0,0,0],
   ![f,g,h,RadixZeroFill.encodedBinary (hs 0),RadixZeroFill.encodedBinary (hs 1),
     RadixZeroFill.encodedBinary (hs 2),tp nq,tp nb,fun _ => blank,fun _ => blank,
     fun _ => blank,fun _ => blank]⟩

def qBits (n q : ℕ) := DimensionProductDescriptor.bits n q
def bBits (n b : ℕ) := DimensionProductDescriptor.bits n b

def qPlace : Fin (6+6) ≃ Fin 12 where
  toFun := ![9,6,10,3,11,5,0,1,2,4,7,8]
  invFun := ![6,7,8,3,9,5,1,10,11,0,2,4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def bPlace : Fin (6+6) ≃ Fin 12 where
  toFun := ![9,7,10,4,11,5,0,1,2,3,6,8]
  invFun := ![6,7,8,9,3,5,10,1,11,0,2,4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def copyVPlace : Fin (4+8) ≃ Fin 12 where
  toFun := ![0,1,8,6,2,3,4,5,7,9,10,11]
  invFun := ![0,1,4,5,6,7,3,8,2,9,10,11]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def copyWPlace : Fin (4+8) ≃ Fin 12 where
  toFun := ![0,2,8,7,1,3,4,5,6,9,10,11]
  invFun := ![0,4,1,5,6,7,8,3,2,9,10,11]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def ctrQPlace : Fin (3+9) ≃ Fin 12 where
  toFun := ![0,8,6,1,2,3,4,5,7,9,10,11]
  invFun := ![0,3,4,5,6,7,2,8,1,9,10,11]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def ctrBPlace : Fin (3+9) ≃ Fin 12 where
  toFun := ![0,8,7,1,2,3,4,5,6,9,10,11]
  invFun := ![0,3,4,5,6,7,8,2,1,9,10,11]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def vPlace : Fin (3+9) ≃ Fin 12 where
  toFun := ![1,8,6,0,2,3,4,5,7,9,10,11]
  invFun := ![3,0,4,5,6,7,2,8,1,9,10,11]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def wPlace : Fin (3+9) ≃ Fin 12 where
  toFun := ![2,8,7,0,1,3,4,5,6,9,10,11]
  invFun := ![3,4,0,5,6,7,8,2,1,9,10,11]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def qProgram := Placement.placed (DimensionProductDescriptor.program (q := a)) qPlace
def bProgram := Placement.placed (DimensionProductDescriptor.program (q := a)) bPlace
def copyV := Placement.placed (CountedRankSplitCopy.program (a := a)) copyVPlace
def copyW := Placement.placed (CountedRankSplitCopy.program (a := a)) copyWPlace
def backCtrQ := Placement.placed (CountedRankSplitPosition.program (a := a)) ctrQPlace
def backCtrB := Placement.placed (CountedRankSplitPosition.program (a := a)) ctrBPlace
def backV := Placement.placed (CountedRankSplitPosition.program (a := a)) vPlace
def backW := Placement.placed (CountedRankSplitPosition.program (a := a)) wPlace
def clearQ := BinaryDescriptorCleanupList.oneProgram (a := a) (6 : Fin 12)
def clearB := BinaryDescriptorCleanupList.oneProgram (a := a) (7 : Fin 12)

theorem placed_exact {s u t k cost : ℕ} {M : Program s k a}
    (e : Fin (s+u) ≃ Fin t) (v w : Tapes t a) (small small' : Tapes s a)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) ?_ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

theorem q_input (f g h : ℤ → Fin (a+4)) (p v w : ℤ) (hs : Fin 3 → List Bool) :
    Placement.active qPlace (bank f g h p v w hs none none) = DimensionProductDescriptor.input (hs 0) (hs 2) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem q_output (f g h : ℤ → Fin (a+4)) (p v w : ℤ) (hs : Fin 3 → List Bool) (n q : ℕ) :
    Placement.active qPlace (bank f g h p v w hs (some (qBits n q)) none) = DimensionProductDescriptor.output (hs 0) (hs 2) n q := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem q_extra (f g h : ℤ → Fin (a+4)) (p v w : ℤ) (hs : Fin 3 → List Bool) (n q : ℕ) :
    Placement.extra qPlace (bank f g h p v w hs none none) =
      Placement.extra qPlace (bank f g h p v w hs (some (qBits n q)) none) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [qPlace,bank,hd,tp]

theorem b_input (f g h : ℤ → Fin (a+4)) (p v w : ℤ) (hs : Fin 3 → List Bool) (qs : List Bool) :
    Placement.active bPlace (bank f g h p v w hs (some qs) none) = DimensionProductDescriptor.input (hs 1) (hs 2) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem b_output (f g h : ℤ → Fin (a+4)) (p v w : ℤ) (hs : Fin 3 → List Bool) (qs : List Bool) (n b : ℕ) :
    Placement.active bPlace (bank f g h p v w hs (some qs) (some (bBits n b))) = DimensionProductDescriptor.output (hs 1) (hs 2) n b := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem b_extra (f g h : ℤ → Fin (a+4)) (p v w : ℤ) (hs : Fin 3 → List Bool) (qs : List Bool) (n b : ℕ) :
    Placement.extra bPlace (bank f g h p v w hs (some qs) none) =
      Placement.extra bPlace (bank f g h p v w hs (some qs) (some (bBits n b))) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [bPlace,bank,hd,tp]

theorem constructQ (f g h : ℤ → Fin (a+4)) (p v w : ℤ) (hs : Fin 3 → List Bool)
    (n q : ℕ) (hq : 0 < q) (hvq : Counter.value (hs 0) = q) (hvn : Counter.value (hs 2) = n)
    (cq : GrowingCounterData.Canonical (hs 0)) (cn : GrowingCounterData.Canonical (hs 2)) :
    HoareTime (qProgram (a := a)) (fun u => u = bank f g h p v w hs none none)
      (fun u => u = bank f g h p v w hs (some (qBits n q)) none) (53*(n*q)+28) := by
  exact placed_exact qPlace _ _ _ _ (q_input f g h p v w hs) (q_output f g h p v w hs n q)
    (q_extra f g h p v w hs n q) (DimensionProductDescriptor.construct_hoare (hs 0) (hs 2) n q hq hvq hvn cq cn)

theorem constructB (f g h : ℤ → Fin (a+4)) (p v w : ℤ) (hs : Fin 3 → List Bool)
    (n b : ℕ) (nbq : List Bool) (hb : 0 < b) (hvb : Counter.value (hs 1) = b) (hvn : Counter.value (hs 2) = n)
    (cb : GrowingCounterData.Canonical (hs 1)) (cn : GrowingCounterData.Canonical (hs 2)) :
    HoareTime (bProgram (a := a)) (fun u => u = bank f g h p v w hs (some nbq) none)
      (fun u => u = bank f g h p v w hs (some nbq) (some (bBits n b))) (53*(n*b)+28) := by
  exact placed_exact bPlace _ _ _ _ (b_input f g h p v w hs nbq) (b_output f g h p v w hs nbq n b)
    (b_extra f g h p v w hs nbq n b) (DimensionProductDescriptor.construct_hoare (hs 1) (hs 2) n b hb hvb hvn cb cn)

theorem copiesV (f g h : ℤ → Fin (a+4)) (p v w : ℤ) (hs : Fin 3 → List Bool)
    (qs bs : List Bool) (N : ℕ) (hv : Counter.value qs = N) :
    HoareTime (copyV (a := a)) (fun u => u = bank f g h p v w hs (some qs) (some bs))
      (fun u => u = bank f (putWord g v (CopyCells.cells f p N)) h (p+N) (v+N) w hs (some qs) (some bs))
      (7*N+7*qs.length+28) := by
  apply placed_exact copyVPlace _ _ _ _ _ _ _ (CountedRankSplitCopy.copies f g p v qs N hv)
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem copiesW (f g h : ℤ → Fin (a+4)) (p v w : ℤ) (hs : Fin 3 → List Bool)
    (qs bs : List Bool) (N : ℕ) (hv : Counter.value bs = N) :
    HoareTime (copyW (a := a)) (fun u => u = bank f g h p v w hs (some qs) (some bs))
      (fun u => u = bank f g (putWord h w (CopyCells.cells f p N)) (p+N) v (w+N) hs (some qs) (some bs))
      (7*N+7*bs.length+28) := by
  apply placed_exact copyWPlace _ _ _ _ _ _ _ (CountedRankSplitCopy.copies f h p w bs N hv)
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem movesCtrQ (f g h : ℤ → Fin (a+4)) (p v w : ℤ) (hs : Fin 3 → List Bool)
    (qs bs : List Bool) (N : ℕ) (hv : Counter.value qs = N) :
    HoareTime (backCtrQ (a := a)) (fun u => u = bank f g h p v w hs (some qs) (some bs))
      (fun u => u = bank f g h (p-N) v w hs (some qs) (some bs)) (7*N+7*qs.length+28) := by
  apply placed_exact ctrQPlace _ _ _ _ _ _ _ (CountedRankSplitPosition.moves f p qs N hv)
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem movesCtrB (f g h : ℤ → Fin (a+4)) (p v w : ℤ) (hs : Fin 3 → List Bool)
    (qs bs : List Bool) (N : ℕ) (hv : Counter.value bs = N) :
    HoareTime (backCtrB (a := a)) (fun u => u = bank f g h p v w hs (some qs) (some bs))
      (fun u => u = bank f g h (p-N) v w hs (some qs) (some bs)) (7*N+7*bs.length+28) := by
  apply placed_exact ctrBPlace _ _ _ _ _ _ _ (CountedRankSplitPosition.moves f p bs N hv)
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem movesV (f g h : ℤ → Fin (a+4)) (p v w : ℤ) (hs : Fin 3 → List Bool)
    (qs bs : List Bool) (N : ℕ) (hv : Counter.value qs = N) :
    HoareTime (backV (a := a)) (fun u => u = bank f g h p v w hs (some qs) (some bs))
      (fun u => u = bank f g h p (v-N) w hs (some qs) (some bs)) (7*N+7*qs.length+28) := by
  apply placed_exact vPlace _ _ _ _ _ _ _ (CountedRankSplitPosition.moves g v qs N hv)
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem movesW (f g h : ℤ → Fin (a+4)) (p v w : ℤ) (hs : Fin 3 → List Bool)
    (qs bs : List Bool) (N : ℕ) (hv : Counter.value bs = N) :
    HoareTime (backW (a := a)) (fun u => u = bank f g h p v w hs (some qs) (some bs))
      (fun u => u = bank f g h p v (w-N) hs (some qs) (some bs)) (7*N+7*bs.length+28) := by
  apply placed_exact wPlace _ _ _ _ _ _ _ (CountedRankSplitPosition.moves h w bs N hv)
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem cleansQ (f g h : ℤ → Fin (a+4)) (p v w : ℤ) (hs : Fin 3 → List Bool) (qs bs : List Bool) :
    HoareTime (clearQ (a := a)) (fun u => u = bank f g h p v w hs (some qs) (some bs))
      (fun u => u = bank f g h p v w hs none (some bs)) (2*qs.length+4) := by
  have h0 := BinaryDescriptorCleanupList.one_hoare (6 : Fin 12)
    (bank f g h p v w hs (some qs) (some bs)) qs (BinaryDescriptorStackRoundtrip.descriptor_encoded qs).symm rfl
  apply h0.consequence (fun _ h => h) ?_ le_rfl
  rintro u rfl
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem cleansB (f g h : ℤ → Fin (a+4)) (p v w : ℤ) (hs : Fin 3 → List Bool) (bs : List Bool) :
    HoareTime (clearB (a := a)) (fun u => u = bank f g h p v w hs none (some bs))
      (fun u => u = bank f g h p v w hs none none) (2*bs.length+4) := by
  have h0 := BinaryDescriptorCleanupList.one_hoare (7 : Fin 12)
    (bank f g h p v w hs none (some bs)) bs (BinaryDescriptorStackRoundtrip.descriptor_encoded bs).symm rfl
  apply h0.consequence (fun _ h => h) ?_ le_rfl
  rintro u rfl
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.CountedRankSplitBank
