import IntegerMultBounds.Machine.TranslationProduct
import IntegerMultBounds.Machine.BinarySubReuse

/-! Literal synthesis of translation's three physical split lengths. All
output counters and work-clock markers are installed on initially blank tapes.
Three nested growing-counter products share immutable binary input counts. -/

namespace IntegerMultBounds.Machine.TranslationDescriptors

open CountedCopyReuse (empty binary)

private def extras (as : List Bool) (diff : ℤ → Fin 4) (r : ℤ) : Tapes 2 0 :=
  ⟨fun i => if i = 0 then 1 else r,fun i => if i = 0 then binary as else diff⟩

/-- Spare, three generated lengths, B clock/descriptor, N clock/Q descriptor,
then immutable a and the subtraction output. All indices are fixed. -/
def bank (ds : Fin 3 → List Bool) (bs qs as : List Bool) (diff : ℤ → Fin 4) (r : ℤ) : Tapes 10 0 :=
  (TranslationProduct.bank ds bs qs).append (extras as diff r)

/-- All writable descriptors/clocks are initially blank, with heads at zero. -/
def initial (bs qs as : List Bool) : Tapes 10 0 :=
  ((CountedLoopReuse.bank
    (CountedLoopReuse.bank
      ((⟨fun _ => 1,fun _ _ => blank⟩ : Tapes 1 0).append
        (⟨fun _ => 0,fun _ _ => blank⟩ : Tapes 3 0))
      (fun _ => blank) (binary bs) 0 1)
    (fun _ => blank) (binary qs) 0 1).append (extras as (fun _ => blank) 0))

private def markerMask (i : Fin 10) : Bool := decide (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 6)

private def marked (v : Tapes 10 0) : Tapes 10 0 :=
  ⟨fun i => v.head i+if markerMask i then 1 else 0,
    fun i => if markerMask i then Function.update (v.tape i) (v.head i) separator else v.tape i⟩

/-- A single literal simultaneous marker installation, preserving all inputs. -/
def markerProgram : Program 10 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols => if state = 0 then
    some (1,fun i => if markerMask i then (separator,Move.right) else (symbols i,Move.stay)) else none

private theorem marker_hoare (v : Tapes 10 0) :
    HoareTime markerProgram (fun w => w = v) (fun w => w = marked v) 1 := by
  intro w hw
  subst w
  refine ⟨1,⟨1,(marked v).head,(marked v).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,markerProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i
      cases h : markerMask i <;> simp [h,marked,Move.offset]
    · funext i z
      cases h : markerMask i <;> by_cases hz : z = v.head i <;> simp [h,marked,hz]
  · simp [step,markerProgram]

private theorem marker_initial (bs qs as : List Bool) :
    marked (initial bs qs as) = bank (fun _ => []) bs qs as (fun _ => blank) 0 := by
  unfold marked markerMask initial bank TranslationProduct.bank ScalingDescriptors.innerBank
    ScalingDescriptors.counters CountedLoopReuse.bank CountedLoopReuse.controls extras Tapes.append
  congr 1
  · funext i
    fin_cases i <;> simp [Fin.addCases]
  · funext i z
    fin_cases i <;> simp [Fin.addCases,binary,empty,putBits,Function.update_apply]

private def count (qs as diff : List Bool) (k : Fin 3) : List Bool := ![qs,as,diff] k

def descriptorSlot (k : Fin 3) : Fin 10 := ⟨7+k.val,by omega⟩

def productPlacement (k : Fin 3) : Fin (8+2) ≃ Fin 10 := Equiv.swap 7 (descriptorSlot k)

def productProgram (j k : Fin 3) : Program 10 35 0 :=
  Placement.placed (TranslationProduct.program j) (productPlacement k)

private theorem active_bank (ds : Fin 3 → List Bool) (bs qs as diff : List Bool) (k : Fin 3) :
    Placement.active (productPlacement k) (bank ds bs qs as (binary diff) 1) =
      TranslationProduct.bank ds bs (count qs as diff k) := by
  unfold Placement.active productPlacement bank extras TranslationProduct.bank ScalingDescriptors.innerBank
    ScalingDescriptors.counters CountedLoopReuse.bank CountedLoopReuse.controls Tapes.append count
  congr 1 <;> funext i <;> fin_cases k <;> fin_cases i <;> rfl

private theorem replace_bank (ds ds' : Fin 3 → List Bool) (bs qs as diff : List Bool) (k : Fin 3) :
    Placement.replace (productPlacement k) (bank ds bs qs as (binary diff) 1)
      (TranslationProduct.bank ds' bs (count qs as diff k)) = bank ds' bs qs as (binary diff) 1 := by
  have he : Placement.extra (productPlacement k) (bank ds bs qs as (binary diff) 1) =
      Placement.extra (productPlacement k) (bank ds' bs qs as (binary diff) 1) := by
    unfold Placement.extra productPlacement bank extras TranslationProduct.bank ScalingDescriptors.innerBank
      ScalingDescriptors.counters CountedLoopReuse.bank CountedLoopReuse.controls Tapes.append
    congr 1
    funext i
    fin_cases k <;> fin_cases i <;> rfl
  rw [Placement.replace,he,← active_bank ds' bs qs as diff k]
  exact Placement.view _ _

/-- One physically selected product descriptor, retaining all other counters
and immutable operands. The temporary subtraction count may have leading zeroes. -/
theorem product_hoare (ds : Fin 3 → List Bool) (j k : Fin 3) (hj : ds j = [])
    (bs qs as diff : List Bool) (B N Q : ℕ) (hB : 0 < B) (hb : Counter.value bs = B)
    (hn : Counter.value (count qs as diff k) = N) (hN : N ≤ Q)
    (wb : bs.length ≤ B+1) (wn : (count qs as diff k).length ≤ Q+1) :
    HoareTime (productProgram j k) (fun v => v = bank ds bs qs as (binary diff) 1)
      (fun v => v = bank (Function.update ds j (GrowingCounterData.advance (N*B) [])) bs qs as (binary diff) 1)
      (53*(Q*B)+23) := by
  have hh := Placement.hoare_at
    (TranslationProduct.product_empty_hoare_bounded ds j hj bs (count qs as diff k) B N Q hB hb hn hN wb wn)
    (productPlacement k) (bank ds bs qs as (binary diff) 1) (active_bank ds bs qs as diff k)
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_bank _ _ _ _ _ _ _

/-- Canonical final descriptors in cut, tail, total order. -/
def descriptors (Q a B : ℕ) : Fin 3 → List Bool :=
  ![GrowingCounterData.advance ((Q-a)*B) [],GrowingCounterData.advance (a*B) [],GrowingCounterData.advance (Q*B) []]

theorem descriptor_values (Q a B : ℕ) :
    Counter.value (descriptors Q a B 0) = (Q-a)*B ∧
    Counter.value (descriptors Q a B 1) = a*B ∧
    Counter.value (descriptors Q a B 2) = Q*B := by
  simp [descriptors,GrowingCounterData.empty_value]

theorem descriptors_canonical (Q a B : ℕ) (j : Fin 3) :
    GrowingCounterData.Canonical (descriptors Q a B j) := by
  fin_cases j <;> exact GrowingCounterData.advance_canonical _ [] (Or.inl rfl)

/-- Fixed order: complement times B, offset times B, then full length times B. -/
def productsProgram : Program 10 105 0 :=
  seq (seq (productProgram 0 2) (productProgram 1 1)) (productProgram 2 0)

/-- Complete three-product stage from the derived subtraction word. -/
theorem products_hoare (Q a B : ℕ) (ha : a ≤ Q) (hB : 0 < B) (bs qs as diff : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (ha' : Counter.value as = a)
    (hd : Counter.value diff = Q-a) (wb : bs.length ≤ B+1)
    (wq : qs.length ≤ Q+1) (wa : as.length ≤ Q+1) (wd : diff.length ≤ Q+1) :
    HoareTime productsProgram (fun v => v = bank (fun _ => []) bs qs as (binary diff) 1)
      (fun v => v = bank (descriptors Q a B) bs qs as (binary diff) 1)
      (159*(Q*B)+71) := by
  let ds₁ : Fin 3 → List Bool := Function.update (fun _ => []) 0 (GrowingCounterData.advance ((Q-a)*B) [])
  let ds₂ : Fin 3 → List Bool := Function.update ds₁ 1 (GrowingCounterData.advance (a*B) [])
  have h₀ := product_hoare (fun _ => []) 0 2 rfl bs qs as diff B (Q-a) Q hB hb hd (Nat.sub_le _ _) wb wd
  have h₁ := product_hoare ds₁ 1 1 (by simp [ds₁]) bs qs as diff B a Q hB hb ha' ha wb wa
  have h₂ := product_hoare ds₂ 2 0 (by simp [ds₂,ds₁]) bs qs as diff B Q Q hB hb hq le_rfl wb wq
  have hfinal : Function.update ds₂ 2 (GrowingCounterData.advance (Q*B) []) = descriptors Q a B := by
    funext j
    fin_cases j <;> simp [ds₂,ds₁,descriptors]
  rw [hfinal] at h₂
  apply ((h₀.seq h₁).seq h₂).consequence (fun _ h => h) (fun _ h => h) _
  omega

/-- Place the subtraction inputs/output in the immutable Q, immutable a, and
scratch difference slots. -/
def subtractionPlacement : Fin (3+7) ≃ Fin 10 :=
  ((Equiv.swap 0 7).trans (Equiv.swap 1 8)).trans (Equiv.swap 2 9)

def subtractionProgram : Program 10 13 0 :=
  Placement.placed BinarySubReuse.program subtractionPlacement

private theorem active_subtraction (ds : Fin 3 → List Bool) (bs qs as : List Bool)
    (diff : ℤ → Fin 4) (r : ℤ) :
    Placement.active subtractionPlacement (bank ds bs qs as diff r) =
      BinarySubReuse.bank qs as diff 1 1 r := by
  unfold Placement.active subtractionPlacement bank extras TranslationProduct.bank ScalingDescriptors.innerBank
    ScalingDescriptors.counters CountedLoopReuse.bank CountedLoopReuse.controls Tapes.append
    BinarySubReuse.bank BinarySubReuse.cfg BinarySub.cfg Config.tapes
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem replace_subtraction (ds : Fin 3 → List Bool) (bs qs as : List Bool)
    (diff diff' : ℤ → Fin 4) (r r' : ℤ) :
    Placement.replace subtractionPlacement (bank ds bs qs as diff r)
      (BinarySubReuse.bank qs as diff' 1 1 r') = bank ds bs qs as diff' r' := by
  have he : Placement.extra subtractionPlacement (bank ds bs qs as diff r) =
      Placement.extra subtractionPlacement (bank ds bs qs as diff' r') := by
    unfold Placement.extra subtractionPlacement bank extras TranslationProduct.bank ScalingDescriptors.innerBank
      ScalingDescriptors.counters CountedLoopReuse.bank CountedLoopReuse.controls Tapes.append
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  rw [Placement.replace,he,← active_subtraction ds bs qs as diff' r']
  exact Placement.view _ _

/-- Physically compute Q-a, leaving all three writable product counters alone. -/
theorem subtraction_hoare (ds : Fin 3 → List Bool) (bs qs as : List Bool) :
    HoareTime subtractionProgram
      (fun v => v = bank ds bs qs as (fun _ => blank) 0)
      (fun v => v = bank ds bs qs as (binary (BinarySubReuse.difference qs as)) 1)
      (4*BinarySubReuse.width qs as+14) := by
  have hh := Placement.hoare_at (BinarySubReuse.sub_hoare qs as) subtractionPlacement
    (bank ds bs qs as (fun _ => blank) 0) (active_subtraction ds bs qs as _ 0)
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_subtraction _ _ _ _ _ _ _ _

/-- Full descriptor synthesis: real marker creation, immutable-input subtraction,
and three unary-counted binary products. The program has no numeric parameters. -/
def program : Program 10 120 0 :=
  seq (seq markerProgram subtractionProgram) productsProgram

/-- All arithmetic, setup, and loop costs are charged. The inputs are preserved,
all generated lengths are canonical, and all descriptor heads finish at one. -/
theorem descriptors_hoare (Q a B : ℕ) (ha : a ≤ Q) (hB : 0 < B) (bs qs as : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (ha' : Counter.value as = a)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (ca : GrowingCounterData.Canonical as) :
    HoareTime program (fun v => v = initial bs qs as)
      (fun v => v = bank (descriptors Q a B) bs qs as (binary (BinarySubReuse.difference qs as)) 1)
      (163*(Q*B)+92) := by
  have wb : bs.length ≤ B+1 := by
    have h := GrowingCounterData.canonical_width bs cb
    rw [hb] at h
    exact h.trans (Nat.add_le_add_right (Nat.log2_le_self _) 1)
  have wq : qs.length ≤ Q+1 := by
    have h := GrowingCounterData.canonical_width qs cq
    rw [hq] at h
    exact h.trans (Nat.add_le_add_right (Nat.log2_le_self _) 1)
  have wa : as.length ≤ Q+1 := by
    have h := GrowingCounterData.canonical_width as ca
    rw [ha'] at h
    have := Nat.log2_le_self a
    omega
  have wd : (BinarySubReuse.difference qs as).length ≤ Q+1 := by
    rw [BinarySubReuse.difference,BinarySubReuse.digits_length,BinarySubReuse.width]
    exact max_le wq wa
  have hd : Counter.value (BinarySubReuse.difference qs as) = Q-a := by
    rw [BinarySubReuse.difference_value qs as (by simpa only [hq,ha'] using ha),hq,ha']
  have hm := marker_hoare (initial bs qs as)
  rw [marker_initial] at hm
  have hs := subtraction_hoare (fun _ => []) bs qs as
  have hp := products_hoare Q a B ha hB bs qs as (BinarySubReuse.difference qs as)
    hb hq ha' hd wb wq wa wd
  apply ((hm.seq hs).seq hp).consequence (fun _ h => h) (fun _ h => h) _
  have hw : BinarySubReuse.width qs as ≤ Q+1 := max_le wq wa
  have hQB : Q ≤ Q*B := by nlinarith
  omega

end IntegerMultBounds.Machine.TranslationDescriptors
