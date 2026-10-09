import IntegerMultBounds.Machine.FixedBasePowerUntilBound
import IntegerMultBounds.Machine.BinaryDescriptorCompare
import IntegerMultBounds.Machine.BinaryDescriptorIncrement
import IntegerMultBounds.Machine.LoopChain

/-! The fixed-base threshold loop on nine permanent tapes. The threshold is
runtime data; neither the loop nor any of its finite subprograms depends on
the threshold or on the eventual stopping exponent. -/
namespace IntegerMultBounds.Machine.FixedBasePowerUntil
noncomputable section
variable {q : ℕ}
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits cost)

def counter : ℕ → List Bool
  | 0 => []
  | i+1 => GrowingCounterData.increment (counter i)

theorem counter_value (i : ℕ) : Counter.value (counter i) = i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [counter,BinaryDescriptorIncrement.value,ih]

theorem counter_canonical (i : ℕ) : GrowingCounterData.Canonical (counter i) := by
  induction i with
  | zero => exact Or.inl rfl
  | succ i ih => exact BinaryDescriptorIncrement.canonical _ ih

def tail (ds rs : List Bool) (flag : ℤ → Fin (q+4)) : Tapes 3 q :=
  ⟨![1,1,0],![BinaryDescriptorStack.descriptor ds,BinaryDescriptorStack.descriptor rs,flag]⟩

def bank (ws ps ds rs : List Bool) (flag : ℤ → Fin (q+4)) : Tapes 9 q :=
  (FixedBasePowerStep.input ws ps).append (tail ds rs flag)

def working (B i : ℕ) (ds : List Bool) : Tapes 9 q :=
  bank (bits B) (FixedBasePowerStep.bits B i) ds (counter i)
    (BinaryDescriptorCompare.result (FixedBasePowerStep.bits B i) ds)

def cleared (B i : ℕ) (ds : List Bool) : Tapes 9 q :=
  bank (bits B) (FixedBasePowerStep.bits B i) ds (counter i) (fun _ => blank)

def comparePlacement : Fin (3+6) ≃ Fin 9 :=
  ((Equiv.swap (0 : Fin 9) 5).trans (Equiv.swap 1 6)).trans (Equiv.swap 2 8)

def compare : Program 9 12 q := Placement.placed BinaryDescriptorCompare.program comparePlacement

private theorem compare_active (ws ps ds rs : List Bool) :
    Placement.active comparePlacement (bank (q := q) ws ps ds rs (fun _ => blank)) =
      BinaryDescriptorCompare.input ps ds := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact (BinaryDescriptorStackRoundtrip.descriptor_encoded ps).symm

private theorem compare_replace (ws ps ds rs : List Bool) :
    Placement.replace comparePlacement (bank (q := q) ws ps ds rs (fun _ => blank))
      (BinaryDescriptorCompare.output ps ds) = bank ws ps ds rs (BinaryDescriptorCompare.result ps ds) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact BinaryDescriptorStackRoundtrip.descriptor_encoded ps

theorem compare_hoare (ws ps ds rs : List Bool) :
    HoareTime (compare (q := q)) (fun v => v = bank ws ps ds rs (fun _ => blank))
      (fun v => v = bank ws ps ds rs (BinaryDescriptorCompare.result ps ds))
      (BinaryDescriptorCompare.cost ps ds) := by
  have h := Placement.hoare_at (BinaryDescriptorCompare.compare_hoare (q := q) ps ds)
    comparePlacement (bank ws ps ds rs (fun _ => blank)) (compare_active ws ps ds rs)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact compare_replace ws ps ds rs

def erase : Program 9 2 q := DescriptorStackControl.once (by decide)
  (fun sy i => (if i = 8 then blank else sy i,.stay))

theorem erase_hoare (ws ps ds rs : List Bool) :
    HoareTime (erase (q := q)) (fun v => v = bank ws ps ds rs (BinaryDescriptorCompare.result ps ds))
      (fun v => v = bank ws ps ds rs (fun _ => blank)) 1 := by
  apply (DescriptorStackControl.once_hoare (by decide) _
    (bank (q := q) ws ps ds rs (BinaryDescriptorCompare.result ps ds))).consequence
    (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk
  · funext i
    fin_cases i <;> rfl
  · funext i z
    fin_cases i
    · change (if z = 0 then blank else blank) = blank
      split_ifs <;> rfl
    · change (if z = 0 then blank else blank) = blank
      split_ifs <;> rfl
    · change (if z = 0 then blank else blank) = blank
      split_ifs <;> rfl
    · change (if z = 1 then RadixZeroFill.encodedBinary ws 1 else RadixZeroFill.encodedBinary ws z) = _
      split_ifs with h
      · rw [h]; rfl
      · rfl
    · change (if z = 0 then blank else blank) = blank
      split_ifs <;> rfl
    · change (if z = 1 then RadixZeroFill.encodedBinary ps 1 else RadixZeroFill.encodedBinary ps z) = _
      split_ifs with h
      · rw [h]; rfl
      · rfl
    · change (if z = 1 then BinaryDescriptorStack.descriptor ds 1 else BinaryDescriptorStack.descriptor ds z) = _
      split_ifs with h
      · rw [h]; rfl
      · rfl
    · change (if z = 1 then BinaryDescriptorStack.descriptor rs 1 else BinaryDescriptorStack.descriptor rs z) = _
      split_ifs with h
      · rw [h]; rfl
      · rfl
    · change (if z = 0 then blank else BinaryDescriptorCompare.result ps ds z) = blank
      by_cases hz : z = 0 <;> simp [hz,BinaryDescriptorCompare.result]

def increment : Program 9 3 q := Placement.placed BinaryDescriptorIncrement.program
  (FiniteReturnStackAt.placement (7 : Fin 9))

theorem increment_hoare (ws ps ds rs : List Bool) :
    HoareTime (increment (q := q)) (fun v => v = bank ws ps ds rs (fun _ => blank))
      (fun v => v = bank ws ps ds (GrowingCounterData.increment rs) (fun _ => blank))
      (2*(rs.length+1)) := by
  have h := Placement.hoare_at (BinaryDescriptorIncrement.increment_linear (q := q) rs)
    (FiniteReturnStackAt.placement (7 : Fin 9)) (bank ws ps ds rs (fun _ => blank))
    (by rw [FiniteReturnStackAt.active_bank]; rfl)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (BinaryDescriptorStack.descriptor
    (GrowingCounterData.increment rs)) 1) = _
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def body : Program 9 (((2+53)+3)+12) q := seq (seq (seq erase
  (extend FixedBasePowerStep.program 3)) increment) compare

def bodyCost (B i : ℕ) (ds : List Bool) :=
  110*B^(i+1)+2*((counter i).length+1)+
    BinaryDescriptorCompare.cost (FixedBasePowerStep.bits B (i+1)) ds+4

theorem body_hoare (B i : ℕ) (hB : 2 ≤ B) (ds : List Bool) :
    HoareTime (body (q := q)) (fun v => v = working B i ds)
      (fun v => v = working B (i+1) ds) (bodyCost B i ds) := by
  have he := erase_hoare (q := q) (bits B) (FixedBasePowerStep.bits B i) ds (counter i)
  have hp := (FixedBasePowerStep.power_step (q := q) (bits B) B i hB
    (RecursiveChildQuotientsConstant.bits_value B) (RecursiveChildQuotientsConstant.bits_canonical B)).extend
      (tail (q := q) ds (counter i) (fun _ => blank))
  have hp' : HoareTime (extend (FixedBasePowerStep.program (q := q)) 3)
      (fun v => v = cleared B i ds)
      (fun v => v = bank (bits B) (FixedBasePowerStep.bits B (i+1)) ds (counter i) (fun _ => blank))
      (110*B^(i+1)) := by
    apply hp.consequence _ _ le_rfl
    · intro v hv; exact ⟨_,rfl,hv⟩
    · rintro v ⟨w,rfl,hv⟩; exact hv
  have hi := increment_hoare (q := q) (bits B) (FixedBasePowerStep.bits B (i+1)) ds (counter i)
  have hc := compare_hoare (q := q) (bits B) (FixedBasePowerStep.bits B (i+1)) ds (counter (i+1))
  exact (((he.seq hp').seq hi).seq hc).consequence (fun _ h => h) (fun _ h => h)
    (by unfold bodyCost; omega)

def test (sy : Fin 9 → Fin (q+4)) : Bool := sy 8 == bitSymbol true
def loop : Program 9 (1+(((2+53)+3)+12)) q := whileLoop body test

theorem loop_hoare (B D : ℕ) (hB : 2 ≤ B) (ds : List Bool) (hd : Counter.value ds = D) :
    HoareTime (loop (q := q)) (fun v => v = working B 0 ds)
      (fun v => v = working B (FixedBasePowerUntilBound.rho B D) ds)
      (∑ i ∈ Finset.range (FixedBasePowerUntilBound.rho B D), (bodyCost B i ds+2)) := by
  apply while_chain_hoare body test (fun i => working B i ds) (fun i => bodyCost B i ds)
  · intro i _; exact body_hoare B i hB ds
  · intro i hi
    have hlt := FixedBasePowerUntilBound.before B D i hB hi
    change (BinaryDescriptorCompare.result (FixedBasePowerStep.bits B i) ds 0 == bitSymbol true) = true
    simp [BinaryDescriptorCompare.result,
      FixedBasePowerStep.bits_value,hd,hlt]
  · have hle := FixedBasePowerUntilBound.dominates B D hB
    change (BinaryDescriptorCompare.result (FixedBasePowerStep.bits B (FixedBasePowerUntilBound.rho B D)) ds 0 == bitSymbol true) = false
    simp [BinaryDescriptorCompare.result,bitSymbol,Fin.ext_iff,
      FixedBasePowerStep.bits_value,hd,show ¬B^FixedBasePowerUntilBound.rho B D < D by omega]

def input (ds : List Bool) : Tapes 9 q :=
  setTape (SharedBank.empty 9 q) (6 : Fin 9) (BinaryDescriptorStack.descriptor ds) 1

def output (B r : ℕ) (ds : List Bool) : Tapes 9 q :=
  setTape (setTape (input ds) (5 : Fin 9) (RadixZeroFill.encodedBinary (FixedBasePowerStep.bits B r)) 1)
    (7 : Fin 9) (BinaryDescriptorStack.descriptor (counter r)) 1

def initializer (n : ℕ) (slot : Fin 9) := Placement.placed
  (RecursiveChildQuotientsConstant.program (a := q) n) (FiniteReturnStackAt.placement slot)

private theorem initialize_hoare (n : ℕ) (slot : Fin 9) (v : Tapes 9 q)
    (ht : v.tape slot = fun _ => blank) (hp : v.head slot = 0) :
    HoareTime (initializer n slot) (fun w => w = v)
      (fun w => w = setTape v slot (BinaryDescriptorStack.descriptor (bits n)) 1) (cost n) := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := q) n)
    (FiniteReturnStackAt.placement slot) v (by rw [FiniteReturnStackAt.active_bank,ht,hp])
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

def setup (B : ℕ) := seq (seq (seq (initializer (q := q) B 3) (initializer 1 5))
  (initializer 0 7)) compare

def setupCost (B : ℕ) (ds : List Bool) := cost B+cost 1+cost 0+
  BinaryDescriptorCompare.cost (FixedBasePowerStep.bits B 0) ds+3

theorem setup_hoare (B : ℕ) (ds : List Bool) :
    HoareTime (setup (q := q) B) (fun v => v = input ds)
      (fun v => v = working B 0 ds) (setupCost B ds) := by
  let v1 := setTape (input (q := q) ds) (3 : Fin 9) (BinaryDescriptorStack.descriptor (bits B)) 1
  let v2 := setTape v1 (5 : Fin 9) (BinaryDescriptorStack.descriptor (bits 1)) 1
  have h1 := initialize_hoare B (3 : Fin 9) (input (q := q) ds) rfl rfl
  have h2 := initialize_hoare 1 (5 : Fin 9) v1 rfl rfl
  have h3 := initialize_hoare 0 (7 : Fin 9) v2 rfl rfl
  have he : setTape v2 (7 : Fin 9) (BinaryDescriptorStack.descriptor (bits 0)) 1 = cleared B 0 ds := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals first | rfl | exact BinaryDescriptorStackRoundtrip.descriptor_encoded _
  rw [he] at h3
  have hc := compare_hoare (q := q) (bits B) (FixedBasePowerStep.bits B 0) ds (counter 0)
  exact (((h1.seq h2).seq h3).seq hc).consequence (fun _ h => h) (fun _ h => h)
    (by unfold setupCost; omega)

def cleanup : Program 9 (2+4) q := seq erase (BinaryDescriptorCleanupList.oneProgram (3 : Fin 9))

theorem cleanup_hoare (B r : ℕ) (ds : List Bool) :
    HoareTime (cleanup (q := q)) (fun v => v = working B r ds)
      (fun v => v = output B r ds) (2*(bits B).length+6) := by
  have he := erase_hoare (q := q) (bits B) (FixedBasePowerStep.bits B r) ds (counter r)
  have hc := BinaryDescriptorCleanupList.one_hoare (3 : Fin 9) (cleared (q := q) B r ds)
    (bits B) (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl
  have hf : setTape (cleared (q := q) B r ds) (3 : Fin 9) (fun _ => blank) 0 = output B r ds := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [hf] at hc
  exact (he.seq hc).consequence (fun _ h => h) (fun _ h => h) (by omega)

def program (B : ℕ) := seq (seq (setup (q := q) B) loop) cleanup

def exactCost (B r : ℕ) (ds : List Bool) := setupCost B ds+
  (∑ i ∈ Finset.range r, (bodyCost B i ds+2))+(2*(bits B).length+6)+2

theorem constructs (B D : ℕ) (hB : 2 ≤ B) (ds : List Bool) (hd : Counter.value ds = D) :
    HoareTime (program (q := q) B) (fun v => v = input ds)
      (fun v => v = output B (FixedBasePowerUntilBound.rho B D) ds)
      (exactCost B (FixedBasePowerUntilBound.rho B D) ds) := by
  exact (((setup_hoare B ds).seq (loop_hoare B D hB ds hd)).seq
    (cleanup_hoare B (FixedBasePowerUntilBound.rho B D) ds)).consequence
    (fun _ h => h) (fun _ h => h) (by unfold exactCost; omega)

private theorem bodyCost_bound (B r i : ℕ) (hB : 2 ≤ B) (hi : i < r) (ds : List Bool) :
    bodyCost B i ds+2 ≤ 150*B^(i+1)+2*(r+1)+2*ds.length := by
  have hc := GrowingCounterData.canonical_width (counter i) (counter_canonical i)
  rw [counter_value] at hc
  have hcl := Nat.log2_le_self i
  have hp := GrowingCounterData.canonical_width (FixedBasePowerStep.bits B (i+1))
    (FixedBasePowerStep.bits_canonical B (i+1))
  rw [FixedBasePowerStep.bits_value] at hp
  have hpl := Nat.log2_le_self (B^(i+1))
  have hpos := FixedBasePowerDescriptor.depth_le_power B (i+1) hB
  have hm : max (FixedBasePowerStep.bits B (i+1)).length ds.length ≤
      (FixedBasePowerStep.bits B (i+1)).length+ds.length := by omega
  unfold bodyCost BinaryDescriptorCompare.cost
  omega

def constant (B : ℕ) := cost B+cost 1+cost 0+2*(bits B).length+340+16*(B+1)

theorem cost_linear (B D : ℕ) (hB : 2 ≤ B) (ds : List Bool)
    (hd : Counter.value ds = D) (cd : GrowingCounterData.Canonical ds) :
    exactCost B (FixedBasePowerUntilBound.rho B D) ds ≤
      constant B*B^(FixedBasePowerUntilBound.rho B D) := by
  let r := FixedBasePowerUntilBound.rho B D
  have hg := FixedBasePowerDescriptor.geometric B r hB
  have hs := FixedBasePowerUntilBound.square_le_power B r hB
  have hdscan := FixedBasePowerUntilBound.repeated_scan B D r hB
    (FixedBasePowerUntilBound.dominates B D hB) ds hd cd
  have hsum : (∑ i ∈ Finset.range r, (bodyCost B i ds+2)) ≤
      150*(∑ i ∈ Finset.range r, B^(i+1))+2*r*(r+1)+2*r*ds.length := by
    calc
      _ ≤ ∑ i ∈ Finset.range r, (150*B^(i+1)+2*(r+1)+2*ds.length) := by
        apply Finset.sum_le_sum
        intro i hi
        exact bodyCost_bound B r i hB (Finset.mem_range.mp hi) ds
      _ = _ := by simp [Finset.sum_add_distrib,← Finset.mul_sum]; ring
  have hlen : (FixedBasePowerStep.bits B 0).length ≤ 1 := by
    have h := GrowingCounterData.canonical_width (FixedBasePowerStep.bits B 0)
      (FixedBasePowerStep.bits_canonical B 0)
    rw [FixedBasePowerStep.bits_value,pow_zero] at h
    exact h
  have hm : max (FixedBasePowerStep.bits B 0).length ds.length ≤
      (FixedBasePowerStep.bits B 0).length+ds.length := by omega
  have hsetup : setupCost B ds ≤ cost B+cost 1+cost 0+2*ds.length+16 := by
    unfold setupCost BinaryDescriptorCompare.cost
    omega
  have hpos := FixedBasePowerDescriptor.depth_le_power B r hB
  have hconst := Nat.mul_le_mul_left (cost B+cost 1+cost 0+2*(bits B).length+24)
    (show 1 ≤ B^r by omega)
  change exactCost B r ds ≤ constant B*B^r
  unfold exactCost constant
  nlinarith

theorem constructs_linear (B D : ℕ) (hB : 2 ≤ B) (ds : List Bool)
    (hd : Counter.value ds = D) (cd : GrowingCounterData.Canonical ds) :
    HoareTime (program (q := q) B) (fun v => v = input ds)
      (fun v => v = output B (FixedBasePowerUntilBound.rho B D) ds)
      (constant B*B^(FixedBasePowerUntilBound.rho B D)) :=
  (constructs B D hB ds hd).consequence (fun _ h => h) (fun _ h => h) (cost_linear B D hB ds hd cd)

end
end IntegerMultBounds.Machine.FixedBasePowerUntil
