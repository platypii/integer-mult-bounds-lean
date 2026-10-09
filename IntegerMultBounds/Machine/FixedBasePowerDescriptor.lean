import IntegerMultBounds.Machine.FixedBasePowerStep
import IntegerMultBounds.Machine.SharedBank

/-! A fixed finite program constructs B^k from a retained binary exponent.
The fixed base and initial one are physically written; reusable countdown
controls and the base constant are fully erased at the final boundary. -/
namespace IntegerMultBounds.Machine.FixedBasePowerDescriptor
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits cost)
variable {q : ℕ}

def input (ks : List Bool) : Tapes 8 q :=
  (SharedBank.empty 6 q).append (CountedLoopReuseAlphabet.controls
    (fun _ => blank) (CountedLoopReuseAlphabet.binary ks) 0 1)

def output (B k : ℕ) (ks : List Bool) : Tapes 8 q :=
  setTape (input ks) (5 : Fin 8) (RadixZeroFill.encodedBinary (FixedBasePowerStep.bits B k)) 1

def initializer (n : ℕ) (slot : Fin 8) :=
  Placement.placed (RecursiveChildQuotientsConstant.program (a := q) n) (FiniteReturnStackAt.placement slot)

def setup (B : ℕ) := seq (seq (initializer (q := q) B 3) (initializer 1 5)) (initializer 0 6)

def loop : Program 8 (7+(53+5)+4) q := CountedLoopReuseAlphabet.program FixedBasePowerStep.program

def cleanup : Program 8 (4+4) q := seq
  (BinaryDescriptorCleanupList.oneProgram (3 : Fin 8))
  (BinaryDescriptorCleanupList.oneProgram (6 : Fin 8))

def program (B : ℕ) := seq (seq (setup (q := q) B) loop) cleanup

def working (B i : ℕ) (ks : List Bool) : Tapes 8 q :=
  CountedLoopReuseAlphabet.bank (FixedBasePowerStep.input (bits B) (FixedBasePowerStep.bits B i))
    CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ks) 1 1

private theorem initialize_hoare (n : ℕ) (slot : Fin 8) (v : Tapes 8 q)
    (ht : v.tape slot = fun _ => blank) (hp : v.head slot = 0) :
    HoareTime (initializer n slot) (fun w => w = v)
      (fun w => w = setTape v slot (BinaryDescriptorStack.descriptor (bits n)) 1) (cost n) := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := q) n)
    (FiniteReturnStackAt.placement slot) v (by rw [FiniteReturnStackAt.active_bank,ht,hp])
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

private theorem setup_hoare (B : ℕ) (ks : List Bool) :
    HoareTime (setup (q := q) B) (fun v => v = input ks) (fun v => v = working B 0 ks)
      (cost B+cost 1+cost 0+2) := by
  let v1 := setTape (input (q := q) ks) (3 : Fin 8) (BinaryDescriptorStack.descriptor (bits B)) 1
  let v2 := setTape v1 (5 : Fin 8) (BinaryDescriptorStack.descriptor (bits 1)) 1
  have h1 := initialize_hoare B (3 : Fin 8) (input (q := q) ks) rfl rfl
  have h2 := initialize_hoare 1 (5 : Fin 8) v1 rfl rfl
  have h3 := initialize_hoare 0 (6 : Fin 8) v2 rfl rfl
  have he : setTape v2 (6 : Fin 8) (BinaryDescriptorStack.descriptor (bits 0)) 1 = working B 0 ks := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals first | rfl | exact BinaryDescriptorStackRoundtrip.descriptor_encoded _
  rw [he] at h3
  exact (h1.seq h2).seq h3

private theorem loop_hoare (B k : ℕ) (hB : 2 ≤ B) (ks : List Bool) (hk : Counter.value ks = k) :
    HoareTime (loop (q := q)) (fun v => v = working B 0 ks) (fun v => v = working B k ks)
      ((∑ i ∈ Finset.range k, 110*B^(i+1))+6*k+7*ks.length+16) := by
  exact CountedLoopReuseAlphabet.loop_hoare FixedBasePowerStep.program ks k
    (fun i => FixedBasePowerStep.input (bits B) (FixedBasePowerStep.bits B i)) (fun i => 110*B^(i+1)) hk
    (fun i _ => FixedBasePowerStep.power_step (bits B) B i hB
      (RecursiveChildQuotientsConstant.bits_value B) (RecursiveChildQuotientsConstant.bits_canonical B))

private theorem cleanup_hoare (B k : ℕ) (ks : List Bool) :
    HoareTime (cleanup (q := q)) (fun v => v = working B k ks) (fun v => v = output B k ks)
      (2*(bits B).length+9) := by
  let vv := setTape (working (q := q) B k ks) (3 : Fin 8) (fun _ => blank) 0
  have h1 := BinaryDescriptorCleanupList.one_hoare (3 : Fin 8) (working (q := q) B k ks) (bits B)
    (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl
  have h2 := BinaryDescriptorCleanupList.one_hoare (6 : Fin 8) vv [] rfl rfl
  have he : setTape vv (6 : Fin 8) (fun _ => blank) 0 = output B k ks := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h2
  exact (h1.seq h2).consequence (fun _ h => h) (fun _ h => h) (by simp only [List.length_nil]; omega)

def exactCost (B k : ℕ) (ks : List Bool) :=
  cost B+cost 1+cost 0+2+(∑ i ∈ Finset.range k, 110*B^(i+1))+6*k+7*ks.length+16+
    (2*(bits B).length+9)+2

theorem constructs (B k : ℕ) (hB : 2 ≤ B) (ks : List Bool) (hk : Counter.value ks = k) :
    HoareTime (program (q := q) B) (fun v => v = input ks) (fun v => v = output B k ks)
      (exactCost B k ks) := by
  exact (((setup_hoare B ks).seq (loop_hoare B k hB ks hk)).seq (cleanup_hoare B k ks)).consequence
    (fun _ h => h) (fun _ h => h) (by unfold exactCost; omega)

/-- Geometric sum bound checked for a symbolic fixed base, without evaluating
any of the large constants used by the multiplication construction. -/
theorem geometric (B k : ℕ) (hB : 2 ≤ B) :
    (∑ i ∈ Finset.range k, B^(i+1))+2 ≤ 2*B^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hm : 2*B^k ≤ B^(k+1) := by
      rw [pow_succ]
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (B^k) hB
    omega

theorem depth_le_power (B k : ℕ) (hB : 2 ≤ B) : k+1 ≤ B^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    nlinarith

/-- One constant for one fixed compile-time base, independent of the exponent
and its canonical runtime encoding. -/
def constant (B : ℕ) := cost B+cost 1+cost 0+2*(bits B).length+300

theorem cost_linear (B k : ℕ) (hB : 2 ≤ B) (ks : List Bool)
    (hk : Counter.value ks = k) (ck : GrowingCounterData.Canonical ks) :
    exactCost B k ks ≤ constant B*B^k := by
  have hg := geometric B k hB
  have hp := depth_le_power B k hB
  have hlen := GrowingCounterData.canonical_width ks ck
  rw [hk] at hlen
  have hlog := Nat.log2_le_self k
  have hl : ks.length ≤ B^k := by omega
  have hC := Nat.mul_le_mul_left (cost B+cost 1+cost 0+2*(bits B).length+67)
    (show 1 ≤ B^k by omega)
  unfold exactCost constant
  rw [← Finset.mul_sum]
  nlinarith

/-- Complete canonical fixed-base power synthesis with all permanent scratch
cleaned and the original exponent descriptor literally retained. -/
theorem constructs_linear (B k : ℕ) (hB : 2 ≤ B) (ks : List Bool)
    (hk : Counter.value ks = k) (ck : GrowingCounterData.Canonical ks) :
    HoareTime (program (q := q) B) (fun v => v = input ks) (fun v => v = output B k ks)
      (constant B*B^k) :=
  (constructs B k hB ks hk).consequence (fun _ h => h) (fun _ h => h) (cost_linear B k hB ks hk ck)

/-- The emitted word is canonical and names the actual integer power. -/
theorem result_value (B k : ℕ) : Counter.value (FixedBasePowerStep.bits B k) = B^k :=
  FixedBasePowerStep.bits_value B k

theorem result_canonical (B k : ℕ) : GrowingCounterData.Canonical (FixedBasePowerStep.bits B k) :=
  FixedBasePowerStep.bits_canonical B k

end
end IntegerMultBounds.Machine.FixedBasePowerDescriptor
