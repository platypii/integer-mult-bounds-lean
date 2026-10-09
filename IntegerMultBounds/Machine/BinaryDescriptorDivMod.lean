import IntegerMultBounds.Machine.BinaryDescriptorDivision
import IntegerMultBounds.Machine.FixedBasePowerUntilBound

/-! Physical quotient and remainder extraction from marked binary inputs.
The shifted long-division remainder is copied, erased and normalized; tracking
then restores every private tape and head, including its shifted source head. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorDivMod
noncomputable section
variable {a : ℕ}

def bank (f0 f1 f2 f3 f4 f5 f6 : ℤ → Fin (a+4)) (p0 p1 p2 p3 p4 p5 p6 : ℤ) : Tapes 7 a :=
  ⟨![p0,p1,p2,p3,p4,p5,p6],![f0,f1,f2,f3,f4,f5,f6]⟩

def placement : Fin (2+5) ≃ Fin 7 where
  toFun := ![2,6,0,1,3,4,5]
  invFun := ![2,3,0,4,5,6,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def initial (ys ds : List Bool) : Tapes 7 a :=
  (BinaryDescriptorDivisionBoundary.input ys ds).append (FiniteReturnStack.bank (fun _ => blank) 0)

def middle (ys ds zs : List Bool) : Tapes 7 a :=
  (BinaryDescriptorDivisionBoundary.output ys ds zs).append (FiniteReturnStack.bank (fun _ => blank) 0)

def normalized (ys ds zs rs : List Bool) : Tapes 7 a :=
  bank (BinaryDescriptorStack.descriptor ys) (BinaryDescriptorStack.descriptor ds)
    (fun _ => blank) (fun _ => blank) (fun _ => blank)
    (BinaryDescriptorStack.descriptor zs) (BinaryDescriptorStack.descriptor rs)
    1 1 (-(ys.length : ℤ)+(BinaryDivide.remainder ds ys).length) 0 0 1 1

def core (a : ℕ) := seq (extend (BinaryDescriptorDivision.core a) 1)
  (Placement.placed BinaryQuotientNormalize.program placement)

def right : Fin 7 → Bool := ![true,true,false,false,false,false,false]
def keep : Fin 7 → Bool := ![true,true,false,false,false,true,true]
def program (a : ℕ) := CleanExecution.program (core a) right keep

def retained (ys ds zs rs : List Bool) : Tapes 7 a :=
  bank (BinaryDescriptorStack.descriptor ys) (BinaryDescriptorStack.descriptor ds)
    (fun _ => blank) (fun _ => blank) (fun _ => blank)
    (BinaryDescriptorStack.descriptor zs) (BinaryDescriptorStack.descriptor rs) 1 1 0 0 0 1 1

def input (ys ds : List Bool) : Tapes 14 a := (initial ys ds).append (SharedBank.empty 7 a)
def output (ys ds zs rs : List Bool) : Tapes 14 a := (retained ys ds zs rs).append (SharedBank.empty 7 a)

def coreCost (ys ds : List Bool) :=
  (∑ i ∈ Finset.range ys.length, (BinaryDivide.costAt ys ds i+2))+5*ys.length+2*ds.length+29
def cost (ys ds : List Bool) := 37*coreCost ys ds+81

theorem divmod_hoare (ys ds : List Bool) (hd : 0 < Counter.value ds) :
    ∃ zs rs : List Bool, GrowingCounterData.Canonical zs ∧ GrowingCounterData.Canonical rs ∧
      Counter.value zs = Counter.value ys/Counter.value ds ∧
      Counter.value rs = Counter.value ys%Counter.value ds ∧ zs.length ≤ ys.length ∧
      rs.length ≤ ys.length+ds.length ∧
      HoareTime (program a) (fun v => v = input ys ds) (fun v => v = output ys ds zs rs) (cost ys ds) := by
  obtain ⟨zs,hzc,hzv,hzl,hdiv⟩ := BinaryDescriptorDivisionRaw.divide_hoare (a := a) ys ds hd
  have hc : HoareTime (BinaryDescriptorDivision.core a)
      (fun v => v = BinaryDescriptorDivisionBoundary.input ys ds)
      (fun v => v = BinaryDescriptorDivisionBoundary.output ys ds zs)
      (BinaryDescriptorDivision.coreCost ys ds) := by
    exact (((BinaryDescriptorDivisionBoundary.prepare_hoare ys ds).seq hdiv).seq
      (BinaryDescriptorDivisionBoundary.finish_hoare ys ds zs)).consequence (fun _ h => h) (fun _ h => h)
      (by unfold BinaryDescriptorDivision.coreCost; omega)
  have hc' := hoare_extend_eq hc (FiniteReturnStack.bank (a := a) (fun _ => blank) 0)
  obtain ⟨rs,hrc,hrv,hrl,hn⟩ := BinaryQuotientNormalize.normalize_exists (a := a)
    (BinaryDivide.remainder ds ys) (-(ys.length : ℤ))
  have ha : Placement.active placement (middle (a := a) ys ds zs) =
      Copy.tapes (BinaryQuotientNormalize.raw (BinaryDivide.remainder ds ys) (-(ys.length : ℤ)))
        (fun _ => blank) (-(ys.length : ℤ)) 0 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hr := Placement.hoare_at hn placement (middle (a := a) ys ds zs) ha
  have hr' : HoareTime (Placement.placed (BinaryQuotientNormalize.program (a := a)) placement)
      (fun v => v = middle ys ds zs) (fun v => v = normalized ys ds zs rs)
      (2*(BinaryDivide.remainder ds ys).length+8) := by
    apply hr.consequence (fun _ h => h) _ le_rfl
    rintro v ⟨w,rfl,rfl⟩
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hlen := BinaryDivide.remainder_length ds ys
  have hcore : HoareTime (core a) (fun v => v = initial ys ds)
      (fun v => v = normalized ys ds zs rs) (coreCost ys ds) := by
    exact (hc'.seq hr').consequence (fun _ h => h) (fun _ h => h)
      (by unfold coreCost BinaryDescriptorDivision.coreCost; omega)
  have hheads : (initial (a := a) ys ds).head = TrackedInit.position right := by
    funext i; fin_cases i <;> rfl
  have hblank : ∀ i, keep i = false → (initial (a := a) ys ds).tape i = fun _ => blank := by
    intro i hi; fin_cases i <;> simp [keep] at hi <;> rfl
  have hclean := CleanExecution.realizes (core a) right keep (initial ys ds) (normalized ys ds zs rs)
    (coreCost ys ds) hheads hblank hcore
  have he : TrackedCleanupList.retained keep (normalized (a := a) ys ds zs rs) = retained ys ds zs rs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [keep,normalized,bank]
  rw [he] at hclean
  exact ⟨zs,rs,hzc,hrc,hzv,hrv.trans (BinaryDivide.div_correct ds ys hd).1,hzl,
    hrl.trans hlen,hclean⟩

theorem cost_le (ys ds : List Bool) :
    cost ys ds ≤ 37*(ys.length*(4*ys.length+6*ds.length+32)+2*ds.length+29)+81 := by
  have h := BinaryDivide.cost_le ys ds
  unfold cost coreCost
  nlinarith

theorem descriptor_square (ys : List Bool) (hc : GrowingCounterData.Canonical ys) :
    ys.length^2 ≤ 8*(Counter.value ys+1) := by
  have hw := GrowingCounterData.canonical_width ys hc
  have hs := FixedBasePowerUntilBound.square_le_power 2 (Counter.value ys).log2 (by omega)
  have hp : 2^(Counter.value ys).log2 ≤ Counter.value ys+1 := by
    simpa only [Nat.log2_eq_log_two] using Nat.pow_log_le_add_one 2 (Counter.value ys)
  nlinarith

def linearConstant (ds : List Bool) := 37*(8*ds.length+93)+81

theorem cost_linear (ys ds : List Bool) (hc : GrowingCounterData.Canonical ys) :
    cost ys ds ≤ linearConstant ds*(Counter.value ys+1) := by
  have hb := cost_le ys ds
  have hs := descriptor_square ys hc
  have hw := GrowingCounterData.canonical_width ys hc
  have hl := Nat.log2_le_self (Counter.value ys)
  have hlen : ys.length ≤ Counter.value ys+1 := by omega
  have hm := Nat.mul_le_mul_left (6*ds.length+32) hlen
  have hp := Nat.mul_le_mul_left (2*ds.length+29) (show 1 ≤ Counter.value ys+1 by omega)
  unfold linearConstant
  nlinarith

/-- At a fixed divisor the complete arithmetic/control boundary has linear
overhead in the runtime dividend, with both results canonical and all scratch
physically erased. The constant depends only on the fixed divisor word. -/
theorem divmod_linear (ys ds : List Bool) (hd : 0 < Counter.value ds)
    (hc : GrowingCounterData.Canonical ys) :
    ∃ zs rs : List Bool, GrowingCounterData.Canonical zs ∧ GrowingCounterData.Canonical rs ∧
      Counter.value zs = Counter.value ys/Counter.value ds ∧
      Counter.value rs = Counter.value ys%Counter.value ds ∧ zs.length ≤ ys.length ∧
      rs.length ≤ ys.length+ds.length ∧
      HoareTime (program a) (fun v => v = input ys ds) (fun v => v = output ys ds zs rs)
        (linearConstant ds*(Counter.value ys+1)) := by
  obtain ⟨zs,rs,hzc,hrc,hzv,hrv,hzl,hrl,h⟩ := divmod_hoare (a := a) ys ds hd
  exact ⟨zs,rs,hzc,hrc,hzv,hrv,hzl,hrl,h.consequence (fun _ h => h) (fun _ h => h) (cost_linear ys ds hc)⟩

end
end IntegerMultBounds.Machine.BinaryDescriptorDivMod
