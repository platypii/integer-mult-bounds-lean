import IntegerMultBounds.Machine.BinaryDivide
import IntegerMultBounds.Machine.BinaryQuotientNormalize

/-! Raw words at cell one, long division, and physical quotient relocation.
The raw quotient tape is erased/head-zero; the sixth tape holds a canonical
marked quotient/head-one. The shifted raw remainder is deliberately explicit. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorDivisionRaw
variable {a : ℕ}
noncomputable section

def bank (f0 f1 f2 f3 f4 f5 : ℤ → Fin (a+4)) (p0 p1 p2 p3 p4 p5 : ℤ) : Tapes 6 a :=
  ⟨![p0,p1,p2,p3,p4,p5],![f0,f1,f2,f3,f4,f5]⟩

def placement : Fin (2+4) ≃ Fin 6 where
  toFun := ![4,5,0,1,2,3]
  invFun := ![2,3,4,5,0,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private theorem appended (f0 f1 f2 f3 f4 f5 : ℤ → Fin (a+4)) (p0 p1 p2 p3 p4 p5 : ℤ) :
    (BinaryDivide.bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4).append (FiniteReturnStack.bank f5 p5) =
      bank f0 f1 f2 f3 f4 f5 p0 p1 p2 p3 p4 p5 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem active (f0 f1 f2 f3 f4 f5 : ℤ → Fin (a+4)) (p0 p1 p2 p3 p4 p5 : ℤ) :
    Placement.active placement (bank f0 f1 f2 f3 f4 f5 p0 p1 p2 p3 p4 p5) = Copy.tapes f4 f5 p4 p5 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem replace (f0 f1 f2 f3 f4 f5 g4 g5 : ℤ → Fin (a+4)) (p0 p1 p2 p3 p4 p5 q4 q5 : ℤ) :
    Placement.replace placement (bank f0 f1 f2 f3 f4 f5 p0 p1 p2 p3 p4 p5) (Copy.tapes g4 g5 q4 q5) =
      bank f0 f1 f2 f3 g4 g5 p0 p1 p2 p3 q4 q5 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def program (a : ℕ) :=
  seq (extend (BinaryDivide.program a) 1) (Placement.placed BinaryQuotientNormalize.program placement)

def input (ys ds : List Bool) : Tapes 6 a :=
  bank (BinaryQuotientNormalize.raw ys 1) (BinaryQuotientNormalize.raw ds 1)
    (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) ys.length 1 0 0 0 0

def output (ys ds zs : List Bool) : Tapes 6 a :=
  bank (BinaryQuotientNormalize.raw ys 1) (BinaryQuotientNormalize.raw ds 1)
    (BinaryDivide.blankWord (-(ys.length : ℤ)) (BinaryDivide.remainder ds ys))
    (fun _ => blank) (fun _ => blank) (BinaryDescriptorStack.descriptor zs) 0 1 (-(ys.length : ℤ)) 0 0 1

/-- Actual normalized quotient, with arithmetic correctness and canonicality.
The precondition still exposes the divisor/dividend raw words and prepared head;
this is not a free conversion of marked runtime input descriptors. -/
theorem divide_hoare (ys ds : List Bool) (hd : 0 < Counter.value ds) :
    ∃ zs : List Bool, GrowingCounterData.Canonical zs ∧
      Counter.value zs = Counter.value ys / Counter.value ds ∧ zs.length ≤ ys.length ∧
      HoareTime (program a) (fun v => v = input ys ds) (fun v => v = output ys ds zs)
        ((∑ i ∈ Finset.range ys.length, (BinaryDivide.costAt ys ds i+2))+2*ys.length+9) := by
  have hdv := BinaryDivide.divide_hoare (a := a) ys ds (fun _ => blank) (fun _ => blank) 1 1 0 0 0 rfl rfl rfl
  have hext := hoare_extend_eq hdv (FiniteReturnStack.bank (a := a) (fun _ => blank) 0)
  simp only [appended,zero_sub] at hext
  have hcoord : (1 : ℤ)+ys.length-1 = ys.length := by omega
  rw [hcoord] at hext
  obtain ⟨zs,hcanon,hval,hlen,hnorm⟩ := BinaryQuotientNormalize.normalize_exists (a := a) (BinaryDivide.quotient ds ys) (-(ys.length : ℤ))
  have hq := BinaryDivide.quotient_length ds ys
  rw [hq] at hlen hnorm
  have hzero : -(ys.length : ℤ)+ys.length = 0 := by omega
  rw [hzero] at hnorm
  refine ⟨zs,hcanon,hval.trans (BinaryDivide.div_correct ds ys hd).2,hlen,?_⟩
  let middle := bank (BinaryQuotientNormalize.raw (a := a) ys 1) (BinaryQuotientNormalize.raw ds 1)
    (BinaryDivide.blankWord (-(ys.length : ℤ)) (BinaryDivide.remainder ds ys)) (fun _ => blank)
    (BinaryDivide.blankWord (-(ys.length : ℤ)) (BinaryDivide.quotient ds ys)) (fun _ => blank)
    0 1 (-(ys.length : ℤ)) 0 (-(ys.length : ℤ)) 0
  have hplaced := Placement.hoare_at hnorm placement middle (active _ _ _ _ _ _ _ _ _ _ _ _)
  have hp : HoareTime (Placement.placed BinaryQuotientNormalize.program placement)
      (fun v => v = middle) (fun v => v = output ys ds zs) (2*ys.length+8) := by
    apply hplaced.consequence (fun _ h => h) _ le_rfl
    rintro v ⟨z,rfl,rfl⟩
    exact replace _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact (hext.seq hp).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.BinaryDescriptorDivisionRaw
