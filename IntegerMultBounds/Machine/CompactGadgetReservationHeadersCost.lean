import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCaller

/-! A uniform linear-volume charge for every executed header instruction. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersCost
noncomputable section
open CompactGadgetReservationHeadersOps
open CompactGadgetReservationHeadersWords

def Within : Op → Words → ℕ → Prop
  | .constant N _,_,V => N ≤ V
  | .erase i,xs,V => value xs i ≤ V
  | .product f _,xs,V => value xs (f 1)*value xs (f 0) ≤ V
  | .difference f _,xs,V => value xs (f 0) ≤ V
  | .round f _,xs,V => RoundedRowDescriptor.rounded (value xs (f 0)) (value xs (f 1)) ≤ V
  | .power f _,xs,V => 2^value xs (f 0) ≤ V

def WithinList : List Op → Words → ℕ → Prop
  | [],_,_ => True
  | op::ops,xs,V => Within op xs V ∧ WithinList ops (transform op xs) V

def coefficient := 4196+FixedBasePowerDescriptor.constant 2

theorem length_bound (xs : List Bool) (hc : GrowingCounterData.Canonical xs) (V : ℕ)
    (hv : Counter.value xs ≤ V) (hV : 0 < V) : xs.length ≤ 2*V := by
  have hw := GrowingCounterData.canonical_width xs hc
  have hl := Nat.log2_le_self (Counter.value xs)
  omega

theorem one_bound (op : Op) (xs : Words) (V : ℕ) (hV : 0 < V)
    (hr : Ready op xs) (hw : Within op xs V) : cost op xs+1 ≤ coefficient*V := by
  have hconst := Nat.le_mul_of_pos_right 100 hV
  cases op with
  | constant N i =>
    have hl := length_bound (RecursiveChildQuotientsConstant.bits N)
      (RecursiveChildQuotientsConstant.bits_canonical N) V
      (by simpa only [Within,RecursiveChildQuotientsConstant.bits_value] using hw) hV
    simp only [cost,RecursiveChildQuotientsConstant.cost,coefficient]
    nlinarith
  | erase i =>
    have hl := length_bound (word xs i) hr.2 V hw hV
    simp only [cost,coefficient]
    nlinarith
  | product f hf => simp only [cost,Within,coefficient] at *; nlinarith
  | difference f hf => simp only [cost,Within,coefficient] at *; nlinarith
  | round f hf => simp only [cost,Within,coefficient] at *; nlinarith
  | power f hf => simp only [cost,Within,coefficient] at *; nlinarith

theorem list_bound (ops : List Op) (xs : Words) (V : ℕ) (hV : 0 < V)
    (hr : ReadyList ops xs) (hw : WithinList ops xs V) :
    bound ops xs ≤ ops.length*coefficient*V := by
  induction ops generalizing xs with
  | nil => simp [bound]
  | cons op ops ih =>
    have h1 := one_bound op xs V hV hr.1 hw.1
    have h2 := ih (transform op xs) hr.2 hw.2
    simp only [bound,List.length_cons]
    nlinarith

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersCost
