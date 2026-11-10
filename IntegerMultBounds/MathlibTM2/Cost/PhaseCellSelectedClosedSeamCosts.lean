module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFullLineLifecycle
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedClosedSeamRun

/-! Apply the existing selected full-period bounds to the actual closed solve
and its at-most-three seam crops. Numerical readiness is derived from inputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement FullLineInputPlan

theorem selectedClosedSeamCosts_le (ct : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
    ∀ (T Q A : ℕ) (U : Type) (input : FullLineInputPlan T) (producer : PackedProducerPlan T Q)
      (d : ℝ) (u target : ℕ) (Fs : List (ZMod (Sizes.s m i) → GaussianInt))
      (v : HS T Q A U) (S : Stacks T A),
    u ≤ Sizes.p m → target ≤ ct*Sizes.p m → 1 ≤ u → 8*Sizes.p m ≤ 2^u →
    (u : ℝ)*d ≤ Sizes.p m → PhaseCellBand.width (Sizes.p m) u ≤ Sizes.s m i →
    let p := Sizes.p m
    let s := Sizes.s m i
    let t := Sizes.t m i
    let l := haloInverseRingLog s t
    2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1 →
    (∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1) → input.Ready p u l target t Fs S →
    let C := gridDispatchPush (U := U) (A := A) producer.hR producer.hQ
    let r := fullLineGridRecord (A := A) p u l target t Fs
    let tape := descriptorScheduleTape producer.gridWork FamilyDispatchInput.words [r]
    let solveTime := setupTime p u l target s t Fs.length+
      ((r.gridCost p l t producer.gridWork+22*tape.length+26)+(2*(∑ j, (r.words j).length)+607))
    let solveStock := setupStock p u l target s t Fs.length+(31*tape.length+9+(C+1)*producer.gridStock p l t r)
    let volume := r.inputs.length*s*(2*p+13)
    ((solveTime+(242*volume+45) : ℕ) : ℝ) ≤ 2624001*(Sizes.T m : ℝ)+
      (Fs.length : ℝ)*D*(t : ℝ)*(1+(PhaseCellBand.width p u : ℝ)^2/Sizes.d m)*(p : ℝ)^(129/128 : ℝ)+
      726*(Fs.length*s*p : ℕ)+455 ∧
    solveStock+(480*volume+86) ≤
      ((C+1)*((1312000+756)*(1032+8*ct)+504)+1440)*(Fs.length*s*p)+2*(C+1)*Sizes.T m+86 := by
  dsimp only
  obtain ⟨D,hD,htime⟩ := selectedFullLineLifecycleTime_fast_le ct
  refine ⟨D,hD,?_⟩
  filter_upwards [htime,selectedFullLineLifecycleStock_le ct] with m htime hstock
  intro h i _ T Q A U input producer d u target Fs v S hu htarget hu1 hwidth hbudget hband
    hpad hFs hready
  let p := Sizes.p m
  let s := Sizes.s m i
  let t := Sizes.t m i
  let l := haloInverseRingLog s t
  let C := gridDispatchPush (U := U) (A := A) producer.hR producer.hQ
  let r := fullLineGridRecord (A := A) p u l target t Fs
  let volume := r.inputs.length*s*(2*p+13)
  have hr := fullLineGridRecord_ready (A := A) p u l target t hu1 hwidth hbudget hband hpad Fs hFs
  have ht := htime h i T Q A U input producer d u target Fs v S hu htarget hband hready hr
  have hs := hstock h i T Q A C U input producer d u target Fs v S hu htarget hband hready hr
  have hp : 13 ≤ p := h.thirteen_le_p
  have hv : volume ≤ 3*(Fs.length*s*p) := by
    change Fs.length*s*(2*p+13) ≤ _
    have hm := Nat.mul_le_mul_left (Fs.length*s) (show 2*p+13 ≤ 3*p by omega)
    nlinarith only [hm]
  have hcropTime : 242*volume+45 ≤ 726*(Fs.length*s*p)+45 := by omega
  have hcropSpace : 480*volume+86 ≤ 1440*(Fs.length*s*p)+86 := by omega
  constructor
  · let tape := descriptorScheduleTape producer.gridWork FamilyDispatchInput.words [r]
    let solveTime := setupTime p u l target s t Fs.length+
      ((r.gridCost p l t producer.gridWork+22*tape.length+26)+(2*(∑ j, (r.words j).length)+607))
    change (solveTime : ℝ) ≤ 2624001*(Sizes.T m : ℝ)+
      (Fs.length : ℝ)*D*(t : ℝ)*(1+(PhaseCellBand.width p u : ℝ)^2/Sizes.d m)*(p : ℝ)^(129/128 : ℝ)+410 at ht
    change ((solveTime+(242*volume+45) : ℕ) : ℝ) ≤ 2624001*(Sizes.T m : ℝ)+
      (Fs.length : ℝ)*D*(t : ℝ)*(1+(PhaseCellBand.width p u : ℝ)^2/Sizes.d m)*(p : ℝ)^(129/128 : ℝ)+
      726*(Fs.length*s*p : ℕ)+455
    rw [Nat.cast_add]
    have hcropR : ((242*volume+45 : ℕ) : ℝ) ≤ 726*(Fs.length*s*p : ℕ)+45 := by exact_mod_cast hcropTime
    linarith only [ht,hcropR]
  · have hb := Nat.add_le_add hs hcropSpace
    calc
      _ ≤ (C+1)*(((1312000+756)*(1032+8*ct)+504)*(Fs.length*s*p)+2*Sizes.T m)+
          (1440*(Fs.length*s*p)+86) := hb
      _ = _ := by ring

end IntegerMultBounds.MathlibTM2.Cost
