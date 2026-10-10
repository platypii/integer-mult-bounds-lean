import IntegerMultBounds.Machine.CompactComplexScalarCountPlaced
import IntegerMultBounds.Machine.CompactSpectatorLeafSetupBudget
import IntegerMultBounds.Machine.NativePolynomialStageShape
import IntegerMultBounds.Machine.CompactNativeRoleHeaderBudget

/-! A uniform physical count-setup budget is paid by the genuine coefficient
count and therefore by the original native stream volume. Untouched original
metadata supplies no caller cost allowance. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarCountBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ButterflyAxisHeadersArithmetic
open CompactSpectatorLeafSetup (raw state geometry)
open CompactComplexScalarCountHeaders (rest schedule)

def constant := 2*FixedBasePowerDescriptor.constant 2+60000

theorem cost_append (xs ys : List Op) (st : ActiveRepairRankHeadersCommands.State) :
    scheduleCost (xs++ys) st=scheduleCost xs st+scheduleCost ys (execute xs st) := by
  induction xs generalizing st with
  | nil => simp [scheduleCost,execute]
  | cons x xs ih => simp only [List.cons_append,scheduleCost,execute,ih]; omega

theorem rest_cost_eq (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    scheduleCost rest (state 0 s rows ell p rho left count slots right source target)=
      FixedBasePowerDescriptor.constant 2*(2^s.bits+2^ell)+
      53*(2^s.bits*2^ell)+53*(rows*2^s.bits*2^ell)+
      100*(s.H+s.B+s.F+s.bits+2^s.bits+2^ell+2^s.bits*2^ell+7)+67 := by
  simp [rest,scheduleCost,cost,eval,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,state,Function.update]
  ring

theorem count_bounds (s : Shape) (rows ell : ℕ) (hr : 0<rows) :
    let N := rows*2^s.bits*2^ell
    1≤N ∧ s.bits+1≤N ∧ 2^s.bits≤N ∧ 2^ell≤N ∧ 2^s.bits*2^ell≤N := by
  have hP : 1≤(2:ℕ)^s.bits := Nat.one_le_pow _ _ (by decide)
  have hR : 1≤(2:ℕ)^ell := Nat.one_le_pow _ _ (by decide)
  have hb : s.bits+1≤(2:ℕ)^s.bits := FixedBasePowerDescriptor.depth_le_power 2 s.bits (by decide)
  dsimp only
  have hPR : 2^s.bits*2^ell≤rows*2^s.bits*2^ell := by
    simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_left (2^s.bits*2^ell) hr
  have hPN : 2^s.bits≤rows*2^s.bits*2^ell :=
    (Nat.le_mul_of_pos_right _ (by omega : 0<2^ell)).trans hPR
  have hRN : 2^ell≤rows*2^s.bits*2^ell :=
    (Nat.le_mul_of_pos_left _ (by omega : 0<2^s.bits)).trans hPR
  exact ⟨by nlinarith,hb.trans hPN,hPN,hRN,hPR⟩

theorem setup_cost (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hr : 0<rows) (hH : 0<s.H) (hK : 0<s.chunk) :
    scheduleCost schedule (raw s rows ell p rho left count slots right source target)≤
      constant*(rows*2^s.bits*2^ell) := by
  obtain ⟨hN,hb,hP,hR,hPR⟩ := count_bounds s rows ell hr
  have hHbits : s.H≤s.bits := by unfold Shape.bits; omega
  have hBbits : s.B≤s.bits := by unfold Shape.bits; omega
  have hFbits : s.F≤s.bits := by unfold Shape.bits; omega
  have hAbits : s.active*s.chunk≤s.bits := by unfold Shape.bits; omega
  have hgeo := CompactSpectatorLeafSetupBudget.geometry_cost_eq s rows ell p rho left count slots right source target hH hK
  rw [schedule,cost_append,CompactSpectatorLeafSetup.geometry_eval _ _ _ _ _ _ _ _ _ _ _ hH hK,
    rest_cost_eq,hgeo]
  have hpow := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2)
    (show 2^s.bits+2^ell≤2*(rows*2^s.bits*2^ell) by omega)
  unfold constant
  nlinarith

/-- Direct physical construction from original descriptors, with no supplied
schedule-cost bound. -/
theorem runs_linear (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hr : 0<rows) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) :
    HoareTime CompactComplexScalarCountHeaders.program
      (fun v => v=ActiveRepairRankHeadersCommands.bank (raw s rows ell p rho left count slots right source target))
      (fun v => v=ActiveRepairRankHeadersCommands.bank
        (CompactComplexScalarCountHeaders.finished s rows ell p rho left count slots right source target))
      (constant*(rows*2^s.bits*2^ell)) :=
  (CompactComplexScalarCountHeaders.runs _ _ _ _ _ _ _ _ _ _ _ hr hG hA hK).consequence
    (fun _ h => h) (fun _ h => h) (setup_cost _ _ _ _ _ _ _ _ _ _ _ hr (Nat.mul_pos hA hG) hK)

/-- The actual three-bit codec volume includes every Gaussian field and its
separator, so it pays the complete original coefficient count. -/
theorem count_le_native_volume (s : Shape) (rows ell p : ℕ) :
    rows*2^s.bits*2^ell≤rows*(NativePolynomialStageShape.shape s ell p).recordWidth := by
  rw [NativePolynomialStageShape.volume]
  have hsymbols : 2^ell≤ActivePrefixStageNativePolynomial.symbols (2^ell)
      (NativePolynomialStageShape.width s p) := by
    unfold ActivePrefixStageNativePolynomial.symbols
    exact Nat.le_mul_of_pos_left _ (by omega)
  have h := Nat.mul_le_mul_left (rows*2^s.bits) hsymbols
  omega

theorem setup_native_volume (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hr : 0<rows) (hH : 0<s.H) (hK : 0<s.chunk) :
    scheduleCost schedule (raw s rows ell p rho left count slots right source target)≤
      constant*(rows*(NativePolynomialStageShape.shape s ell p).recordWidth) :=
  (setup_cost _ _ _ _ _ _ _ _ _ _ _ hr hH hK).trans
    (Nat.mul_le_mul_left constant (count_le_native_volume s rows ell p))

/-- Actual arbitrary caller-port count construction inherits the same uniform
budget while all appended work tapes are physically cleaned. -/
theorem placed_runs_linear {k : ℕ} (common : Fin 16 → Fin k) (hc : Function.Injective common)
    (v : Tapes k 2) (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hr : 0<rows) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk)
    (hi : SharedBank.payload (ActiveRepairRankHeadersCommands.bank (a:=2)
      (raw s rows ell p rho left count slots right source target)) CompactComplexScalarCountPlaced.ports=
      SharedBank.payload v common) :
    HoareTime (CompactComplexScalarCountPlaced.program common hc)
      (fun z => z=CleanSubbank.bank (s:=43) v)
      (fun z => z=CleanSubbank.bank (s:=43)
        (CompactComplexScalarCountPlaced.output common v (rows*2^s.bits*2^ell)))
      (constant*(rows*2^s.bits*2^ell)) :=
  (CompactComplexScalarCountPlaced.runs _ hc v _ _ _ _ _ _ _ _ _ _ _ hr hG hA hK hi).consequence
    (fun _ h => h) (fun _ h => h) (setup_cost _ _ _ _ _ _ _ _ _ _ _ hr (Nat.mul_pos hA hG) hK)

/-- Erase the retained generated count after its final scalar use, without
changing sources, the live denominator, or any other caller tape. -/
def eraseProgram {k : ℕ} (slot : Fin k) := BinaryDescriptorCleanupList.oneProgram (a:=2) slot

theorem erase_runs_linear {k : ℕ} (slot : Fin k) (v : Tapes k 2) (N : ℕ) (hN : 1≤N)
    (ht : v.tape slot=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits N))
    (hh : v.head slot=1) :
    HoareTime (eraseProgram slot) (fun z => z=v)
      (fun z => z=SharedPlacementAlphabet.setTape v slot (fun _ => blank) 0) (8*N) := by
  have h := BinaryDescriptorCleanupList.one_hoare slot v (RecursiveChildQuotientsConstant.bits N)
    (by rw [ht,BinaryDescriptorStackRoundtrip.descriptor_encoded]) hh
  have hw := ActiveRepairRankHeadersCommands.bits_length N
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem lifecycle_cost (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hr : 0<rows) (hH : 0<s.H) (hK : 0<s.chunk) :
    scheduleCost schedule (raw s rows ell p rho left count slots right source target)+
      2*(RecursiveChildQuotientsConstant.bits (rows*2^s.bits*2^ell)).length+4≤
      (constant+8)*(rows*(NativePolynomialStageShape.shape s ell p).recordWidth) := by
  have hs := setup_cost s rows ell p rho left count slots right source target hr hH hK
  have hw := ActiveRepairRankHeadersCommands.bits_length (rows*2^s.bits*2^ell)
  have hN := (count_bounds s rows ell hr).1
  have hv := count_le_native_volume s rows ell p
  have hc := Nat.mul_le_mul_left (constant+8) hv
  nlinarith

def roleConstant (c : ℕ) := constant+12000*(c+1)

theorem role_rest_cost_eq (c : ℕ) (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    scheduleCost (CompactComplexScalarCountHeaders.roleRest c)
      (state 0 s rows ell p rho left count slots right source target)=
    scheduleCost rest (state 0 s (rows/c) ell p rho left count slots right source target)+
      BinaryDescriptorDivision.cost (RecursiveChildQuotientsConstant.bits rows)
        (RecursiveChildQuotientsConstant.bits c)+3*(RecursiveChildQuotientsConstant.bits c).length+
        100*c+100*(rows/c)+210 := by
  simp [CompactComplexScalarCountHeaders.roleRest,rest,scheduleCost,cost,eval,
    CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,state,Function.update,RecursiveChildQuotientsConstant.cost]
  ring

theorem role_setup_cost (c : ℕ) (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hr : 0<rows) (hH : 0<s.H) (hK : 0<s.chunk) :
    scheduleCost (CompactComplexScalarCountHeaders.roleSchedule c)
      (raw s rows ell p rho left count slots right source target) ≤
      roleConstant c*(rows*2^s.bits*2^ell) := by
  have hold := setup_cost s rows ell p rho left count slots right source target hr hH hK
  have hrest : scheduleCost rest (state 0 s (rows/c) ell p rho left count slots right source target) ≤
      scheduleCost rest (state 0 s rows ell p rho left count slots right source target) := by
    rw [rest_cost_eq,rest_cost_eq]
    have hmul := Nat.mul_le_mul_right (2^s.bits*2^ell) (Nat.div_le_self rows c)
    simp only [←Nat.mul_assoc] at hmul
    omega
  have hdiv := CompactNativeRoleHeaderBudget.quotient_linear rows c hr
  have hb := ActiveRepairRankHeadersCommands.bits_length c
  have hq := Nat.div_le_self rows c
  have hc := Nat.le_mul_of_pos_right c hr
  have hN := (count_bounds s rows ell hr).1
  have hrows : rows ≤ rows*2^s.bits*2^ell := by
    exact (Nat.le_mul_of_pos_right rows (pow_pos (by decide) s.bits)).trans
      (Nat.le_mul_of_pos_right _ (pow_pos (by decide) ell))
  rw [schedule,cost_append,CompactSpectatorLeafSetup.geometry_eval _ _ _ _ _ _ _ _ _ _ _ hH hK] at hold
  rw [CompactComplexScalarCountHeaders.roleSchedule,cost_append,
    CompactSpectatorLeafSetup.geometry_eval _ _ _ _ _ _ _ _ _ _ _ hH hK,role_rest_cost_eq]
  have hpay := Nat.mul_le_mul_left (12000*(c+1)) hrows
  unfold roleConstant
  nlinarith

theorem role_placed_runs_linear (c : ℕ) (common : Fin 16 → Fin k) (hc : Function.Injective common)
    (v : Tapes k 2) (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hroles : 0<c) (hr : 0<rows) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk)
    (hi : SharedBank.payload (ActiveRepairRankHeadersCommands.bank (a:=2)
      (raw s rows ell p rho left count slots right source target)) CompactComplexScalarCountPlaced.ports=
        SharedBank.payload v common) :
    HoareTime (CompactComplexScalarCountPlaced.roleProgram c common hc)
      (fun z => z=CleanSubbank.bank (s:=43) v)
      (fun z => z=CleanSubbank.bank (s:=43)
        (CompactComplexScalarCountPlaced.output common v ((rows/c)*2^s.bits*2^ell)))
      (roleConstant c*(rows*2^s.bits*2^ell)) :=
  (CompactComplexScalarCountPlaced.role_runs c common hc v s rows ell p rho left count slots right source target
    hroles hG hA hK hi).consequence (fun _ h => h) (fun _ h => h)
      (role_setup_cost c s rows ell p rho left count slots right source target hr (Nat.mul_pos hA hG) hK)

end
end IntegerMultBounds.Machine.CompactComplexScalarCountBudget
