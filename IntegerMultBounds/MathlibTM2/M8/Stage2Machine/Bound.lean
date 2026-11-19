module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Supplier
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Spec
public import IntegerMultBounds.MathlibTM2.M8.Global.SupplierNet

/-!
# The stage-2 supplier's bound

On the supplier's network (`BinaryRadixEqualShared.supplierNet`, the PR97 node), stage 1's exponent
is the PR97 exponent `τ₁ = 1 - 3734039/10¹²` (`tau_eq`), so the core's exponents hold at `θ = 1/1000`
(`HighCost.exponents`), and the reversed family's data semantics is `Spec.familySpec`. The stage-2
supplier then transposes every positive descriptor within `C V max(1,e)^τ₂` with
`τ₂ = 1 - 123899714039/10¹⁵` (`tau₂_eq`), a saving of about `2^-12.98` (`uniform_bound`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Bound

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedPlacementAlphabet (setTape)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open RevMachine
open HighBody (tau₂)

theorem le_two_pow (n : ℕ) : n ≤ 2 ^ n := Nat.lt_two_pow_self.le

/-- The family's program counters fit `card` bits. -/
theorem capacity97 : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤
    2 ^ Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) := le_two_pow _

/-- Stage 1's exponent is the PR97 exponent. -/
theorem tau_eq : M8.Machine.BudgetBound.tau = M8.Global.Branching97.tau := by
  change M8.Global.pr97.tau = _
  exact M8.Global.pr97_tau

/-- **The stage-2 exponent.** -/
theorem tau₂_eq : tau₂ HighCost.K = 1 - 123899714039 / 10 ^ 15 := by
  simp only [tau₂, Stage2Width.tau2, Cost.tauS, Stage2Moments.savingB, tau_eq, M8.Global.Branching97.tau,
    M8.Global.Branching97.saving]
  push_cast
  norm_num

/-- **The stage-2 supplier's uniform bound.** One fixed program transposes the source of every
positive descriptor, from blank private banks to blank private banks, within a constant times
`V max(1,e)^τ₂`. -/
theorem uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {t : ℕ} (caller : Tapes t prime) (headers : Fin 6 → Fin t) (source : Fin t)
      (d : Descriptor) (hs : Fin 6 → List Bool), d.Positive → RecursiveDimensionBank.Headers d hs →
      (∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i)) → (∀ i, caller.head (headers i) = 1) →
      ∀ x : Fin (volume prime d) → ZMod 2, caller.tape source = sourceWord x → caller.head source = 0 →
      ∃ c : ℕ, (c : ℝ) ≤ C * volume prime d * ((max 1 d.width : ℕ) : ℝ) ^ (1 - 123899714039 / 10 ^ 15 : ℝ) ∧
        HoareTime (Supplier.program capacity97 headers source) (fun z => z = Supplier.input capacity97 caller)
          (fun z => z = Supplier.input capacity97 (setTape caller source
            (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0)) c := by
  rw [← tau₂_eq]
  exact Supplier.runs capacity97 (Spec.familySpec capacity97) (HighCost.exponents tau_eq)

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Bound
