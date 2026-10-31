module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Total
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.SupplierWithin

/-! The sealed selected supplier retains its existing paid budget and gains
one fixed linear-volume workspace reserve. Tape and state counts stay sealed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.TotalWithin
noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedPlacementAlphabet (setTape)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open Total

/-- Relabel a bounded contract before any concrete counts are instantiated. -/
theorem within_recast {n m q r a b : ℕ} (h : n = m) (hq : q = r)
    {M : Program n q a} {v w : Tapes n a} (lo upper : ℤ)
    (hM : HoareWithin M (· = v) (· = w) b (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper)) :
    HoareWithin (recastProgram h hq M) (· = recast h v) (· = recast h w) b
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  subst h hq
  exact hM

theorem margin_recast {n m a D : ℕ} (h : n = m) (v : Tapes n a) (lo upper : ℤ) :
    (∀ j, lo+(D : ℕ) ≤ (recast h v).head j ∧ (recast h v).head j+(D : ℕ) ≤ upper) ↔
    (∀ j, lo+(D : ℕ) ≤ v.head j ∧ v.head j+(D : ℕ) ≤ upper) := by
  subst h
  rfl

/-- A single numerical cutoff, independent of every input descriptor. -/
def cutoff : ℕ := Classical.choose (M8.Machine.ArbitraryWidthHighGuard.bounded_fallback prime Params.prime_two)

theorem cutoff_spec : ∀ n, cutoff ≤ n →
    1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n :=
  Classical.choose_spec (M8.Machine.ArbitraryWidthHighGuard.bounded_fallback prime Params.prime_two)

variable [Capacity] {t : ℕ}

def coefficient : ℕ := SupplierWithin.coefficient Capacity.bits cutoff

/-- The actual sealed supplier, in its original budget, bounds every prefix. -/
theorem runs (caller : Tapes t prime) (headers : Fin 6 → Fin t) (source : Fin t)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hp : d.Positive)
    (hv : RecursiveDimensionBank.Headers d hs)
    (ht : ∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (headers i) = 1)
    (x : Fin (volume prime d) → ZMod 2)
    (hf : caller.tape source = sourceWord x) (hhead : caller.head source = 0)
    (lo upper : ℤ)
    (hm : ∀ j, lo+(coefficient*volume prime d : ℕ) ≤ (Total.input caller).head j ∧
      (Total.input caller).head j+(coefficient*volume prime d : ℕ) ≤ upper) :
    HoareWithin (Total.program headers source) (· = Total.input caller)
      (· = Total.input (setTape caller source
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0)) (cost d)
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  have hm' := (margin_recast (count_def t).symm (Supplier.input Capacity.fits caller) lo upper).mp hm
  obtain ⟨C,hC,hbound⟩ := SupplierWithin.runs Capacity.fits cutoff cutoff_spec (HighCost.exponents Bound.tau_eq)
  obtain ⟨c,hc,hr⟩ := hbound caller headers source d hs hp hv ht hh x hf hhead lo upper hm'
  have h := within_recast (count_def t).symm (states_def t).symm lo upper hr
  change HoareWithin (Total.program headers source) (· = Total.input caller)
    (· = Total.input (setTape caller source
      (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0)) c _ at h
  apply HoareWithin.of_time_invariant (Total.runs caller headers source d hs hp hv ht hh x hf hhead)
  intro z hz
  exact h.invariant hz

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.TotalWithin
