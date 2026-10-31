module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreShared
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreRunWithin
public import IntegerMultBounds.Machine.SharedPlacementWithin


/-!
# The stage-2 core on a caller's tape

The core's bank (`Assembly.bank`) is a function of the stream on its I/O role (`bankWith`). Placed
with that role shared with a caller's tape (`program`), the core transposes the bit array on the
caller's tape and restores its own bank, the core's bank with a blank I/O role (`privateBank`):
`runs`, from `CoreRun.core_run`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreSharedWithin

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankStageInput (raw)
open SharedPlacementAlphabet (setTape)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open Stage2Width (tau2)
open RevMachine
open FamilyRoot (ext FamilySpec)
open Assembly (tW wOf nOf)

variable [M8.Machine.Net] {k : ℕ} (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)

open CoreShared

theorem runs (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n) {K : ℕ} (hK : 2 ≤ K)
    (hs1 : Cost.tauS ≤ M8.Machine.BudgetBound.tau) (hτ₁ : M8.Machine.BudgetBound.tau ≤ 1)
    (hhalf : 1 / 2 ≤ M8.Machine.BudgetBound.tau)
    (h2 : 1 / 2 ≤ tau2 (K : ℝ)⁻¹ Cost.tauS M8.Machine.BudgetBound.tau)
    (hlin : 1 - (K : ℝ)⁻¹ ≤ tau2 (K : ℝ)⁻¹ Cost.tauS M8.Machine.BudgetBound.tau) :
    ∃ C' : ℝ, ∀ v : Descriptor, v.Positive → 2 ≤ v.width →
      rev97m.roleCount ^ RevNode.depth rev97m.width (RevHalf.Rk rev97m) (nOf K v) ∣ v.rows →
      ∀ (f : ℤ → Fin (prime+4)) (p : ℤ), (∀ z, p ≤ z → f z = blank) →
      ∀ (node : Tapes 1 prime), Family.NodeFree node → ∀ st : Tapes 2 prime,
      RecursiveStackAllocation.Available 0 st → RecursiveStackAllocation.Available 1 st →
      ∀ {t : ℕ} (caller : Tapes t prime) (focus : Fin t) (x : Fin (volume prime v) → ZMod 2),
      caller.tape focus = sourceWord x → caller.head focus = 0 → ∀ lo upper : ℤ,
      (∀ j, lo+(CoreRunWithin.coefficient k cutoff*volume prime v : ℕ) ≤
        (caller.append (privateBank capacity f p node st (wOf K v) v)).head j ∧
        (caller.append (privateBank capacity f p node st (wOf K v) v)).head j+
          (CoreRunWithin.coefficient k cutoff*volume prime v : ℕ) ≤ upper) → ∃ c : ℕ,
        (c : ℝ) ≤ C' * volume prime v * (v.width : ℝ) ^ tau2 (K : ℝ)⁻¹ Cost.tauS M8.Machine.BudgetBound.tau ∧
        HoareWithin (program capacity focus)
          (· = caller.append (privateBank capacity f p node st (wOf K v) v))
          (· = (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) 0).append
            (privateBank capacity f p node st (wOf K v) v)) c (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  obtain ⟨C,hC⟩ := CoreRunWithin.core_run capacity cutoff hcut hK hs1 hτ₁ hhalf h2 hlin
  refine ⟨C,?_⟩
  intro v hp he hrows f p hpay node hfree st hdesc hpc t caller focus x hf hh lo upper hm
  have hio := bankWith_io capacity f p node (Place.memo v.width) st (wOf K v) v (sourceWord x)
  have hsmall := SharedPlacementAlphabet.shared_margin caller focus (ioSlot capacity) (fun _ => blank) 0
    (hf.trans hio.2.symm) (hh.trans hio.1.symm)
    (by simpa only [bankWith_set,privateBank] using hm)
  obtain ⟨c,hc,hH⟩ := hC v hp he hrows f p hpay node hfree st hdesc hpc x lo upper
    (by rw [bank_eq]; exact hsmall)
  rw [bank_eq,bank_eq] at hH
  have hio' := bankWith_io capacity f p node (Place.memo v.width) st (wOf K v) v
    (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x))
  have hframe : ∀ j, lo ≤ (caller.append (privateBank capacity f p node st (wOf K v) v)).head j ∧
      (caller.append (privateBank capacity f p node st (wOf K v) v)).head j ≤ upper := by
    intro j
    have h := hm j
    omega
  have h := SharedPlacementAlphabet.shared_within hH caller focus (ioSlot capacity) (fun _ => blank) 0
    (hf.trans hio.2.symm) (hh.trans hio.1.symm)
    (by simpa only [bankWith_set,privateBank] using hframe)
  rw [bankWith_set,bankWith_set,hio'.1,hio'.2] at h
  exact ⟨c,hc,h⟩

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreSharedWithin
