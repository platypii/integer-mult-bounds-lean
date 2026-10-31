module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.HighBody
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreSharedWithin
public import IntegerMultBounds.Machine.SharedPlacementWithin

/-! Real row padding, the bounded nine-phase core and reversed crop share
one reserve measured against padded volume, retaining their paid runtime. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.PaddedCoreWithin
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveRowPadding
open SharedPlacementAlphabet (setTape)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open RevMachine
open HighBody
noncomputable section
variable [M8.Machine.Net] {k : ℕ}
  (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)

def coefficient (k cutoff : ℕ) : ℕ := max (413+CoreRunWithin.coefficient k cutoff) 826

theorem padded_runs (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n) {K : ℕ} (hτ : Exponents K) :
    ∃ C' : ℝ, ∀ (v : Descriptor) (R' : ℕ) (ph : Fin 4 → List Bool), v.Positive → v.rows ≤ R' →
      M8.Machine.ArbitraryWidthPaddedPiecePadding.Headers v R' ph → Fits K (withRows v R') →
      ∀ (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime), Ready f p node st →
      ∀ (x : Fin (volume prime v) → ZMod 2) (lo upper : ℤ),
      (∀ j, lo+(coefficient k cutoff*volume prime (withRows v R') : ℕ) ≤
        (bank capacity K x ph R' f p node st).head j ∧
        (bank capacity K x ph R' f p node st).head j+
          (coefficient k cutoff*volume prime (withRows v R') : ℕ) ≤ upper) → ∃ c : ℕ,
        (c : ℝ) ≤ 826 * volume prime (withRows v R') + 2 +
          C' * volume prime (withRows v R') * (v.width : ℝ) ^ tau₂ K ∧
        HoareWithin (padded capacity) (· = bank capacity K x ph R' f p node st)
          (· = bank capacity K (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x) ph R' f p node st) c (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  obtain ⟨C', hC'⟩ := CoreSharedWithin.runs capacity cutoff hcut hτ.hK hτ.s1 hτ.le1 hτ.half hτ.two hτ.lin
  refine ⟨C', fun v R' ph hp hR hph hfit f p node st hready x lo upper hmargin => ?_⟩
  have hpad := hoare_extend_eq (M8.Machine.ArbitraryWidthPaddedPiecePadding.pad_hoare v R' ph hp hR hph x)
    (corePrivate capacity K f p node st (withRows v R'))
  have hreserve := Nat.mul_le_mul_right (volume prime (withRows v R'))
    (show 413+CoreRunWithin.coefficient k cutoff ≤ coefficient k cutoff from le_max_left _ _)
  rw [Nat.add_mul] at hreserve
  have hcleanup := Nat.mul_le_mul_right (volume prime (withRows v R'))
    (show 826 ≤ coefficient k cutoff from le_max_right _ _)
  have hwpad := HoareWithin.of_time_heads hpad lo upper (by
    rintro z rfl j
    have hm := hmargin j
    change lo+_ ≤ (bank capacity K x ph R' f p node st).head j ∧
      (bank capacity K x ph R' f p node st).head j+_ ≤ upper
    omega)
  have hprepared : ∀ j, lo+(CoreRunWithin.coefficient k cutoff*volume prime (withRows v R') : ℕ) ≤
      ((M8.Machine.ArbitraryWidthPaddedPiecePadding.middle (padArray R' 0 x) ph).append
        (corePrivate capacity K f p node st (withRows v R'))).head j ∧
      ((M8.Machine.ArbitraryWidthPaddedPiecePadding.middle (padArray R' 0 x) ph).append
        (corePrivate capacity K f p node st (withRows v R'))).head j+
        (CoreRunWithin.coefficient k cutoff*volume prime (withRows v R') : ℕ) ≤ upper := by
    intro j
    have ht := hpad.head_change j
    have hm := hmargin j
    change lo+_ ≤ ((M8.Machine.ArbitraryWidthPaddedPiecePadding.input x ph).append
      (corePrivate capacity K f p node st (withRows v R'))).head j ∧
      ((M8.Machine.ArbitraryWidthPaddedPiecePadding.input x ph).append
      (corePrivate capacity K f p node st (withRows v R'))).head j+_ ≤ upper at hm
    omega
  obtain ⟨c, hc, hcore⟩ := hC' (withRows v R') hfit.pos hfit.width hfit.rows f p hready.pay node hready.node st
    hready.desc hready.pc (M8.Machine.ArbitraryWidthPaddedPiecePadding.middle (padArray R' 0 x) ph) (1 : Fin 12)
    (padArray R' 0 x) rfl rfl lo upper hprepared
  rw [M8.Machine.ArbitraryWidthPaddedPiecePadding.middle_source] at hcore
  have hcrop := hoare_extend_eq (M8.Machine.ArbitraryWidthPaddedPiecePadding.crop_hoare v R' ph hp hR hph
    (Shared50RecursiveNodeRows.transpose (one_dvd R') (padArray R' 0 x)))
    (corePrivate capacity K f p node st (withRows v R'))
  rw [cropArray_transpose_padArray] at hcrop
  have hheads : (bank capacity K (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x) ph R' f p node st).head =
      (bank capacity K x ph R' f p node st).head :=
    Tapes.append_head_congr _ _ (corePrivate capacity K f p node st (withRows v R'))
      (corePrivate capacity K f p node st (withRows v R')) rfl rfl
  have hwcrop := HoareWithin.of_time_post_heads hcrop lo upper (by
    rintro z rfl j
    change lo+_ ≤ (bank capacity K (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x) ph R' f p node st).head j ∧
      (bank capacity K (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x) ph R' f p node st).head j+_ ≤ upper
    rw [hheads]
    have hm := hmargin j
    omega)
  refine ⟨_, ?_, ((hwpad.seq hcore).seq hwcrop).consequence (fun _ h => h) (fun _ h => h) le_rfl (fun _ h => h)⟩
  have hw : (withRows v R').width = v.width := rfl
  rw [hw] at hc
  push_cast
  linarith

theorem shared_runs (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n) {K : ℕ} (hτ : Exponents K) :
    ∃ C' : ℝ, ∀ (v : Descriptor) (R' : ℕ) (ph : Fin 4 → List Bool), v.Positive → v.rows ≤ R' →
      M8.Machine.ArbitraryWidthPaddedPiecePadding.Headers v R' ph → Fits K (withRows v R') →
      ∀ (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime), Ready f p node st →
      ∀ {t : ℕ} (caller : Tapes t prime) (focus : Fin t) (x : Fin (volume prime v) → ZMod 2),
      caller.tape focus = sourceWord x → caller.head focus = 0 → ∀ lo upper : ℤ,
      (∀ j, lo+(coefficient k cutoff*volume prime (withRows v R') : ℕ) ≤
        (caller.append (privateBank capacity K ph (withRows v R') f p node st)).head j ∧
        (caller.append (privateBank capacity K ph (withRows v R') f p node st)).head j+
          (coefficient k cutoff*volume prime (withRows v R') : ℕ) ≤ upper) → ∃ c : ℕ,
        (c : ℝ) ≤ 826 * volume prime (withRows v R') + 2 +
          C' * volume prime (withRows v R') * (v.width : ℝ) ^ tau₂ K ∧
        HoareWithin (shared capacity focus)
          (· = caller.append (privateBank capacity K ph (withRows v R') f p node st))
          (· = (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) 0).append
            (privateBank capacity K ph (withRows v R') f p node st)) c (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  obtain ⟨C,hC⟩ := padded_runs capacity cutoff hcut hτ
  refine ⟨C,?_⟩
  intro v R' ph hp hR hph hfit f p node st hready t caller focus x hf hh lo upper hm
  have hf' : caller.tape focus = (bankWith capacity K (sourceWord x) ph (withRows v R') f p node st).tape
      (sourceSlot capacity) := by rw [bankWith_tape]; exact hf
  have hh' : caller.head focus = (bankWith capacity K (sourceWord x) ph (withRows v R') f p node st).head
      (sourceSlot capacity) := by rw [bankWith_head]; exact hh
  have hsmall := SharedPlacementAlphabet.shared_margin caller focus (sourceSlot capacity) (fun _ => blank) 0 hf' hh'
    (by simpa only [bankWith_source,privateBank] using hm)
  obtain ⟨c,hc,hrun⟩ := hC v R' ph hp hR hph hfit f p node st hready x lo upper hsmall
  change HoareWithin _ (fun w => w = bankWith capacity K (sourceWord x) ph (withRows v R') f p node st)
    (fun w => w = bankWith capacity K (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x))
      ph (withRows v R') f p node st) _ _ at hrun
  have hframe : ∀ j, lo ≤ (caller.append (privateBank capacity K ph (withRows v R') f p node st)).head j ∧
      (caller.append (privateBank capacity K ph (withRows v R') f p node st)).head j ≤ upper := by
    intro j
    have h := hm j
    omega
  have h := SharedPlacementAlphabet.shared_within hrun caller focus (sourceSlot capacity) (fun _ => blank) 0 hf' hh'
    (by simpa only [bankWith_source,privateBank] using hframe)
  refine ⟨c,hc,?_⟩
  simpa only [shared,bankWith_tape,bankWith_head,bankWith_source,privateBank] using h

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.PaddedCoreWithin
