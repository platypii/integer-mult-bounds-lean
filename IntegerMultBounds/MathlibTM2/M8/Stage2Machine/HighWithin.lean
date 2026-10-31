module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Common
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.High
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.PreparedWithin
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighOriginalEncoding

/-! The six original headers generate the common bank for the bounded high path. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.HighWithin
noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedPlacementAlphabet (setTape)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open M8.Machine.ArbitraryWidthHighExchangeJoin (exchangeCount movementCount)
open RevMachine
open HighBody (Exponents tau₂ padCount)
open Params (threshold)
open High
variable [M8.Machine.Net] {k : ℕ}
  (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)
variable {t : ℕ}

def overheadCoefficient : ℕ := 2*MetaPrepare.constant prime+486

def coefficient (k cutoff : ℕ) : ℕ :=
  max (overheadCoefficient+PreparedWithin.coefficient k cutoff) (2*overheadCoefficient)

/-- Blank private banks preserve caller head equality before sizes are instantiated. -/
theorem input_head_congr {v w : Tapes t prime} (h : v.head = w.head) :
    (input capacity v).head = (input capacity w).head := by
  have h0 := Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty 16) (FixedHeaderBankCopy.empty 16) h rfl
  have h1 := Tapes.append_head_congr _ _ (MetaShared.privateInput (a := prime)) (MetaShared.privateInput (a := prime)) h0 rfl
  have h2 := Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty 17) (FixedHeaderBankCopy.empty 17) h1 rfl
  have h3 := Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty 12) (FixedHeaderBankCopy.empty 12) h2 rfl
  have h4 := Tapes.append_head_congr _ _ (ArbitraryWidthZeroHeaderShared.empty) (ArbitraryWidthZeroHeaderShared.empty) h3 rfl
  have h5 := Tapes.append_head_congr _ _ (Width.privateIn (q := prime)) (Width.privateIn (q := prime)) h4 rfl
  have h6 := Tapes.append_head_congr _ _ (SharedBank.empty exchangeCount prime) (SharedBank.empty exchangeCount prime) h5 rfl
  have h7 := Tapes.append_head_congr _ _ (SharedBank.empty movementCount prime) (SharedBank.empty movementCount prime) h6 rfl
  have h8 := Tapes.append_head_congr _ _ (SharedBank.empty (padCount capacity) prime) (SharedBank.empty (padCount capacity) prime) h7 rfl
  exact h8

theorem runs (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n) (hτ : Exponents HighCost.K) :
    ∃ C D : ℝ, ∀ {t : ℕ} (caller : Tapes t prime) (headers : Fin 6 → Fin t) (source : Fin t)
      (d : Descriptor) (hs : Fin 6 → List Bool), d.Positive → threshold 2 ≤ d.width →
      RecursiveDimensionBank.Headers d hs →
      (∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i)) → (∀ i, caller.head (headers i) = 1) →
      ∀ x : Fin (volume prime d) → ZMod 2, caller.tape source = sourceWord x → caller.head source = 0 →
      ∀ lo upper : ℤ,
      (∀ j, lo+(coefficient k cutoff*volume prime d : ℕ) ≤ (input capacity caller).head j ∧
        (input capacity caller).head j+(coefficient k cutoff*volume prime d : ℕ) ≤ upper) →
      ∃ c : ℕ, (c : ℝ) ≤ C * volume prime d * (d.width : ℝ) ^ tau₂ HighCost.K + D * volume prime d ∧
        HoareWithin (program capacity headers source) (fun z => z = input capacity caller)
          (fun z => z = input capacity (setTape caller source
            (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0)) c (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  obtain ⟨C, D, hCD⟩ := PreparedWithin.runs capacity cutoff hcut hτ
  refine ⟨C, D + ((2 * MetaPrepare.constant prime + 486 + 2 : ℕ) : ℝ),
    fun {t} caller headers source d hs hp he hv ht hh x hf hhead lo upper hmargin => ?_⟩
  have hfit := Params.fit_of_threshold (le_refl 2) he
  have hd : 0 < d.width := by omega
  have hs' := extend_banks_hoare capacity (Common.constructs headers caller prime d hs Params.prime_two hp hd hv ht hh)
  have hlin := Common.costs_le d hp (by omega)
  have hreserve := Nat.mul_le_mul_right (volume prime d)
    (show overheadCoefficient+PreparedWithin.coefficient k cutoff ≤ coefficient k cutoff from le_max_left _ _)
  rw [Nat.add_mul] at hreserve
  have hcleanup := Nat.mul_le_mul_right (volume prime d)
    (show 2*overheadCoefficient ≤ coefficient k cutoff from le_max_right _ _)
  rw [Nat.mul_assoc] at hcleanup
  change Common.setupCost prime d+Common.cleanupCost prime d ≤ overheadCoefficient*volume prime d at hlin
  have hws := HoareWithin.of_time_heads hs' lo upper (by
    rintro z rfl j
    change lo+_ ≤ (input capacity caller).head j ∧ (input capacity caller).head j+_ ≤ upper
    have hm := hmargin j
    omega)
  have hprepared : ∀ j, lo+(PreparedWithin.coefficient k cutoff*volume prime d : ℕ) ≤
      (Prepared.input capacity (Common.output caller d hs prime)).head j ∧
      (Prepared.input capacity (Common.output caller d hs prime)).head j+
        (PreparedWithin.coefficient k cutoff*volume prime d : ℕ) ≤ upper := by
    intro j
    have ht := hs'.head_change j
    change (input capacity caller).head j-(Common.setupCost prime d : ℕ) ≤
      (Prepared.input capacity (Common.output caller d hs prime)).head j ∧
      (Prepared.input capacity (Common.output caller d hs prime)).head j ≤
        (input capacity caller).head j+(Common.setupCost prime d : ℕ) at ht
    have hm := hmargin j
    omega
  have hfold := Common.folded_headers d hs hv
  have hbase : (Common.output caller d hs prime).head (callerSlot source) = caller.head source ∧
      (Common.output caller d hs prime).tape (callerSlot source) = caller.tape source := by
    simp only [callerSlot, Common.output, Tapes.append, Fin.addCases_left]
    exact ⟨trivial, trivial⟩
  obtain ⟨c, hc, hb⟩ := hCD (Common.output caller d hs prime) (callerSlot source)
    Common.dimensionsFocus Common.joinedFocus Common.exchangeFocus Common.rowFocus Common.roundedFocus
    (Common.foldedPrefix d) d.width d.between d.afterD he (Common.foldedPrefix_positive d hp)
    hp.2.2.2.1 hp.2.2.2.2
    (Common.dimensionsWords d hs) (Common.joinedWords d hs) (ArbitraryWidthHighFoldHeaders.words d hs)
    (Common.rhoWord d) (Common.rowWord d) (Common.roundedWord d)
    (Common.dimensions_values d hs hv) (Common.dimensions_canonical d hs hv)
    (Common.joined_values d hs hv) (Common.joined_canonical d hs hv)
    (Common.dimensions_sources caller d hs) (Common.joined_sources caller d hs) (Common.exchange_sources caller d hs)
    hfold (Common.rho_value d) (Common.rho_canonical d) (Common.row_value d) (Common.row_canonical d)
    (Common.rounded_value d) (Common.rounded_canonical d) (Common.row_cells caller d hs).2
    (Common.row_cells caller d hs).1 (Common.rounded_cells caller d hs).2 (Common.rounded_cells caller d hs).1
    (ArbitraryWidthHighFoldSemantics.foldArray x)
    (hbase.2.trans (hf.trans (M8.Machine.ArbitraryWidthHighOriginalEncoding.source_fold x).symm))
    (hbase.1.trans hhead) lo upper (by
      have hvol : volume prime d = volume prime
          (ArbitraryWidthHighLayout.originalDescriptor (Common.foldedPrefix d) d.width d.between d.afterD) :=
        ArbitraryWidthHighFoldSemantics.folded_volume prime d
      rw [← hvol]
      exact hprepared)
  have hword : sourceWord (Shared50RecursiveNodeRows.transpose
      (v := ArbitraryWidthHighLayout.originalDescriptor (Common.foldedPrefix d) d.width d.between d.afterD)
      (one_dvd _) (ArbitraryWidthHighFoldSemantics.foldArray x)) =
      sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x) :=
    M8.Machine.ArbitraryWidthHighOriginalEncoding.source_transpose_fold (by decide : 0 < 1) (one_dvd d.rows) x
  rw [hword, changed_common] at hb
  have hn : headers 3 ≠ source := by
    intro h
    have hh3 := hh 3
    rw [h, hhead] at hh3
    omega
  have hcl := extend_banks_hoare capacity (Common.cleans headers
    (setTape caller source (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0)
    prime d hs Params.prime_two hp hv
    (by simpa only [setTape, Function.update_of_ne hn] using ht 3)
    (by simpa only [setTape, Function.update_of_ne hn] using hh 3))
  let changed := setTape caller source (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0
  have hcallerHeads : changed.head = caller.head := by
    funext j
    by_cases hj : j = source
    · subst j; simp only [changed,setTape,Function.update_self,hhead]
    · simp only [changed,setTape,Function.update_of_ne hj]
  have hheads := input_head_congr capacity hcallerHeads
  have hwcl := HoareWithin.of_time_post_heads hcl lo upper (by
    rintro z rfl j
    change lo+_ ≤ (input capacity changed).head j ∧ (input capacity changed).head j+_ ≤ upper
    rw [hheads]
    have hm := hmargin j
    omega)
  refine ⟨_, ?_, ((hws.seq hb).seq hwcl).consequence (fun _ h => h) (fun _ h => h) le_rfl (fun _ h => h)⟩
  have hvol : volume prime d = volume prime
      (ArbitraryWidthHighLayout.originalDescriptor (Common.foldedPrefix d) d.width d.between d.afterD) :=
    ArbitraryWidthHighFoldSemantics.folded_volume prime d
  rw [← hvol] at hc
  have hV := RecursiveAffinePrepare.volume_positive Params.prime_two d hp
  exact cost_arith hlin hV hc

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.HighWithin
