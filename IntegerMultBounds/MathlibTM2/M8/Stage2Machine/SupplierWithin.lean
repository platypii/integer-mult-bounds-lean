module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Supplier
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.HighWithin
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthOriginalTotalRunWithin
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighBranchCompositionWithin

/-! The actual supplier selector, both branches and guard lifecycle share a
fixed linear-volume reserve, preserving the selected runtime exponent. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.SupplierWithin
noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedPlacementAlphabet (setTape)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open M8.Machine.ArbitraryWidthHighExchangeJoin (exchangeCount movementCount)
open M8.Machine.ArbitraryWidthHighCommonFallback (elementaryCount)
open RevMachine
open HighBody (Exponents tau₂ padCount)
open Params (threshold)
open Supplier
variable [M8.Machine.Net] {k : ℕ}
  (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)
variable {t : ℕ}

/-- Extend a bounded execution over the fixed, stationary stage-1 private bank. -/
theorem extend_outer_within {states budget : ℕ} {M : Program t states prime} {v w : Tapes t prime}
    (lo upper : ℤ) (hzero : lo ≤ 0 ∧ 0 ≤ upper)
    (h : HoareWithin M (· = v) (· = w) budget (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper)) :
    HoareWithin (extendOuter M) (· = outer v) (· = outer w) budget
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  have h0 := HoareWithin.extend_heads_eq (FixedHeaderBankCopy.empty 16) lo upper h (fun _ => hzero)
  have h1 := HoareWithin.extend_heads_eq (M8.Machine.ArbitraryWidthHighPrepareShared.privateInput) lo upper h0 (fun _ => hzero)
  have h2 := HoareWithin.extend_heads_eq (FixedHeaderBankCopy.empty 17) lo upper h1 (fun _ => hzero)
  have h3 := HoareWithin.extend_heads_eq (FixedHeaderBankCopy.empty 12) lo upper h2 (fun _ => hzero)
  have h4 := HoareWithin.extend_heads_eq (ArbitraryWidthZeroHeaderShared.empty) lo upper h3 (fun _ => hzero)
  have h5 := HoareWithin.extend_heads_eq (SharedBank.empty exchangeCount prime) lo upper h4 (fun _ => hzero)
  have h6 := HoareWithin.extend_heads_eq (SharedBank.empty movementCount prime) lo upper h5 (fun _ => hzero)
  have h7 := HoareWithin.extend_heads_eq (SharedBank.empty M8.Machine.ArbitraryWidthHighRun.paddingCount prime) lo upper h6 (fun _ => hzero)
  have h8 := HoareWithin.extend_heads_eq (FixedHeaderBankCopy.empty elementaryCount) lo upper h7 (fun _ => hzero)
  exact h8

def branchCoefficient (k cutoff : ℕ) : ℕ := max (HighWithin.coefficient k cutoff)
  (max (M8.Machine.ArbitraryWidthOriginalTotalRunWithin.coefficient cutoff) (21*(1+bound)))

def coefficient (k cutoff : ℕ) : ℕ :=
  max (RecursiveChildQuotientsConstant.cost bound+branchCoefficient k cutoff)
    (2*(2*(RecursiveChildQuotientsConstant.bits bound).length+4))

omit [M8.Machine.Net] in
private theorem margin_mono {B C : ℕ} {lo upper x : ℤ} (h : B ≤ C)
    (hm : lo+(C : ℕ) ≤ x ∧ x+(C : ℕ) ≤ upper) :
    lo+(B : ℕ) ≤ x ∧ x+(B : ℕ) ≤ upper := by omega

omit [M8.Machine.Net] in
private theorem margin_after {S B C : ℕ} {lo upper x y : ℤ} (h : S+B ≤ C)
    (ht : x-(S : ℕ) ≤ y ∧ y ≤ x+(S : ℕ))
    (hm : lo+(C : ℕ) ≤ x ∧ x+(C : ℕ) ≤ upper) :
    lo+(B : ℕ) ≤ y ∧ y+(B : ℕ) ≤ upper := by omega

omit [M8.Machine.Net] in
private theorem constant_allowance (V n : ℕ) (hV : 0 < V) : V+n ≤ (1+n)*V := by
  nlinarith

attribute [local irreducible] RecursiveChildQuotientsConstant.cost RecursiveChildQuotientsConstant.bits

theorem runs (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n) (hτ : Exponents HighCost.K) :
    ∃ C : ℝ, 0 < C ∧ ∀ {t : ℕ} (caller : Tapes t prime) (headers : Fin 6 → Fin t) (source : Fin t)
      (d : Descriptor) (hs : Fin 6 → List Bool), d.Positive → RecursiveDimensionBank.Headers d hs →
      (∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i)) → (∀ i, caller.head (headers i) = 1) →
      ∀ x : Fin (volume prime d) → ZMod 2, caller.tape source = sourceWord x → caller.head source = 0 →
      ∀ lo upper : ℤ,
      (∀ j, lo+(coefficient k cutoff*volume prime d : ℕ) ≤ (Supplier.input capacity caller).head j ∧
        (Supplier.input capacity caller).head j+(coefficient k cutoff*volume prime d : ℕ) ≤ upper) →
      ∃ c : ℕ, (c : ℝ) ≤ C * volume prime d * ((max 1 d.width : ℕ) : ℝ) ^ tau₂ HighCost.K ∧
        HoareWithin (program capacity headers source) (fun z => z = Supplier.input capacity caller)
          (fun z => z = Supplier.input capacity (setTape caller source
            (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0)) c (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  obtain ⟨C, D, hCD⟩ := HighWithin.runs capacity cutoff hcut hτ
  obtain ⟨C₁, hC₁, hb₁⟩ := M8.Machine.ArbitraryWidthOriginalTotalRun.uniform_bound
  have hτ₂ := tau₂_le hτ
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = RecursiveChildQuotientsConstant.cost bound +
      (2 * (RecursiveChildQuotientsConstant.bits bound).length + 4) + 21 + 21 * bound + 3 := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = ((threshold 2 : ℕ) : ℝ) ^ (M8.Machine.BudgetBound.tau - tau₂ HighCost.K) :=
    ⟨_, rfl⟩
  have hE : 0 ≤ E := hEdef ▸ Real.rpow_nonneg (Nat.cast_nonneg _) _
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = |C| + |D| + C₁ * E := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  refine ⟨(L : ℝ) + A + 1, by positivity, fun {t} caller headers source d hs hp hv ht hh x hf hhead lo upper hmargin => ?_⟩
  have h5 := Prepared.five_le_threshold
  have hVpos := RecursiveAffinePrepare.volume_positive Params.prime_two d hp
  have il := inner_lift capacity (t := t + 2)
  have ol := outer_lift (t := innerCount capacity (t + 2))
  -- the Supplier.guard's cells
  have gt0 : (guardWith bound).tape 0 = BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits bound) := by
    simp [guardWith, setTape]
  have gh0 : (guardWith bound).head 0 = 1 := by simp [guardWith, setTape]
  have gt1 : (guardWith bound).tape 1 = fun _ => blank := by simp [guardWith, Supplier.guard, setTape, SharedBank.empty]
  have gh1 : (guardWith bound).head 1 = 0 := by simp [guardWith, Supplier.guard, setTape, SharedBank.empty]
  have hguard : setTape (guardWith bound) 0 (fun _ => blank) 0 = Supplier.guard := by
    unfold guardWith
    rw [SharedPlacementAlphabet.setTape_setTape]
    exact SharedPlacementAlphabet.setTape_self Supplier.guard 0
  have cell : ∀ (y : Tapes (t+2) prime) (j : Fin (t+2)),
      (outer (High.input capacity y)).tape (slot capacity j) = y.tape j ∧
      (outer (High.input capacity y)).head (slot capacity j) = y.head j := fun y j =>
    ⟨(ol.tape _ _).trans (il.tape _ _), (ol.head _ _).trans (il.head _ _)⟩
  have setc : ∀ (y : Tapes (t+2) prime) (j : Fin (t+2)) (f : ℤ → Fin (prime+4)) (p : ℤ),
      setTape (outer (High.input capacity y)) (slot capacity j) f p = outer (High.input capacity (setTape y j f p)) :=
    fun y j f p => by rw [il.set, ol.set]; rfl
  -- write the constant
  have hw := const_hoare bound (rho capacity) (Supplier.input capacity caller)
    (by rw [Supplier.input, rho, (cell _ _).1]; simp [Tapes.append, Supplier.guard, SharedBank.empty])
    (by rw [Supplier.input, rho, (cell _ _).2]; simp [Tapes.append, Supplier.guard, SharedBank.empty])
  rw [Supplier.input, rho, setc, SharedPlacementAlphabet.setTape_append_right] at hw
  change HoareTime _ _ (fun w => w = outer (High.input capacity (caller.append (guardWith bound)))) _ at hw
  have hreserve := Nat.mul_le_mul_right (volume prime d)
    (show RecursiveChildQuotientsConstant.cost bound+branchCoefficient k cutoff ≤ coefficient k cutoff from le_max_left _ _)
  rw [Nat.add_mul] at hreserve
  have hcleanup := Nat.mul_le_mul_right (volume prime d)
    (show 2*(2*(RecursiveChildQuotientsConstant.bits bound).length+4) ≤ coefficient k cutoff from le_max_right _ _)
  rw [Nat.mul_assoc] at hcleanup
  have hwrite : RecursiveChildQuotientsConstant.cost bound ≤
      RecursiveChildQuotientsConstant.cost bound*volume prime d := Nat.le_mul_of_pos_right _ hVpos
  have hwriteBudget : RecursiveChildQuotientsConstant.cost bound ≤ coefficient k cutoff*volume prime d :=
    hwrite.trans ((Nat.le_add_right _ _).trans hreserve)
  have hww := HoareWithin.of_time_heads hw lo upper (by
    rintro z rfl j
    change lo+_ ≤ (Supplier.input capacity caller).head j ∧ (Supplier.input capacity caller).head j+_ ≤ upper
    exact margin_mono hwriteBudget (hmargin j))
  have hprepared : ∀ j, lo+(branchCoefficient k cutoff*volume prime d : ℕ) ≤
      (outer (High.input capacity (caller.append (guardWith bound)))).head j ∧
      (outer (High.input capacity (caller.append (guardWith bound)))).head j+
        (branchCoefficient k cutoff*volume prime d : ℕ) ≤ upper := by
    intro j
    have ht := hw.head_change j
    change (Supplier.input capacity caller).head j-(RecursiveChildQuotientsConstant.cost bound : ℕ) ≤
      (outer (High.input capacity (caller.append (guardWith bound)))).head j ∧
      (outer (High.input capacity (caller.append (guardWith bound)))).head j ≤
        (Supplier.input capacity caller).head j+(RecursiveChildQuotientsConstant.cost bound : ℕ) at ht
    exact margin_after ((Nat.add_le_add_right hwrite _).trans hreserve) ht (hmargin j)
  have hhighReserve := Nat.mul_le_mul_right (volume prime d)
    (show HighWithin.coefficient k cutoff ≤ branchCoefficient k cutoff from le_max_left _ _)
  have hlowReserve := Nat.mul_le_mul_right (volume prime d)
    (show M8.Machine.ArbitraryWidthOriginalTotalRunWithin.coefficient cutoff ≤ branchCoefficient k cutoff from
      (le_max_left _ _).trans (le_max_right _ _))
  have hselectReserve := Nat.mul_le_mul_right (volume prime d)
    (show 21*(1+bound) ≤ branchCoefficient k cutoff from (le_max_right _ _).trans (le_max_right _ _))
  -- the branch
  obtain ⟨W, hW⟩ : ∃ W, W = sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x) := ⟨_, rfl⟩
  rw [← hW]
  have hcells : ∀ (y : Tapes t prime) (j : Fin t), (y.append (guardWith bound)).tape (Fin.castAdd 2 j) = y.tape j ∧
      (y.append (guardWith bound)).head (Fin.castAdd 2 j) = y.head j := fun y j =>
    ⟨by simp only [Tapes.append, Fin.addCases_left], by simp only [Tapes.append, Fin.addCases_left]⟩
  have gcells : ∀ (y : Tapes t prime) (j : Fin 2), (y.append (guardWith bound)).tape (Fin.natAdd t j) =
      (guardWith bound).tape j ∧ (y.append (guardWith bound)).head (Fin.natAdd t j) = (guardWith bound).head j :=
    fun y j => ⟨by simp only [Tapes.append, Fin.addCases_right], by simp only [Tapes.append, Fin.addCases_right]⟩
  have hout_set : setTape (caller.append (guardWith bound)) (Fin.castAdd 2 source) W 0 =
      (setTape caller source W 0).append (guardWith bound) :=
    SharedPlacementAlphabet.setTape_append_left _ _ _ _ _
  have hrs := RecursiveChildQuotientsConstant.bits_value bound
  have hes := hv.1 3
  have hwV : d.width ≤ volume prime d := RecursiveHeaderBounds.values_le_volume Params.prime_two d hp 3
  have hcond : (1 ≤ Counter.value (RecursiveChildQuotientsConstant.bits bound) ∧
      Counter.value (RecursiveChildQuotientsConstant.bits bound) < Counter.value (hs 3)) ↔ threshold 2 ≤ d.width := by
    rw [hrs, hes]
    show (1 ≤ threshold 2 - 1 ∧ threshold 2 - 1 < d.width) ↔ threshold 2 ≤ d.width
    omega
  have hrr : (outer (High.input capacity (caller.append (guardWith bound)))).tape (rho capacity) =
      BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits bound) := by
    rw [rho, (cell _ _).1, (gcells _ 0).1, gt0]
  have hrh : (outer (High.input capacity (caller.append (guardWith bound)))).head (rho capacity) = 1 := by
    rw [rho, (cell _ _).2, (gcells _ 0).2, gh0]
  have her : (outer (High.input capacity (caller.append (guardWith bound)))).tape (Supplier.width capacity headers) =
      BinaryDescriptorStack.descriptor (hs 3) := by
    rw [Supplier.width, (cell _ _).1, (hcells _ _).1, ht 3, BinaryDescriptorStackRoundtrip.descriptor_encoded]
  have heh : (outer (High.input capacity (caller.append (guardWith bound)))).head (Supplier.width capacity headers) = 1 := by
    rw [Supplier.width, (cell _ _).2, (hcells _ _).2, hh 3]
  have hfr : (outer (High.input capacity (caller.append (guardWith bound)))).tape (flag capacity) = fun _ => blank := by
    rw [flag, (cell _ _).1, (gcells _ 1).1, gt1]
  have hfh : (outer (High.input capacity (caller.append (guardWith bound)))).head (flag capacity) = 0 := by
    rw [flag, (cell _ _).2, (gcells _ 1).2, gh1]
  -- the erasure of the constant
  have he := BinaryDescriptorCleanupList.one_hoare (rho capacity)
    (outer (High.input capacity ((setTape caller source W 0).append (guardWith bound))))
    (RecursiveChildQuotientsConstant.bits bound) (by rw [rho, (cell _ _).1, (gcells _ 0).1, gt0])
    (by rw [rho, (cell _ _).2, (gcells _ 0).2, gh0])
  rw [rho, setc, SharedPlacementAlphabet.setTape_append_right, hguard] at he
  have hcallerHeads : (setTape caller source W 0).head = caller.head := by
    funext j
    by_cases hj : j = source
    · subst j; simp only [setTape,Function.update_self,hhead]
    · simp only [setTape,Function.update_of_ne hj]
  have hheads := M8.Machine.ArbitraryWidthOriginalRunWithin.input_head_congr
    (HighWithin.input_head_congr capacity (Tapes.append_head_congr _ _ Supplier.guard Supplier.guard hcallerHeads rfl))
  change (Supplier.input capacity (setTape caller source W 0)).head = (Supplier.input capacity caller).head at hheads
  have hwe := HoareWithin.of_time_post_heads he lo upper (by
    rintro z rfl j
    change lo+_ ≤ (Supplier.input capacity (setTape caller source W 0)).head j ∧
      (Supplier.input capacity (setTape caller source W 0)).head j+_ ≤ upper
    rw [hheads]
    have h := Nat.le_mul_of_pos_right (2*(RecursiveChildQuotientsConstant.bits bound).length+4) hVpos
    exact margin_mono ((Nat.mul_le_mul_left 2 h).trans hcleanup) (hmargin j))
  have hselect := ArbitraryWidthHighBranch.cost_volume (RecursiveChildQuotientsConstant.bits bound) (hs 3)
    (RecursiveChildQuotientsConstant.bits_canonical bound) (hv.2 3) (volume prime d+bound)
    (Nat.add_pos_left hVpos _) (by rw [hrs]; exact Nat.le_add_left _ _)
    (by rw [hes]; exact hwV.trans (Nat.le_add_right _ _))
  have hselectTotal : ArbitraryWidthHighBranch.cost (RecursiveChildQuotientsConstant.bits bound) (hs 3) ≤
      branchCoefficient k cutoff*volume prime d := by
    have h := Nat.mul_le_mul_left 21 (constant_allowance (volume prime d) bound hVpos)
    rw [← Nat.mul_assoc] at h
    exact (hselect.trans h).trans hselectReserve
  have hselectorMargin : ∀ j, lo+(ArbitraryWidthHighBranch.cost (RecursiveChildQuotientsConstant.bits bound) (hs 3) : ℕ) ≤
      (outer (High.input capacity (caller.append (guardWith bound)))).head j ∧
      (outer (High.input capacity (caller.append (guardWith bound)))).head j+
        (ArbitraryWidthHighBranch.cost (RecursiveChildQuotientsConstant.bits bound) (hs 3) : ℕ) ≤ upper := by
    intro j
    exact margin_mono hselectTotal (hprepared j)
  have hzero : lo ≤ 0 ∧ 0 ≤ upper := by
    have hm := margin_mono (Nat.zero_le _) (hprepared (flag capacity))
    rw [hfh] at hm
    omega
  have hP1 : (1 : ℝ) ≤ ((max 1 d.width : ℕ) : ℝ) ^ tau₂ HighCost.K :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 d.width) (by linarith [hτ.two])
  have hV0 : (0 : ℝ) ≤ volume prime d := Nat.cast_nonneg _
  have hV1 : 1 ≤ volume prime d := hVpos
  by_cases hg : threshold 2 ≤ d.width
  · obtain ⟨c, hc, hhigh⟩ := hCD (caller.append (guardWith bound)) (fun i => Fin.castAdd 2 (headers i))
      (Fin.castAdd 2 source) d hs hp hg hv (fun i => (hcells _ _).1.trans (ht i))
      (fun i => (hcells _ _).2.trans (hh i)) x ((hcells _ _).1.trans hf) ((hcells _ _).2.trans hhead) lo upper (by
        intro j
        have hm := hprepared (outerSlot j)
        rw [ol.head] at hm
        exact margin_mono hhighReserve hm)
    rw [← hW, hout_set] at hhigh
    have hb := M8.Machine.ArbitraryWidthHighBranchCompositionWithin.runs_within (rho capacity)
      (Supplier.width capacity headers) (flag capacity) (rho_ne_width capacity headers) (rho_ne_flag capacity)
      (width_ne_flag capacity headers)
      (extendOuter (High.program capacity (fun i => Fin.castAdd 2 (headers i)) (Fin.castAdd 2 source)))
      (M8.Machine.ArbitraryWidthOriginalTotalRun.program (fun i => innerSlot capacity (Fin.castAdd 2 (headers i)))
        (innerSlot capacity (Fin.castAdd 2 source)))
      (outer (High.input capacity (caller.append (guardWith bound))))
      (outer (High.input capacity ((setTape caller source W 0).append (guardWith bound))))
      (outer (High.input capacity ((setTape caller source W 0).append (guardWith bound)))) c 0
      (RecursiveChildQuotientsConstant.bits bound) (hs 3)
      (RecursiveChildQuotientsConstant.bits_canonical bound)
      hrr hrh her heh hfr hfh lo upper hselectorMargin (fun _ => extend_outer_within lo upper hzero hhigh) (fun hn => absurd (hcond.mpr hg) hn)
    simp only [ite_eq_left (hcond.mpr hg)] at hb
    have hb' := hb.consequence (fun _ h => h) (fun _ h => h)
      (Nat.add_le_add_right (Nat.add_le_add_right hselect 1) _) (fun _ h => h)
    refine ⟨_, ?_, ((hww.seq hb').seq hwe).consequence (fun _ h => h) (fun _ h => h) le_rfl (fun _ h => h)⟩
    have hmax : max 1 d.width = d.width := max_eq_right (by omega)
    rw [hmax] at hP1 ⊢
    have h1 := cost_arith (w := RecursiveChildQuotientsConstant.cost bound)
      (er := 2 * (RecursiveChildQuotientsConstant.bits bound).length + 4) (n := bound) hV1 rfl hc
    rw [← hL] at h1
    have hB := high_B (C := C) (D := D) (X := C₁ * E) hP1 hV0 (mul_nonneg hC₁.le hE)
    rw [← hA] at hB
    exact bound_le h1 hB hP1 hV0 (Nat.cast_nonneg L)
  · have hfb := M8.Machine.ArbitraryWidthOriginalTotalRunWithin.runs_within cutoff hcut (High.input capacity (caller.append (guardWith bound)))
      (fun i => innerSlot capacity (Fin.castAdd 2 (headers i))) (innerSlot capacity (Fin.castAdd 2 source)) d hs hp hv
      (fun i => (il.tape _ _).trans ((hcells _ _).1.trans (ht i)))
      (fun i => (il.head _ _).trans ((hcells _ _).2.trans (hh i))) x
      ((il.tape _ _).trans ((hcells _ _).1.trans hf)) ((il.head _ _).trans ((hcells _ _).2.trans hhead)) lo upper (by
        intro j
        have hm := hprepared j
        change lo+_ ≤ (outer (High.input capacity (caller.append (guardWith bound)))).head j ∧
          (outer (High.input capacity (caller.append (guardWith bound)))).head j+_ ≤ upper
        exact margin_mono hlowReserve hm)
    rw [← hW, ← il.set, hout_set] at hfb
    have hb := M8.Machine.ArbitraryWidthHighBranchCompositionWithin.runs_within (rho capacity)
      (Supplier.width capacity headers) (flag capacity) (rho_ne_width capacity headers) (rho_ne_flag capacity)
      (width_ne_flag capacity headers)
      (extendOuter (High.program capacity (fun i => Fin.castAdd 2 (headers i)) (Fin.castAdd 2 source)))
      (M8.Machine.ArbitraryWidthOriginalTotalRun.program (fun i => innerSlot capacity (Fin.castAdd 2 (headers i)))
        (innerSlot capacity (Fin.castAdd 2 source)))
      (outer (High.input capacity (caller.append (guardWith bound))))
      (outer (High.input capacity ((setTape caller source W 0).append (guardWith bound))))
      (outer (High.input capacity ((setTape caller source W 0).append (guardWith bound)))) 0
      (M8.Machine.ArbitraryWidthOriginalTotalRun.cost d hs)
      (RecursiveChildQuotientsConstant.bits bound) (hs 3)
      (RecursiveChildQuotientsConstant.bits_canonical bound)
      hrr hrh her heh hfr hfh lo upper hselectorMargin (fun hy => absurd (hcond.mp hy) hg) (fun _ => hfb)
    simp only [ite_eq_right (fun hy => absurd (hcond.mp hy) hg)] at hb
    have hb' := hb.consequence (fun _ h => h) (fun _ h => h)
      (Nat.add_le_add_right (Nat.add_le_add_right hselect 1) _) (fun _ h => h)
    refine ⟨_, ?_, ((hww.seq hb').seq hwe).consequence (fun _ h => h) (fun _ h => h) le_rfl (fun _ h => h)⟩
    have hsmall := HighCost.small_le hτ₂ hC₁.le (show d.width < threshold 2 by omega) hV0 (hb₁ d hs hp hv)
    rw [← hEdef] at hsmall
    have h1 := cost_arith (w := RecursiveChildQuotientsConstant.cost bound)
      (er := 2 * (RecursiveChildQuotientsConstant.bits bound).length + 4) (n := bound) hV1 rfl hsmall
    rw [← hL] at h1
    have hB := low_B (C := C) (D := D) (X := C₁ * E) hP1 hV0
    rw [← hA] at hB
    exact bound_le h1 hB hP1 hV0 (Nat.cast_nonneg L)

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.SupplierWithin
