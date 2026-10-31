module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Prepared
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.InitWithin
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Width
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighBranchPrepare
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighHeaderBounds

/-! Generated dimension/join metadata, atom-width computation and their
recovery surround the bounded initialized body. Setup and cleanup have linear
head travel, so one fixed reserve covers every prefix of the actual program. -/
@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.PreparedWithin

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ArbitraryWidthHighLayout (originalDescriptor joinedDescriptor)
open SharedPlacementAlphabet (setTape)
open FlatCoordinateSchedule (bits)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open M8.Machine.ArbitraryWidthHighExchangeJoin (exchangeCount movementCount)
open M8.Machine.ArbitraryWidthHighExecutionInitialize (Sources Bounded)
open M8.Machine.ArbitraryWidthExecutionPrivateHeadersRoot (exchangeWords)
open M8.Machine.ArbitraryWidthExecutionPrivateHeadersMovement (movementWords)
open M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring (bank baseSlot dimensionSlot joinedSlot zeroSlot
  exchangeFocus movementFocus paddingWords)
open RevMachine
open FamilyRoot (FamilySpec)
open HighBody (Exponents tau₂ padCount)
open Params (r padded view threshold)

open Prepared
variable [M8.Machine.Net]

def setupCoefficient : ℕ := ArbitraryWidthHighDimensions.linearConstant prime+429+200*Width.constant

def cleanupCoefficient : ℕ := 333+20000*533+1

def coefficient (k cutoff : ℕ) : ℕ :=
  max (setupCoefficient+InitWithin.coefficient k cutoff 2) (2*cleanupCoefficient)

variable {k : ℕ}
  (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)

theorem runs (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n) (hτ : Exponents HighCost.K) :
    ∃ C D : ℝ, ∀ {t : ℕ} (base : Tapes t prime) (focus : Fin t)
      (dimensions : Fin 5 → Fin t) (joined : Fin 6 → Fin t) (exchange : Fin 7 → Fin t)
      (rowsSlot roundedSlot : Fin t) (P e G B : ℕ), threshold 2 ≤ e →
      0 < P → 0 < G → 0 < B →
      ∀ (dh : Fin 5 → List Bool) (jh : Fin 6 → List Bool) (hs : Fin 6 → List Bool)
        (rs rowBits roundedBits : List Bool),
      (∀ i, Counter.value (dh i) = ArbitraryWidthHighDimensions.originalValues P G B e (r 2 e) i) →
      (∀ i, GrowingCounterData.Canonical (dh i)) →
      (∀ i, Counter.value (jh i) =
        ArbitraryWidthJoinedHeaders.originalValues P G B e (r 2 e) (padded 2 e) i) →
      (∀ i, GrowingCounterData.Canonical (jh i)) →
      Sources base dimensions dh → Sources base joined jh → Sources base exchange (exchangeWords hs rs) →
      RecursiveDimensionBank.Headers (originalDescriptor P e G B) hs →
      Counter.value rs = r 2 e → GrowingCounterData.Canonical rs →
      Counter.value rowBits = prime^(2*r 2 e) → GrowingCounterData.Canonical rowBits →
      Counter.value roundedBits = padded 2 e → GrowingCounterData.Canonical roundedBits →
      base.tape rowsSlot = RadixZeroFill.encodedBinary rowBits → base.head rowsSlot = 1 →
      base.tape roundedSlot = RadixZeroFill.encodedBinary roundedBits → base.head roundedSlot = 1 →
      ∀ x : Fin (volume prime (originalDescriptor P e G B)) → ZMod 2,
      base.tape focus = sourceWord x → base.head focus = 0 → ∀ lo upper : ℤ,
      (∀ j, lo+(coefficient k cutoff*volume prime (originalDescriptor P e G B) : ℕ) ≤
        (input capacity base).head j ∧ (input capacity base).head j+
          (coefficient k cutoff*volume prime (originalDescriptor P e G B) : ℕ) ≤ upper) → ∃ c : ℕ,
        (c : ℝ) ≤ C * volume prime (originalDescriptor P e G B) * (e : ℝ) ^ tau₂ HighCost.K +
          D * volume prime (originalDescriptor P e G B) ∧
        HoareWithin (program capacity focus dimensions joined exchange rowsSlot roundedSlot)
          (fun z => z = input capacity base)
          (fun z => z = input capacity (setTape base focus
            (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)) c (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  obtain ⟨C, hC⟩ := InitWithin.runs capacity cutoff hcut 2 hτ (le_refl 2)
  refine ⟨C, ((ArbitraryWidthHighDimensions.linearConstant prime + 429 + 333 + 200 * Width.constant +
    20000 * 533 + 1604 + 6 : ℕ) : ℝ), fun {t} base focus dimensions joined exchange rowsSlot roundedSlot P e G B he hP hG hB
    dh jh hs rs rowBits roundedBits dhv dhc jhv jhc sd sj sx hh hr cr hrows crows hrounded crounded
    rowsTape rowsHead roundedTape roundedHead x hf hhead lo upper hmargin => ?_⟩
  have hfit := Params.fit_of_threshold (le_refl 2) he
  have hdvol := ArbitraryWidthHighPaddingSuffix.original_volume prime P e G B
  obtain ⟨V, hVdef⟩ : ∃ V, V = 2*volume prime (originalDescriptor P e G B) := ⟨_, rfl⟩
  have ho := ArbitraryWidthHighDimensionsShared.original_bounds prime P G B e (r 2 e) Params.prime_two
    (by omega) hP hG hB
  have hU : 0 < volume prime (originalDescriptor P e G B) := by rw [hdvol]; exact ho.1
  have heU : e ≤ volume prime (originalDescriptor P e G B) := by rw [hdvol]; exact ho.2 3
  have hD : 0 < ArbitraryWidthHighDimensions.dataVolume prime P G B e := by rw [← hdvol]; exact hU
  have hs1 := M8.Machine.ArbitraryWidthHighBranchPrepare.setup_cost_bound prime P G B e hD
  have hs2 := M8.Machine.ArbitraryWidthHighBranchPrepare.cleanup_cost_bound prime P G B e hD
  rw [← hdvol, ← hVdef] at hs1 hs2
  let U := volume prime (originalDescriptor P e G B)
  let S := M8.Machine.ArbitraryWidthHighBranchPrepare.setupCost prime P G B e V
  let A := 100*Width.constant*(e-r 2 e+1)
  let E := 20000*(e-r 2 e+2)+20000*530+1
  let F := M8.Machine.ArbitraryWidthHighBranchPrepare.cleanupCost prime P G B e V
  have hsetup : S+A ≤ setupCoefficient*U := by
    have ha : e-r 2 e+1 ≤ 2*U := by dsimp only [U]; omega
    have hb := Nat.mul_le_mul_left (100*Width.constant) ha
    dsimp only [setupCoefficient,S,A,U]
    nlinarith only [hs1,hb]
  have hclean : E+F ≤ cleanupCoefficient*U := by
    have ha : e-r 2 e+2 ≤ 3*U := by dsimp only [U]; omega
    have hb := Nat.mul_le_mul_left 20000 ha
    dsimp only [cleanupCoefficient,E,F,U]
    nlinarith only [hs2,hb,hU]
  have hreserve := Nat.mul_le_mul_right U
    (show setupCoefficient+InitWithin.coefficient k cutoff 2 ≤ coefficient k cutoff from le_max_left _ _)
  rw [Nat.add_mul] at hreserve
  have hcleanup := Nat.mul_le_mul_right U
    (show 2*cleanupCoefficient ≤ coefficient k cutoff from le_max_right _ _)
  rw [Nat.mul_assoc] at hcleanup
  have hV : 0 < V := by omega
  have bP : P ≤ V := by have := ho.2 0; change P ≤ _ at this; rw [← hdvol] at this; omega
  have bG : G ≤ V := by have := ho.2 1; change G ≤ _ at this; rw [← hdvol] at this; omega
  have bB : B ≤ V := by have := ho.2 2; change B ≤ _ at this; rw [← hdvol] at this; omega
  have be : e ≤ V := by have := ho.2 3; change e ≤ _ at this; rw [← hdvol] at this; omega
  have hviewpos : (view 2 P e G B).Positive :=
    ⟨hP, (Params.rows_pos 2 e).trans_le (Params.rows_le 2 e), by change 0 < 1; decide, hG, hB⟩
  have bR : padded 2 e ≤ V := by
    have h1 := RecursiveHeaderBounds.values_le_volume Params.prime_two _ hviewpos 1
    have h2 := Params.volume_le (b := 2) (P := P) (G := G) (B := B) (by omega : r 2 e ≤ e)
    change padded 2 e ≤ _ at h1
    omega
  -- the metadata banks
  have hp := M8.Machine.ArbitraryWidthHighBranchPrepare.constructs dimensions joined base
    prime P G B e (r 2 e) (padded 2 e) V Params.prime_two (by omega) hP hG hB hV dh jh dhv dhc jhv jhc
    bP bG bB be bR sd.tape sd.head sj.tape sj.head
  have hp' := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hp
    (Width.privateIn (q := prime))) (SharedBank.empty exchangeCount prime))
    (SharedBank.empty movementCount prime)) (SharedBank.empty (padCount capacity) prime)
  -- the atom width
  have hj := joined_hdr P G B e (r 2 e) (padded 2 e) jh jhv jhc
  have hwc : ∀ base' : Tapes t prime, (bank base' P G B e (r 2 e) dh jh).tape wslot =
      RadixZeroFill.encodedBinary (bits (e - r 2 e)) ∧ (bank base' P G B e (r 2 e) dh jh).head wslot = 1 := by
    intro base'
    have h := M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.joined_cells base' P G B e (r 2 e) dh jh 3
    rw [hj] at h
    exact ⟨h.2, h.1⟩
  have hw := Width.shared_runs Params.prime_two (bank base P G B e (r 2 e) dh jh) wslot (by omega)
    (hwc base).1 (hwc base).2
  have hw' := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hw
    (SharedBank.empty exchangeCount prime)) (SharedBank.empty movementCount prime))
    (SharedBank.empty (padCount capacity) prime)
  let start := input capacity base
  let middle := Init.input capacity ((bank base P G B e (r 2 e) dh jh).append (Width.privateIn (q := prime)))
  let ready := Init.input capacity ((bank base P G B e (r 2 e) dh jh).append (Width.privateOut (q := prime) (e-r 2 e)))
  have hwp := HoareWithin.of_time_heads hp' lo upper (by
    rintro z rfl j
    change lo+(S : ℕ) ≤ start.head j ∧ start.head j+(S : ℕ) ≤ upper
    have hm := hmargin j
    change lo+_ ≤ start.head j ∧ start.head j+_ ≤ upper at hm
    dsimp only [U] at hsetup hreserve
    omega)
  have hww := HoareWithin.of_time_heads hw' lo upper (by
    rintro z rfl j
    change lo+(A : ℕ) ≤ middle.head j ∧ middle.head j+(A : ℕ) ≤ upper
    have ht := hp'.head_change j
    change start.head j-(S : ℕ) ≤ middle.head j ∧ middle.head j ≤ start.head j+(S : ℕ) at ht
    have hm := hmargin j
    change lo+_ ≤ start.head j ∧ start.head j+_ ≤ upper at hm
    dsimp only [U] at hsetup hreserve
    omega)
  have hprepared : ∀ j, lo+(InitWithin.coefficient k cutoff 2*U : ℕ) ≤ ready.head j ∧
      ready.head j+(InitWithin.coefficient k cutoff 2*U : ℕ) ≤ upper := by
    intro j
    have ht := hp'.head_change j
    have hwhead := hw'.head_change j
    change start.head j-(S : ℕ) ≤ middle.head j ∧ middle.head j ≤ start.head j+(S : ℕ) at ht
    change middle.head j-(A : ℕ) ≤ ready.head j ∧ ready.head j ≤ middle.head j+(A : ℕ) at hwhead
    have hm := hmargin j
    change lo+_ ≤ start.head j ∧ start.head j+_ ≤ upper at hm
    dsimp only [U] at hsetup hreserve ⊢
    omega
  -- the high body
  have mv := M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.movement_values P G B e (r 2 e) rs hr
  have mc := M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.movement_canonical P G B e (r 2 e) rs cr
  have hjc : HighBody.JoinCounters P e (r 2 e) G B rs (ArbitraryWidthHighDimensions.words prime P G B e (r 2 e) 4)
      (ArbitraryWidthHighDimensions.words prime P G B e (r 2 e) 3)
      (ArbitraryWidthHighDimensions.words prime P G B e (r 2 e) 5) :=
    ⟨hr, cr, mv 0, mc 0, mv 1, mc 1, mv 2, mc 2⟩
  have hph := M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.padding_headers P G B e (r 2 e) (padded 2 e) dh
    rowBits roundedBits (dhv 0) hrows hrounded (dhc 0) crows crounded
  have bex := M8.Machine.ArbitraryWidthHighHeaderBounds.exchange_bounded P e G B (r 2 e) hP hG hB (by omega)
    hs rs hh hr cr
  have bmv := M8.Machine.ArbitraryWidthHighHeaderBounds.movement_bounded P e G B (r 2 e) hP hG hB (by omega)
    _ _ _ rs (mv 0) (mc 0) (mv 1) (mc 1) (mv 2) (mc 2) hr cr
  have bpd := padding_bounded P e G B hP hG hB he _ hph
  rw [← hVdef] at bex bmv bpd
  have sxb := sources_append (M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.exchange_sources base P G B e (r 2 e)
    dh jh exchange hs rs sx) (Width.privateOut (q := prime) (e - r 2 e))
  have smb := sources_append (M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.movement_sources base P G B e (r 2 e)
    dh jh exchange hs rs sx) (Width.privateOut (q := prime) (e - r 2 e))
  have spb := padding_sources base P G B e dh jh rowsSlot roundedSlot rowBits roundedBits jhv jhc
    rowsTape rowsHead roundedTape roundedHead
  have hbc := M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring.base_cells base P G B e (r 2 e) dh jh focus
  have hft : ((bank base P G B e (r 2 e) dh jh).append (Width.privateOut (q := prime) (e - r 2 e))).tape
      (low (baseSlot focus)) = sourceWord x := by
    simp only [low, Tapes.append, Fin.addCases_left]
    exact hbc.2.trans hf
  have hfh : ((bank base P G B e (r 2 e) dh jh).append (Width.privateOut (q := prime) (e - r 2 e))).head
      (low (baseSlot focus)) = 0 := by
    simp only [low, Tapes.append, Fin.addCases_left]
    exact hbc.1.trans hhead
  obtain ⟨c, hc, hi⟩ := hC P e G B he hP hG hB hs rs _ _ _ hh hjc _ hph
    ((bank base P G B e (r 2 e) dh jh).append (Width.privateOut (q := prime) (e - r 2 e))) (low (baseSlot focus))
    (fun i => low (exchangeFocus exchange i)) (fun i => low (movementFocus exchange i))
    (padFocus rowsSlot roundedSlot) V hV sxb smb spb bex bmv bpd x hft hfh (by omega) lo upper hprepared
  rw [SharedPlacementAlphabet.setTape_append_left, changed_bank] at hi
  -- the width's erasure
  have hwe := Width.shared_cleans Params.prime_two
    (bank (setTape base focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0) P G B e (r 2 e) dh jh)
    wslot (hwc _).1 (hwc _).2
  have hwe' := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hwe
    (SharedBank.empty exchangeCount prime)) (SharedBank.empty movementCount prime))
    (SharedBank.empty (padCount capacity) prime)
  -- the metadata's erasure
  have hcl := M8.Machine.ArbitraryWidthHighBranchPrepare.cleans dimensions
    (setTape base focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)
    prime P G B e (r 2 e) (padded 2 e) V Params.prime_two (by omega) hP hG hB hV dh jh dhv dhc jhv jhc bP bG bB be bR
  have hcl' := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hcl
    (Width.privateIn (q := prime))) (SharedBank.empty exchangeCount prime))
    (SharedBank.empty movementCount prime)) (SharedBank.empty (padCount capacity) prime)
  let changed := setTape base focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0
  have hbaseHeads : changed.head = base.head := by
    funext j
    by_cases hj : j = focus
    · subst j; simp only [changed,setTape,Function.update_self,hhead]
    · simp only [changed,setTape,Function.update_of_ne hj]
  have hbHeads := Tapes.append_head_congr _ _ ArbitraryWidthZeroHeaderShared.empty
    ArbitraryWidthZeroHeaderShared.empty
    (Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty 12) (FixedHeaderBankCopy.empty 12)
      (Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty 17) (FixedHeaderBankCopy.empty 17) hbaseHeads rfl) rfl) rfl
  have hinputHeads := Tapes.append_head_congr _ _ (SharedBank.empty (padCount capacity) prime)
    (SharedBank.empty (padCount capacity) prime)
    (Tapes.append_head_congr _ _ (SharedBank.empty movementCount prime) (SharedBank.empty movementCount prime)
      (Tapes.append_head_congr _ _ (SharedBank.empty exchangeCount prime) (SharedBank.empty exchangeCount prime)
        (Tapes.append_head_congr _ _ (Width.privateIn (q := prime)) (Width.privateIn (q := prime)) hbHeads rfl) rfl) rfl) rfl
  change (input capacity changed).head = start.head at hinputHeads
  let afterWidth := Init.input capacity ((bank changed P G B e (r 2 e) dh jh).append (Width.privateIn (q := prime)))
  have hwcl := HoareWithin.of_time_post_heads hcl' lo upper (by
    rintro z rfl j
    change lo+2*(F : ℕ) ≤ (input capacity changed).head j ∧
      (input capacity changed).head j+2*(F : ℕ) ≤ upper
    rw [hinputHeads]
    have hm := hmargin j
    change lo+_ ≤ start.head j ∧ start.head j+_ ≤ upper at hm
    dsimp only [U] at hclean hcleanup
    omega)
  have hwwe := HoareWithin.of_time_post_heads hwe' lo upper (by
    rintro z rfl j
    change lo+2*(E : ℕ) ≤ afterWidth.head j ∧ afterWidth.head j+2*(E : ℕ) ≤ upper
    have ht := hcl'.head_change j
    change afterWidth.head j-(F : ℕ) ≤ (input capacity changed).head j ∧
      (input capacity changed).head j ≤ afterWidth.head j+(F : ℕ) at ht
    rw [hinputHeads] at ht
    have hm := hmargin j
    change lo+_ ≤ start.head j ∧ start.head j+_ ≤ upper at hm
    dsimp only [U] at hclean hcleanup
    omega)
  have hrun := (hwp.seq ((hww.seq hi).seq hwwe)).seq hwcl
  refine ⟨_, ?_, hrun.consequence (fun _ h => h) (fun _ h => h) le_rfl (fun _ h => h)⟩
  exact cost_arith hs1 hs2 hVdef heU hU hc rfl

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.PreparedWithin
