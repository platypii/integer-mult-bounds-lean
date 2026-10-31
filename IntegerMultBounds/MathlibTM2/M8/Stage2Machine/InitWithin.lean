module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreSparse
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.HighCostWithin
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Init
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExecutionInitializeCleanup

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.InitWithin

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ArbitraryWidthHighLayout
open SharedPlacementAlphabet (setTape)
open FixedHeaderSparseBankCopy (headerBank)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open M8.Machine.ArbitraryWidthHighExchangeJoin (exchangeCount movementCount)
open M8.Machine.ArbitraryWidthExecutionPrivateHeadersCore (blankTape emptyOne emptyTwo)
open M8.Machine.ArbitraryWidthExecutionPrivateHeadersRoot (exchangeSlots exchangeWords exchange_injective)
open M8.Machine.ArbitraryWidthExecutionPrivateHeadersMovement (movementSlots movementWords movement_injective)
open M8.Machine.ArbitraryWidthHighExecutionInitialize (Sources Bounded exchangePrivate movementPrivate
  exchangeCopy movementCopy movementFocus exchange_room movement_room)
open RevMachine
open FamilyRoot (FamilySpec)
open HighBody (Exponents tau₂ padCount)
open CoreSparse (paddedSlots paddedWords paddedSlots_injective)
open Params (r padded view threshold)

variable [M8.Machine.Net] {k : ℕ} (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)
variable {t : ℕ}

open Init

def coefficient (k cutoff D : ℕ) : ℕ :=
  max (400*D+HighBodyWithin.coefficient k cutoff) (800*D)

theorem runs (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n) (D : ℕ) (hτ : Exponents HighCost.K) {b : ℕ} (hb : 2 ≤ b) :
    ∃ C : ℝ, ∀ P e G B : ℕ, threshold b ≤ e → 0 < P → 0 < G → 0 < B →
      ∀ (hs : Fin 6 → List Bool) (rs ss op oe : List Bool),
      RecursiveDimensionBank.Headers (originalDescriptor P e G B) hs →
      HighBody.JoinCounters P e (r b e) G B rs ss op oe →
      ∀ ph : Fin 4 → List Bool,
      M8.Machine.ArbitraryWidthPaddedPiecePadding.Headers (joinedDescriptor prime P e (r b e) G B) (padded b e) ph →
      ∀ {t : ℕ} (caller : Tapes t prime) (focus : Fin t) (exchange : Fin 7 → Fin t) (movement : Fin 5 → Fin t)
        (padding : Fin (4+15) → Fin t) (V : ℕ), 0 < V →
      Sources caller exchange (exchangeWords hs rs) → Sources caller movement (movementWords ss op oe rs) →
      Sources caller padding (coreWords b ph P e G B) →
      Bounded (exchangeWords hs rs) V → Bounded (movementWords ss op oe rs) V →
      Bounded (coreWords b ph P e G B) V →
      ∀ x : Fin (volume prime (originalDescriptor P e G B)) → ZMod 2,
      caller.tape focus = sourceWord x → caller.head focus = 0 → V ≤ D*volume prime (originalDescriptor P e G B) → ∀ lo hi : ℤ,
      (∀ j, lo+(coefficient k cutoff D*volume prime (originalDescriptor P e G B) : ℕ) ≤
        (input capacity caller).head j ∧ (input capacity caller).head j+
          (coefficient k cutoff D*volume prime (originalDescriptor P e G B) : ℕ) ≤ hi) → ∃ c : ℕ,
        (c : ℝ) ≤ C * volume prime (originalDescriptor P e G B) * (e : ℝ) ^ tau₂ HighCost.K + 802 * V ∧
        HoareWithin (program capacity focus exchange movement padding) (fun w => w = input capacity caller)
          (fun w => w = input capacity
            (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)) c (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  obtain ⟨C, hC⟩ := HighCostWithin.runs capacity cutoff hcut hτ hb
  refine ⟨C, fun P e G B he hP hG hB hs rs ss op oe hv hj ph hph t caller focus exchange movement padding V hV
    sx sm sp bx bm bp x hf hh hdom lo hi hmargin => ?_⟩
  have h1 := fills capacity caller exchange movement padding hs rs ss op oe _ V hV sx sm sp bx bm bp
  let W := volume prime (originalDescriptor P e G B)
  have hreserve : 400*V+HighBodyWithin.coefficient k cutoff*W ≤ coefficient k cutoff D*W := by
    calc
      _ ≤ (400*D+HighBodyWithin.coefficient k cutoff)*W := by
        have h := Nat.mul_le_mul_left 400 hdom
        dsimp only [W]
        nlinarith only [h]
      _ ≤ _ := Nat.mul_le_mul_right W (le_max_left _ _)
  have hcleanup : 2*(400*V) ≤ coefficient k cutoff D*W := by
    calc
      _ ≤ (800*D)*W := by
        have h := Nat.mul_le_mul_left 800 hdom
        dsimp only [W]
        nlinarith only [h]
      _ ≤ _ := Nat.mul_le_mul_right W (le_max_right _ _)
  have hw1 := HoareWithin.of_time_heads h1 lo hi (by
    rintro z rfl j
    have hm := hmargin j
    dsimp only [W] at hreserve
    omega)
  have hprepared : ∀ j, lo+(HighBodyWithin.coefficient k cutoff*W : ℕ) ≤
      (output capacity caller hs rs ss op oe (coreWords b ph P e G B)).head j ∧
      (output capacity caller hs rs ss op oe (coreWords b ph P e G B)).head j+
        (HighBodyWithin.coefficient k cutoff*W : ℕ) ≤ hi := by
    intro j
    have ht := h1.head_change j
    have hm := hmargin j
    dsimp only [W] at hreserve ⊢
    omega
  have hbank (c' : Tapes t prime) : HighBody.privateBanks capacity HighCost.K hs rs ss op oe
      blankTape 0 emptyOne emptyOne emptyTwo ph (view b P e G B) blankTape 0 emptyOne emptyTwo c' =
      output capacity c' hs rs ss op oe (coreWords b ph P e G B) := by
    unfold HighBody.privateBanks output
    rw [CoreSparse.padded_sparse]
    rfl
  obtain ⟨c, hc, h2⟩ := hC P e G B he hP hG hB hs rs ss op oe hv hj ph hph blankTape 0 emptyOne emptyOne emptyTwo
    M8.Machine.RootExecution.blank_ready blankTape 0 emptyOne emptyTwo
    ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩ caller focus x hf hh lo hi (by rw [hbank]; exact hprepared)
  simp only [hbank] at h2
  have h3 := erases capacity (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)
    hs rs ss op oe _ V hV bx bm bp
  have hcallerHeads : (setTape caller focus
      (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0).head = caller.head := by
    funext j
    by_cases hj : j = focus
    · subst j; simp only [setTape,Function.update_self,hh]
    · simp only [setTape,Function.update_of_ne hj]
  have hheads := Tapes.append_head_congr _ _ (SharedBank.empty (padCount capacity) prime)
    (SharedBank.empty (padCount capacity) prime)
    (Tapes.append_head_congr _ _ (SharedBank.empty movementCount prime)
      (SharedBank.empty movementCount prime)
      (Tapes.append_head_congr _ _ (SharedBank.empty exchangeCount prime)
        (SharedBank.empty exchangeCount prime) hcallerHeads rfl) rfl) rfl
  change (input capacity (setTape caller focus
      (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)).head =
    (input capacity caller).head at hheads
  have hw3 := HoareWithin.of_time_post_heads h3 lo hi (by
    rintro w rfl j
    rw [hheads]
    have hm := hmargin j
    dsimp only [W] at hcleanup
    omega)
  refine ⟨400*V+1+c+1+400*V, ?_, ?_⟩
  · have hV1 : (1 : ℝ) ≤ V := by exact_mod_cast hV
    push_cast
    linarith only [hc,hV1]
  · simpa only [program] using (hw1.seq h2).seq hw3

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.InitWithin
