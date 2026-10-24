module

public import IntegerMultBounds.MathlibTM2.Routing.BlockExchangeChain
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirPlacement

/-!
# The concrete three-call reservoir interchange schedule

A zero-width first exchange handles reservoir zero with the same fixed program.
The actual rank schedule has exactly the coordinate action proved previously for
reservoir placement. `exchangeChain_exec` executes this concrete schedule and
prices all calls from prepared banks; uniform header generation remains open.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable (n H : ℕ) (hfit : 9 * H ≤ n)

def reservoirFrontSpec (k : Fin 3) : BlockExchangeSpec n where
  a := 0
  b := k.val * (3 * H)
  w := if k.val = 0 then 0 else 3 * H
  separate := by
    split_ifs with hk
    · omega
    · have hk' : 1 ≤ k.val := by omega
      nlinarith
  fits := by
    split_ifs with hk
    · simp [hk]
    · have hk' : k.val ≤ 2 := by omega
      nlinarith

variable (w : ℕ) (hw : w ≤ H)

def reservoirExchangeSpecs (k : Fin 3) : Fin 3 → BlockExchangeSpec n :=
  ![reservoirFrontSpec n H hfit k,
    ⟨w, n - 2 * w, w, by omega, by omega⟩,
    ⟨2 * w, n - w, w, by omega, by omega⟩]

theorem reservoirExchangeWidthPrice_sum (k : Fin 3) (reverse : Bool) (price : ℕ → ℝ) :
    ((if reverse then ([2, 1, 0] : List (Fin 3)) else [0, 1, 2]).map
      (fun j => price (reservoirExchangeSpecs n H hfit w hw k j).w)).sum =
      price (if k.val = 0 then 0 else 3 * H) + 2 * price w := by
  cases reverse <;> simp [reservoirExchangeSpecs, reservoirFrontSpec] <;> ring

theorem reservoirExchangeWidthPrice_sum_le (k : Fin 3) (reverse : Bool)
    (price : ℕ → ℝ) (hprice : Monotone price) :
    ((if reverse then ([2, 1, 0] : List (Fin 3)) else [0, 1, 2]).map
      (fun j => price (reservoirExchangeSpecs n H hfit w hw k j).w)).sum ≤
      price (3 * H) + 2 * price w := by
  rw [reservoirExchangeWidthPrice_sum]
  have hfront : (if k.val = 0 then 0 else 3 * H) ≤ 3 * H := by split_ifs <;> omega
  exact add_le_add (hprice hfront) (le_refl _)

theorem reservoirExchangeWidthPower_sum_le (k : Fin 3) (reverse : Bool) :
    ((if reverse then ([2, 1, 0] : List (Fin 3)) else [0, 1, 2]).map
      (fun j => ((max 1 (reservoirExchangeSpecs n H hfit w hw k j).w : ℕ) : ℝ) ^ Parameters.tau)).sum ≤
      ((max 1 (3 * H) : ℕ) : ℝ) ^ Parameters.tau +
        2 * ((max 1 w : ℕ) : ℝ) ^ Parameters.tau := by
  apply reservoirExchangeWidthPrice_sum_le n H hfit w hw k reverse
    (fun width => ((max 1 width : ℕ) : ℝ) ^ Parameters.tau)
  intro x y hxy
  apply Real.rpow_le_rpow (by positivity)
  · exact_mod_cast max_le_max_left 1 hxy
  · norm_num [Parameters.tau]

omit w hw in
theorem reservoirFrontSpec_coordinate (k : Fin 3) :
    (reservoirFrontSpec n H hfit k).coordinate = reservoirFrontPerm n H hfit k := by
  by_cases hk : k.val = 0
  · ext i
    simp [reservoirFrontSpec, BlockExchangeSpec.coordinate, blockExchangePerm,
      reservoirFrontPerm, hk, blockExchange]
  · simp [reservoirFrontSpec, BlockExchangeSpec.coordinate, reservoirFrontPerm, hk]

def reservoirExchangeRank (k : Fin 3) (R : ℕ) : Equiv.Perm (Fin (R * 2 ^ n)) :=
  (((reservoirExchangeSpecs n H hfit w hw k 0).rank R).trans
    ((reservoirExchangeSpecs n H hfit w hw k 1).rank R)).trans
      ((reservoirExchangeSpecs n H hfit w hw k 2).rank R)

theorem reservoirExchangeRank_row (k : Fin 3) (R : ℕ) (i : Fin (R * 2 ^ n)) :
    (reservoirExchangeRank n H hfit w hw k R i).val / 2 ^ n = i.val / 2 ^ n := by
  change (((reservoirExchangeSpecs n H hfit w hw k 2).rank R)
    (((reservoirExchangeSpecs n H hfit w hw k 1).rank R)
      (((reservoirExchangeSpecs n H hfit w hw k 0).rank R) i))).val / 2 ^ n = _
  rw [BlockExchangeSpec.rank_row, BlockExchangeSpec.rank_row, BlockExchangeSpec.rank_row]

theorem reservoirExchangeRank_bit (k : Fin 3) (R : ℕ)
    (i : Fin (R * 2 ^ n)) (q : Fin n) :
    (reservoirExchangeRank n H hfit w hw k R i).val.testBit q.val =
      i.val.testBit (reservoirPlacement n H hfit w hw k q).val := by
  change (((reservoirExchangeSpecs n H hfit w hw k 2).rank R)
    (((reservoirExchangeSpecs n H hfit w hw k 1).rank R)
      (((reservoirExchangeSpecs n H hfit w hw k 0).rank R) i))).val.testBit q.val = _
  rw [BlockExchangeSpec.rank_bit, BlockExchangeSpec.rank_bit, BlockExchangeSpec.rank_bit]
  have hf : (reservoirExchangeSpecs n H hfit w hw k 0).coordinate =
      reservoirFrontPerm n H hfit k := reservoirFrontSpec_coordinate n H hfit k
  rw [hf]
  rfl

/-- The executed list schedule moves exactly the records of the concrete placement. -/
theorem reservoirExchangeChainData_eq {α : Type*} (k : Fin 3) (R : ℕ)
    (l : List (List α)) (hl : l.length = R * 2 ^ n) :
    exchangeChainData (R := R) (reservoirExchangeSpecs n H hfit w hw k) [0, 1, 2] l =
      moveRecs (reservoirExchangeRank n H hfit w hw k R) l := by
  rw [reservoirExchangeRank, moveRecs_trans _ _ l hl, moveRecs_trans _ _ l hl]
  rfl

theorem reservoirExchangeChainData_inverse {α : Type*} (k : Fin 3) (R : ℕ)
    (l : List (List α)) (hl : l.length = R * 2 ^ n) :
    exchangeChainData (R := R) (reservoirExchangeSpecs n H hfit w hw k) [2, 1, 0] l =
      moveRecs (reservoirExchangeRank n H hfit w hw k R).symm l := by
  have he : (reservoirExchangeRank n H hfit w hw k R).symm =
      (((reservoirExchangeSpecs n H hfit w hw k 2).rank R).trans
        ((reservoirExchangeSpecs n H hfit w hw k 1).rank R)).trans
          ((reservoirExchangeSpecs n H hfit w hw k 0).rank R) := by
    ext i
    rfl
  rw [he, moveRecs_trans _ _ l hl, moveRecs_trans _ _ l hl]
  rfl

def reservoirExchangeOrder (reverse : Bool) : List (Fin 3) :=
  if reverse then [2, 1, 0] else [0, 1, 2]

def reservoirExchangeAction (k : Fin 3) (R : ℕ) (reverse : Bool) :
    Equiv.Perm (Fin (R * 2 ^ n)) :=
  if reverse then (reservoirExchangeRank n H hfit w hw k R).symm
  else reservoirExchangeRank n H hfit w hw k R

theorem reservoirExchangeChainData_direction {α : Type*} (k : Fin 3) (R : ℕ)
    (reverse : Bool) (l : List (List α)) (hl : l.length = R * 2 ^ n) :
    exchangeChainData (R := R) (reservoirExchangeSpecs n H hfit w hw k)
      (reservoirExchangeOrder reverse) l =
        moveRecs (reservoirExchangeAction n H hfit w hw k R reverse) l := by
  cases reverse
  · exact reservoirExchangeChainData_eq n H hfit w hw k R l hl
  · exact reservoirExchangeChainData_inverse n H hfit w hw k R l hl

/-- Executed concrete reservoir placement from prepared canonical headers,
with all three calls charged and every register except the stream restored. -/
theorem reservoirPlacement_exec {t₀ T Q K R B : ℕ} {U F : Type} (reservoir : Fin 3) (reverse : Bool)
    (body : F → Pr F T Q (prime + K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd)
    (hQ : swapStates hd pay hhd ≤ Q)
    (bank : Fin 3 → Fin (swapT t₀) → Fin T) (hbank : ∀ j, Function.Injective (bank j))
    (hT : swapT t₀ ≤ T) (str tmp : Fin T) (hst : str ≠ tmp)
    (hstr : ∀ j k, bank j k ≠ str) (htmp : ∀ j k, bank j k ≠ tmp)
    (hR : 0 < R) (hB : 0 < B) (hs : Fin 3 → Fin 5 → List Bool)
    (hv : ∀ j k, Counter.value (hs j k) = swapValues
      (blockExchangeDimensions n ((reservoirExchangeSpecs n H hfit w hw reservoir) j).a ((reservoirExchangeSpecs n H hfit w hw reservoir) j).b ((reservoirExchangeSpecs n H hfit w hw reservoir) j).w R B).1
      (blockExchangeDimensions n ((reservoirExchangeSpecs n H hfit w hw reservoir) j).a ((reservoirExchangeSpecs n H hfit w hw reservoir) j).b ((reservoirExchangeSpecs n H hfit w hw reservoir) j).w R B).2.1
      (blockExchangeDimensions n ((reservoirExchangeSpecs n H hfit w hw reservoir) j).a ((reservoirExchangeSpecs n H hfit w hw reservoir) j).b ((reservoirExchangeSpecs n H hfit w hw reservoir) j).w R B).2.2
      ((reservoirExchangeSpecs n H hfit w hw reservoir) j).w ((reservoirExchangeSpecs n H hfit w hw reservoir) j).w k)
    (hc : ∀ j k, GrowingCounterData.Canonical (hs j k))
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ k, S.L k = []) (htmp0 : S.R tmp = [])
    (hpay0 : ∀ j, S.R (bank j (reg pay)) = [])
    (hpriv : ∀ j k, t₀ ≤ k.val → S.R (bank j k) = [])
    (hhdr : ∀ j k, S.R (bank j (reg (hd k))) = separator :: (hs j k).map bitSymbol)
    (hother : ∀ j i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (bank j (reg i)), s ≠ blank ∧ s.val < prime + 4)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ s ∈ r, s.val < 8)
    (hsrc : S.R str = l.flatten) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ exchangeChainCost (reservoirExchangeSpecs n H hfit w hw reservoir) bank R B S (reservoirExchangeOrder reverse) ∧
      Exec body (exchangeChain hd pay hhd hQ bank hbank hT str tmp (reservoirExchangeOrder reverse)) (mk v S) m
        (mk v' { S with R := Function.update S.R str (moveRecs (reservoirExchangeAction n H hfit w hw reservoir R reverse) l).flatten }) := by
  obtain ⟨v', m, hu, hm, he⟩ := exchangeChain_exec (reservoirExchangeSpecs n H hfit w hw reservoir)
    body hd pay hhd hQ bank hbank hT str tmp hst hstr htmp hR hB hs hv hc
    (reservoirExchangeOrder reverse) v S hL htmp0 hpay0 hpriv hhdr hother l hl hlB h8 hsrc
  rw [reservoirExchangeChainData_direction n H hfit w hw reservoir R reverse l hl] at he
  exact ⟨v', m, hu, hm, he⟩

end IntegerMultBounds.MathlibTM2.Routing
