module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterArithmetic
public import IntegerMultBounds.MathlibTM2.Routing.RouterMatchingTable
public import IntegerMultBounds.MathlibTM2.Routing.ProfilePlacedMatching

/-! Actual canonical bulk inputs for every router residue. The matching source,
activity, density, all word widths and physical placement are constructed from
one original matching and common record geometry. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

def canonicalRouterLocalMatching (n : ℕ) (hn : canonicalRouterStride n ≤ n) (k : Fin 3)
    (mate : Fin n → Fin n) (hinv : Function.Involutive mate) :
    Fin (routerTargetWidth n (canonicalRouterStride n) (canonicalRouterGap n)) →
      Fin (routerTargetWidth n (canonicalRouterStride n) (canonicalRouterGap n)) :=
  reservoirClassLocalMatching n (routingReservoirWidth n (canonicalRouterGap n))
    (routingReservoir_fit n (canonicalRouterGap n) hn)
    (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
    (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k mate hinv

theorem canonicalRouterLocalMatching_involutive (n : ℕ) (hn : canonicalRouterStride n ≤ n) (k : Fin 3)
    (mate : Fin n → Fin n) (hinv : Function.Involutive mate) :
    Function.Involutive (canonicalRouterLocalMatching n hn k mate hinv) :=
  reservoirClassLocalMatching_involutive n _ _ _ _ k mate hinv

def canonicalRouterInput {Q K : ℕ} (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (k : Fin 3) (reverse : Bool)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8) (r : Fin (canonicalRouterStride n)) :
    GeneratedPlacedInput 6 Q K Empty Empty Unit := by
  let G := canonicalRouterGap n
  let stride := canonicalRouterStride n
  let p := routerProfileParameters n stride G r.val
  let localMate := canonicalRouterLocalMatching n hn k mate hinv
  let targets := matchingDirectionTargets localMate reverse
  have hK : 0 < stride := by
    have := canonicalRouterGap_pos n
    dsimp [stride, canonicalRouterStride]
    omega
  have ht : ∀ q ∈ targets, localMate q ∉ targets :=
    matchingDirectionTargets_source localMate (canonicalRouterLocalMatching_involutive n hn k mate hinv) reverse
  have hfit : 9 * routingReservoirWidth n G ≤ fieldsLen (selectiveLen p 0) := by
    rw [routerProfileFieldsLen n stride G hn r]
    exact routingReservoir_fit n G hn
  have hw : p.wc ≤ routingReservoirWidth n G :=
    routerBorrowed_le_reservoir n G (canonicalRouterGap_pos n)
  apply canonicalGeneratedInput p (canonicalRouterArithmetic n r R B hR hB)
    (routerLocalTargets n stride G hn r targets) (routerLocalSource n stride G hn r localMate)
    (routerLocalSource_allowed n stride G hn r targets localMate ht) hQ hA
    (routingReservoirWidth n G) hfit hw k l ?_ ?_
  · change l.length = R * 2 ^ fieldsLen (selectiveLen p 0)
    rw [routerProfileFieldsLen n stride G hn r]
    exact hl
  · exact hlen

/-- Canonical bulk metadata widths have no matching or record arguments. -/
def canonicalRouterMetadataWidth (n : ℕ) (r : Fin (canonicalRouterStride n))
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) : ℕ :=
  canonicalGeneratedMetadataWidth
    (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)
    (canonicalRouterArithmetic n r R B hR hB)

theorem canonicalRouterInput_length_le {Q K : ℕ} (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (k : Fin 3) (reverse : Bool)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8) (r : Fin (canonicalRouterStride n))
    (j : Fin (inactiveClassifierPlacementT 6))
    (hj : j ≠ inactiveClassifierPlacementEmbed (t₀ := 6)
      (classifierCore (inactiveConfigurationCore repairHost.src))) :
    ((canonicalRouterInput n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r).M.R j).length ≤
      canonicalRouterMetadataWidth n r R B hR hB := by
  dsimp only [canonicalRouterInput, canonicalRouterMetadataWidth]
  exact canonicalGeneratedInput_length_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj

end
end IntegerMultBounds.MathlibTM2.Routing
