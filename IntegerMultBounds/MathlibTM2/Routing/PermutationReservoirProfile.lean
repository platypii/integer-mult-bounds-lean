module

public import IntegerMultBounds.MathlibTM2.Routing.PermutationReservoirTable
public import IntegerMultBounds.MathlibTM2.Routing.RouterMatchingTable

/-! Identify the generated reservoir table on the profile domain and preserve
its involution. Executed canonical production/compilation lives in
`CanonicalPermutationProfile`. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {A : ℕ}

def permutationReservoirLocalWord (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H)
    (k : Fin 3) (second : Bool) (f : Equiv.Perm (Fin n)) (L : ℕ) : List (Fin (A + 4)) :=
  matchingEntryWords L (matchingTableEntries (n - 3 * w) (matchingMateCoordinate
    (reservoirClassLocalMatching n H hfit w hw k (permutationMatchingCoordinate second f)
      (permutationMatchingCoordinate_involutive second f))))

def permutationReservoirSource (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H)
    (k : Fin 3) (second : Bool) (f : Equiv.Perm (Fin n)) (p : Par) (hsize : p.wy = n - 3 * w) : Fin p.wy → Fin p.wy :=
  fun q => Fin.cast hsize.symm (reservoirClassLocalMatching n H hfit w hw k (permutationMatchingCoordinate second f)
    (permutationMatchingCoordinate_involutive second f) (Fin.cast hsize q))

theorem permutationReservoirLocalWord_eq (n H : ℕ) (hfit : 9 * H ≤ n)
    (w : ℕ) (hw : w ≤ H) (k : Fin 3) (second : Bool) (f : Equiv.Perm (Fin n))
    (p : Par) (hsize : p.wy = n - 3 * w) (L : ℕ) :
    permutationReservoirLocalWord (A := A) n H hfit w hw k second f L =
      matchingEntryWords L (matchingTableEntries p.wy
        (matchingMateCoordinate (permutationReservoirSource n H hfit w hw k second f p hsize))) := by
  unfold permutationReservoirLocalWord permutationReservoirSource
  rw [matchingMateCoordinate_cast hsize, hsize]

theorem permutationReservoirSource_involutive (n H : ℕ) (hfit : 9 * H ≤ n)
    (w : ℕ) (hw : w ≤ H) (k : Fin 3) (second : Bool) (f : Equiv.Perm (Fin n))
    (p : Par) (hsize : p.wy = n - 3 * w) :
    Function.Involutive (permutationReservoirSource n H hfit w hw k second f p hsize) := by
  intro q
  have h := reservoirClassLocalMatching_involutive n H hfit w hw k
    (permutationMatchingCoordinate second f) (permutationMatchingCoordinate_involutive second f)
    (Fin.cast hsize q)
  have hc (x : Fin (n - 3 * w)) : Fin.cast hsize (Fin.cast hsize.symm x) = x := by
    apply Fin.ext
    rfl
  dsimp only [permutationReservoirSource]
  rw [hc]
  exact (congrArg (Fin.cast hsize.symm) h).trans (by apply Fin.ext; rfl)

-- The superseded supplied-frame compiler is available in commit 89abda33.

end
end IntegerMultBounds.MathlibTM2.Routing
