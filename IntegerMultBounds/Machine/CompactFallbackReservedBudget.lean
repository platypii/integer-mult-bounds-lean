import IntegerMultBounds.Machine.CompactFallbackActualBudget

/-! The original individual-work reservation contains low back-field axes and
high row/front-field axes. Their exact occurrence map supplies real sparse-axis
call costs to the uniform cutoff budget; they are not treated as one contiguous
prefix of the original address. The occurrence controller is a separate layer. -/
namespace IntegerMultBounds.Machine.CompactFallbackReservedBudget
noncomputable section
open Filter Sizes Parameters CompactReservationCutoff CompactReservationGrowth
open CompactFallbackActualBudget

def back (n : ℕ) := CompactGadgetReservationCapacity.backChunks (d n) (guard n) (K n)

def selectedIndex (c m n D j : ℕ) :=
  if j<min (back n) (processed c m n D) then j else D-processed c m n D+j

theorem selected_lt (c m n D j : ℕ) (hj : j<processed c m n D) : selectedIndex c m n D j<D := by
  have hp : processed c m n D≤D := Nat.min_le_left _ _
  unfold selectedIndex
  split_ifs <;> omega

theorem selected_injective (c m n D : ℕ) :
    Function.Injective (fun j : Fin (processed c m n D) => selectedIndex c m n D j) := by
  intro i j he
  have hp : processed c m n D≤D := Nat.min_le_left _ _
  apply Fin.ext
  unfold selectedIndex at he
  dsimp only at he
  split_ifs at he <;> omega

theorem small_index (c m n D j : ℕ) (hD : D≤reserved c m n) : selectedIndex c m n D j=j := by
  rw [selectedIndex,(fallback c m n D hD).1,Nat.sub_self]
  split_ifs <;> omega

theorem reserved_back_le (c m n : ℕ) : back n≤reserved c m n := by
  unfold back reserved CompactGlobalReservation.reservedAxes
  omega

theorem large_index (c m n D j : ℕ) (hD : reserved c m n≤D) :
    selectedIndex c m n D j=if j<back n then j else D-reserved c m n+j := by
  have hp : processed c m n D=reserved c m n := Nat.min_eq_right hD
  rw [selectedIndex,hp,Nat.min_eq_left (reserved_back_le c m n)]

theorem high_axis (c m n D j : ℕ) (hD : reserved c m n≤D)
    (hback : back n≤j) (hj : j<reserved c m n) :
    D-(CompactGlobalRowPadding.rowAxes c m (d n)+
      CompactGadgetReservationCapacity.frontChunks (d n) (guard n) (K n))≤selectedIndex c m n D j ∧
      selectedIndex c m n D j<D := by
  rw [large_index c m n D j hD,ite_eq_right (by omega)]
  unfold reserved CompactGlobalReservation.reservedAxes back at *
  omega

def cost (c m n D rho : ℕ) :=
  CompactFallbackBudget.cost c m n D (fun j => axisCost n D rho (selectedIndex c m n D j))

/-- Uniform savings now charge the physical original-header calls at the
actual reserved positions. The small branch automatically reduces to all D
original chunk axes, and no dimension-versus-reservation premise is needed. -/
theorem eventually_cost (c m : ℕ) (hm : 2≤m) (η : ℝ) (hη : 0<η) :
    ∀ᶠ n : ℕ in atTop, ∀ D rho : ℕ, D≤d n → rho<K n →
      (cost c m n D rho : ℝ)≤η*(baseVolume n D : ℝ)*(d n : ℝ)^lam' := by
  filter_upwards [CompactFallbackBudget.eventually_cost c m CompactFallbackActualBudget.constant hm η hη]
    with n hn D rho hD hr
  exact hn D (baseVolume n D) _ (fun j hj =>
    axisCost_le n D rho (selectedIndex c m n D j) hD hr (selected_lt c m n D j hj))

end
end IntegerMultBounds.Machine.CompactFallbackReservedBudget
