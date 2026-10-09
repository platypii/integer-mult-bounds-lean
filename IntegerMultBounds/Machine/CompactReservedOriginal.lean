import IntegerMultBounds.Machine.CompactReservedLifecycle
import IntegerMultBounds.Machine.CompactFallbackReservedBudget

/-! The complete nonfallback reservation machine visits the actual low back
and high row/front positions, using runtime counts derived from original
geometry and erasing every generated control before returning. -/
namespace IntegerMultBounds.Machine.CompactReservedOriginal
noncomputable section
open CompactReservedHeaders
open CompactFallbackAxisRun (Array Width word volume)
open CompactReservedSchedule (bank)
open CompactGadgetReservationCapacity (backChunks)

def low (inverse : Bool) (D K rho ell q d G : ℕ) (f : Array D K ell) :=
  CompactReservedAxisRun.run inverse D K rho ell q 0 (backChunks d G K) f
def result (inverse : Bool) (c m D K rho ell q d G : ℕ) (f : Array D K ell) :=
  CompactReservedAxisRun.run inverse D K rho ell q (D-high c m d G K) (high c m d G K)
    (low inverse D K rho ell q d G f)

def program (inverse : Bool) (c m : ℕ) :=
  seq (seq (seq (seq (CompactReservedLifecycle.setup c m)
    (CompactReservedSchedule.program inverse 9))
    (CompactReservedLifecycle.headerProgram CompactReservedLifecycle.switch))
    (CompactReservedSchedule.program inverse 10))
    (CompactReservedLifecycle.headerProgram CompactReservedLifecycle.cleanup)

def cost (c m D K rho ell q d G : ℕ) :=
  CompactReservedHeaders.cost c m D K rho ell q d G+
  CompactReservedSchedule.cost D K ell q (backChunks d G K)+
  CompactChildHeadersArithmetic.scheduleCost CompactReservedLifecycle.switch
    (prepared c m D K rho ell q d G (backChunks d G K))+
  CompactReservedSchedule.cost D K ell q (high c m d G K)+
  CompactChildHeadersArithmetic.scheduleCost CompactReservedLifecycle.cleanup
    (prepared c m D K rho ell q d G D)+4

theorem width_result (inverse : Bool) (c m D K rho ell q d G : ℕ)
    (f : Array D K ell) (hw : Width D K ell q f) :
    Width D K ell q (result inverse c m D K rho ell q d G f) :=
  CompactReservedAxisRun.width_run inverse D K rho ell q _ _ _
    (CompactReservedAxisRun.width_run inverse D K rho ell q _ _ f hw)

theorem runs (inverse : Bool) (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hK : 0<K) (hr : rho<K) (hD : reserved c m d G K≤D)
    (f : Array D K ell) (hw : Width D K ell q f) :
    HoareTime (program inverse c m) (fun v => v=bank (initial D K rho ell q d G) (word f))
      (fun v => v=bank (initial D K rho ell q d G) (word (result inverse c m D K rho ell q d G f)))
      (cost c m D K rho ell q d G) := by
  have hh : high c m d G K≤D := by unfold reserved at hD; omega
  have hb : backChunks d G K≤D := by unfold reserved at hD; omega
  have he : D-high c m d G K+high c m d G K=D := Nat.sub_add_cancel hh
  have h0 := CompactReservedLifecycle.setup_runs c m D K rho ell q d G hc hm hd hK hD (word f)
  have h1 := CompactReservedSchedule.runs inverse c m D K rho ell q d G 0 (backChunks d G K) 9
    rfl hK hr (by omega) f hw
  simp only [Nat.zero_add] at h1
  have h2 := CompactReservedLifecycle.switch_runs c m D K rho ell q d G (backChunks d G K)
    (word (low inverse D K rho ell q d G f))
  have h3 := CompactReservedSchedule.runs inverse c m D K rho ell q d G (D-high c m d G K) (high c m d G K) 10
    rfl hK hr (by omega) (low inverse D K rho ell q d G f)
    (CompactReservedAxisRun.width_run inverse D K rho ell q 0 (backChunks d G K) f hw)
  rw [he] at h3
  have h4 := CompactReservedLifecycle.cleanup_runs c m D K rho ell q d G D
    (word (result inverse c m D K rho ell q d G f))
  exact ((((h0.seq h1).seq h2).seq h3).seq h4).consequence (fun _ h => h) (fun _ h => h)
    (by unfold cost; omega)

/-- The second interval is exactly the high branch of the frozen distinct
reservation occurrence map at the actual multiplier's global choices. -/
theorem actual_high_index (c m n D j : ℕ)
    (hD : CompactReservationGrowth.reserved c m n≤D) :
    D-high c m (Sizes.d n) (CompactReservationGrowth.guard n) (Sizes.K n)+j=
      CompactFallbackReservedBudget.selectedIndex c m n D
        (CompactFallbackReservedBudget.back n+j) := by
  rw [CompactFallbackReservedBudget.large_index c m n D _ hD,ite_eq_right (by omega)]
  unfold CompactReservationGrowth.reserved CompactGlobalReservation.reservedAxes
    CompactFallbackReservedBudget.back high at *
  omega

end
end IntegerMultBounds.Machine.CompactReservedOriginal
