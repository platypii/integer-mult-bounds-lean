import IntegerMultBounds.Machine.ActivePrefixDirtyControlData

/-! Dirty-U offset metadata comes from exactly six original descriptors.
The count, compact width, wide output width and prefix cardinality are physical
power/product outputs; neither synthetic source padding nor f=n+1 is used. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlHeaders
noncomputable section
open ActivePrefixDirtyControlData
open BinaryVaryingOffsetGatherPlaced (Kind)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ} {k : Kind}

def bank (v : Tapes 15 a) := CleanSubbank.bank (s := 24) v

def core := seq (seq (seq
  (CompactGadgetReservationHeadersPowerRound.powerProgram (a := a) powerFocus (by decide))
  (CompactGadgetReservationHeadersCore.productProgram widthFocus (by decide)))
  (CompactGadgetReservationHeadersCore.productProgram countFocus (by decide)))
  (CompactGadgetReservationHeadersCore.productProgram wideFocus (by decide))
def program := extend (core (a := a)) 9

def cost (s : Shape k) := FixedBasePowerDescriptor.constant 2*2^s.W+
  (53*(s.n*s.b)+28)+(53*(s.n*2^s.W)+28)+(53*(s.n*s.q)+28)+3

theorem pad15 (v : Tapes 15 a) :
    (CompactGadgetReservationHeadersCore.bank v).append (SharedBank.empty 9 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem core_runs (s : Shape k) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (core (a := a)) (fun v => v=CompactGadgetReservationHeadersCore.bank (base hs))
      (fun v => v=CompactGadgetReservationHeadersCore.bank (headers s hs)) (cost s) := by
  have h₀ := CompactGadgetReservationHeadersPowerRound.power (base (a := a) hs) powerFocus (by decide)
    (hs 0) s.W (hv 0) (hc 0) rfl rfl rfl rfl
  have h₁ := CompactGadgetReservationHeadersCore.product (power (a := a) s hs) widthFocus (by decide)
    (hs 4) (hs 5) s.n s.b s.hb (hv 4) (hv 5) (hc 4) (hc 5) rfl rfl rfl rfl rfl rfl
  have h₂ := CompactGadgetReservationHeadersCore.product (narrow (a := a) s hs) countFocus (by decide)
    (bits (2^s.W)) (hs 5) s.n (2^s.W) (by positivity) (RecursiveChildQuotientsConstant.bits_value _)
    (hv 5) (RecursiveChildQuotientsConstant.bits_canonical _) (hc 5) rfl rfl rfl rfl rfl rfl
  have h₃ := CompactGadgetReservationHeadersCore.product (counted (a := a) s hs) wideFocus (by decide)
    (hs 3) (hs 5) s.n s.q (by have := s.hbq; omega) (hv 3) (hv 5) (hc 3) (hc 5) rfl rfl rfl rfl rfl rfl
  exact (((h₀.seq h₁).seq h₂).seq h₃).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem runs (s : Shape k) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun v => v=bank (base hs)) (fun v => v=bank (headers s hs)) (cost s) := by
  simpa only [program,pad15] using hoare_extend_eq (core_runs s hs hv hc) (SharedBank.empty 9 a)

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlHeaders
