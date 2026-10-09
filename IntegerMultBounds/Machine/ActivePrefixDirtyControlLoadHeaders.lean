import IntegerMultBounds.Machine.ActivePrefixDirtyControlLoadData

/-! Rotation dimensions are physical products/powers of original descriptors,
with all three outputs retained only until the final cleanup. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlLoadHeaders
noncomputable section
open ActivePrefixDirtyControlLoadProducer (Mode Shape values width word)
open ActivePrefixDirtyControlLoadData
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ} {m : Mode}

def bank (v : Tapes 14 a) := CleanSubbank.bank (s := 51) v
theorem pad15 (v : Tapes 14 a) :
    (CompactGadgetReservationHeadersCore.bank v).append (SharedBank.empty 36 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def power := extend (CompactGadgetReservationHeadersPowerRound.powerProgram (a := a) powerFocus (by decide)) 36
def makeWidth (m : Mode) := extend (CompactGadgetReservationHeadersCore.productProgram (a := a) (widthFocus m) width_injective) 36
def product := extend (CompactGadgetReservationHeadersCore.productProgram (a := a) productFocus (by decide)) 36
def program (m : Mode) := seq (seq (power (a := a)) (makeWidth m)) product
def cost (s : Shape m) (rows : ℕ) := FixedBasePowerDescriptor.constant 2*2^s.W+
  (53*width s+28)+(53*prefixCount s rows+28)+2

def factorSlot : Mode → Fin 6 | .selected | .correction => 3 | .pure | .negative => 4
def factor (s : Shape m) := values s (factorSlot m)
theorem factor_pos (s : Shape m) : 0<factor s := by
  cases m <;> dsimp [factor,factorSlot,values,ActivePrefixDirtyControlData.values]
  all_goals first | exact s.hb | have := s.hbq; omega
theorem width_eq (s : Shape m) : width s=s.n*factor s := by cases m <;> rfl

theorem power_runs (s : Shape m) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (power (a := a)) (fun v => v=bank (produced (base s rows B hs rs bs x) s))
      (fun v => v=bank (powered (base s rows B hs rs bs x) s)) (FixedBasePowerDescriptor.constant 2*2^s.W) := by
  have h := CompactGadgetReservationHeadersPowerRound.power (produced (base (a := a) s rows B hs rs bs x) s)
    powerFocus (by decide) (hs 0) s.W (hv 0) (hc 0) rfl rfl rfl rfl
  simpa only [power,pad15,powered,show powerFocus 1=(11 : Fin 14) from rfl] using hoare_extend_eq h (SharedBank.empty 36 a)

theorem width_runs (s : Shape m) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (makeWidth (a := a) m) (fun v => v=bank (powered (base s rows B hs rs bs x) s))
      (fun v => v=bank (headers (base s rows B hs rs bs x) s)) (53*width s+28) := by
  have h := CompactGadgetReservationHeadersCore.product (powered (base (a := a) s rows B hs rs bs x) s)
    (widthFocus m) width_injective (hs (factorSlot m)) (hs 5) s.n (factor s) (factor_pos s)
    (hv _) (hv 5) (hc _) (hc 5)
    (by cases m <;> rfl) (by cases m <;> rfl) (by cases m <;> rfl)
    (by cases m <;> rfl) (by cases m <;> rfl) (by cases m <;> rfl)
  simpa only [makeWidth,pad15,headers,←width_eq,show widthFocus m 2=(12 : Fin 14) from rfl]
    using hoare_extend_eq h (SharedBank.empty 36 a)

theorem product_runs (s : Shape m) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs) :
    HoareTime (product (a := a)) (fun v => v=bank (headers (base s rows B hs rs bs x) s))
      (fun v => v=bank (dimensions (base s rows B hs rs bs x) s rows)) (53*prefixCount s rows+28) := by
  have h := CompactGadgetReservationHeadersCore.product (headers (base (a := a) s rows B hs rs bs x) s)
    productFocus (by decide) (bits (2^s.W)) rs rows (2^s.W) (by positivity)
    (RecursiveChildQuotientsConstant.bits_value _) hr (RecursiveChildQuotientsConstant.bits_canonical _) cr
    rfl rfl rfl rfl rfl rfl
  simpa only [product,pad15,dimensions,prefixCount,show productFocus 2=(13 : Fin 14) from rfl]
    using hoare_extend_eq h (SharedBank.empty 36 a)

theorem runs (s : Shape m) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs) :
    HoareTime (program (a := a) m) (fun v => v=bank (produced (base s rows B hs rs bs x) s))
      (fun v => v=bank (dimensions (base s rows B hs rs bs x) s rows)) (cost s rows) := by
  exact (((power_runs s rows B hs rs bs x hv hc).seq (width_runs s rows B hs rs bs x hv hc)).seq
    (product_runs s rows B hs rs bs x hr cr)).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlLoadHeaders
