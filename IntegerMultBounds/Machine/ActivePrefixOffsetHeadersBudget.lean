import IntegerMultBounds.Machine.ActivePrefixOffsetHeadersRun

/-! Degree-one full-prefix bound for actual descriptor synthesis. Both field
fit hypotheses remain explicit; the n*P product is charged, never supplied. -/
namespace IntegerMultBounds.Machine.ActivePrefixOffsetHeadersBudget
noncomputable section
open ActivePrefixOffsetHeadersData
open CompactGadgetReservationHeadersCore (bank)
variable {a t : ℕ}

def volume (W : ℕ) := 2^W*(W+1)
def constant := FixedBasePowerDescriptor.constant 2+328

theorem volume_pos (W : ℕ) : 0<volume W := by unfold volume; positivity

theorem values_le (W q b n f : ℕ) (hq : 1≤q) (hnf : n+1=f)
    (hsource : f*q≤W) (htemp : n*b≤W) : ∀ i, values W q b n f i≤volume W := by
  have hP : 2^W≤volume W := Nat.le_mul_of_pos_right _ (by omega)
  have hW : W≤volume W := (by omega : W≤W+1).trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hnq : n*q≤W := (Nat.mul_le_mul_right q (by omega : n≤f)).trans hsource
  have hn : n≤W := (Nat.le_mul_of_pos_right _ hq).trans hnq
  have hnP : n*2^W≤volume W := by
    simpa only [volume,Nat.mul_comm] using Nat.mul_le_mul_right (2^W) (by omega : n≤W+1)
  intro i
  fin_cases i <;> simp only [values]
  · exact hP
  · exact hsource.trans hW
  · exact htemp.trans hW
  · exact hnP
  · exact hnq.trans hW

theorem cost_bound (W q b n f : ℕ) (hq : 1≤q) (hnf : n+1=f)
    (hsource : f*q≤W) (htemp : n*b≤W) :
    ActivePrefixOffsetHeadersRun.cost W q b n f ≤ constant*volume W := by
  have h0 := values_le W q b n f hq hnf hsource htemp 0
  have h1 := values_le W q b n f hq hnf hsource htemp 1
  have h2 := values_le W q b n f hq hnf hsource htemp 2
  have h3 := values_le W q b n f hq hnf hsource htemp 3
  have h4 := values_le W q b n f hq hnf hsource htemp 4
  change 2^W≤volume W at h0
  change f*q≤volume W at h1
  change n*b≤volume W at h2
  change n*2^W≤volume W at h3
  change n*q≤volume W at h4
  have hA := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) h0
  have hV := volume_pos W
  unfold ActivePrefixOffsetHeadersRun.cost constant
  nlinarith

theorem constructs (caller : Tapes t a) (focus : Fin 10 → Fin t) (hf : Function.Injective focus)
    (hs : Fin 5 → List Bool) (W q b n f : ℕ)
    (hsrc : SharedBank.payload caller focus=sources hs)
    (hv : ∀ i, Counter.value (hs i)=originalValues W q b n f i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hb : 1≤b) (hbq : b+1≤q) (hnf : n+1=f) (hsource : f*q≤W) (htemp : n*b≤W) :
    HoareTime (ActivePrefixOffsetHeadersRun.program (a := a) focus hf) (fun v => v=bank caller)
      (fun v => v=bank (result caller focus W q b n f)) (constant*volume W) :=
  (ActivePrefixOffsetHeadersRun.constructs caller focus hf hs W q b n f hsrc hv hc (by omega) hb).consequence
    (fun _ h => h) (fun _ h => h) (cost_bound W q b n f (by omega) hnf hsource htemp)

end
end IntegerMultBounds.Machine.ActivePrefixOffsetHeadersBudget
