import IntegerMultBounds.Machine.ActivePrefixCorrectionOffsetRun

/-! Complete original-descriptor correction producer: every current prefix
supplies its own source controls and temporary, all arithmetic is rowwise,
and every intermediate table/header is physically erased. -/
namespace IntegerMultBounds.Machine.ActivePrefixCorrectionOffset
noncomputable section
open ActivePrefixSelectedOffsetBank (Shape values)
variable {a : ℕ}

def input (hs : Fin 8 → List Bool) := ActivePrefixCorrectionOffsetRun.bank
  (ActivePrefixCorrectionOffsetBank.base (a := a) hs)
def output (s : Shape) (hs : Fin 8 → List Bool) := ActivePrefixCorrectionOffsetRun.bank
  (ActivePrefixCorrectionOffsetBank.output (a := a) s hs)
def program := ActivePrefixCorrectionOffsetRun.program (a := a)
def constant := ActivePrefixSelectedOffset.constant+ActivePrefixControlOffset.constant+
  ActivePrefixOffsetHeadersBudget.constant+208

theorem cost_bound (s : Shape) : ActivePrefixCorrectionOffsetRun.cost s≤constant*(2^s.W*(s.W+1)) := by
  have hsource : s.f*s.q≤s.W := by have := s.sourceFits; omega
  have htemp : s.n*s.b≤s.W := by have := s.tempFits; omega
  have hq : 1≤s.q := by have := s.hb; have := s.hbq; omega
  have hnq : s.n*s.q≤s.W := by
    have hnf := s.hnf
    have hmul := Nat.mul_le_mul_right s.q (show s.n≤s.f by omega)
    omega
  have hsub := Nat.mul_le_mul_left (2^s.W) (Nat.add_le_add_right hnq 1)
  have hclean := ActivePrefixOffsetHeadersCleanup.derived_cost s.W s.q s.b s.n s.f hq s.hnf hsource htemp
  have hvol := ActivePrefixOffsetHeadersBudget.volume_pos s.W
  unfold ActivePrefixOffsetHeadersBudget.volume at hclean hvol
  unfold ActivePrefixCorrectionOffsetRun.cost constant
  nlinarith

theorem runs_linear (s : Shape) (hs : Fin 8 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun v => v=input hs) (fun v => v=output s hs)
      (constant*(2^s.W*(s.W+1))) :=
  (ActivePrefixCorrectionOffsetRun.runs s hs hv hc).consequence (fun _ h => h) (fun _ h => h) (cost_bound s)

end
end IntegerMultBounds.Machine.ActivePrefixCorrectionOffset
