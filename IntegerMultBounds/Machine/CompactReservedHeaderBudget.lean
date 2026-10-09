import IntegerMultBounds.Machine.CompactReservedRoundtrip

/-! Uniform charged budgets for the actual reservation synthesis and lifecycle.
The quotient routines are bounded by their proved descriptor runtimes. -/
namespace IntegerMultBounds.Machine.CompactReservedHeaderBudget
noncomputable section
open CompactReservedHeaders
open CompactGlobalRowPadding (rowAxes)
open RecursiveChildQuotientsConstant (bits)

def scalar (c m D K d G : ℕ) := D+K+d+d*G+rowAxes c m d+1

theorem division_cost (x y S : ℕ) (hS : 0<S) (hx : x≤3*S) (hy : y≤3*S) :
    BinaryDescriptorDivision.cost (bits x) (bits y)≤100000*S^2 := by
  have hx' := ActiveRepairRankHeadersCommands.bits_length x
  have hy' := ActiveRepairRankHeadersCommands.bits_length y
  have hb := BinaryDescriptorDivision.cost_le (bits x) (bits y)
  have hxl : (bits x).length≤4*S := by omega
  have hyl : (bits y).length≤4*S := by omega
  have hin : 4*(bits x).length+6*(bits y).length+30≤70*S := by omega
  have hm := Nat.mul_le_mul hxl hin
  nlinarith

theorem row_cost (c m D K rho ell q d G : ℕ) :
    CompactGlobalRowHeaderOps.scheduleCost (rowOps c m) (initial D K rho ell q d G)=
      RecursiveChildQuotientsConstant.cost (Nat.clog 2 c)+500*d+
      CompactGlobalRowHeaderPrimitives.logConstant m*(2*d)+53*rowAxes c m d+
      100*Nat.clog 2 c+100*Nat.clog m (2*d)+536 := by
  simp [rowOps,CompactGlobalRowHeaderOps.scheduleCost,CompactGlobalRowHeaderOps.cost,
    CompactGlobalRowHeaderOps.eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,initial,Function.update,rowAxes]
  rw [show d+d=2*d by omega]
  ring

theorem count_cost (c m D K rho ell q d G : ℕ) :
    CompactChildHeadersArithmetic.scheduleCost countOps (rowState c m D K rho ell q d G)≤
      210000*(scalar c m D K d G)^2 := by
  let S := scalar c m D K d G
  have hS : 0<S := by dsimp [S,scalar]; omega
  have hD : D≤S := by dsimp [S,scalar]; omega
  have hK : K≤S := by dsimp [S,scalar]; omega
  have hp : d*G≤S := by dsimp [S,scalar]; omega
  have hr : rowAxes c m d≤S := by dsimp [S,scalar]; omega
  have hs : K-1≤S := (Nat.sub_le _ _).trans hK
  have hn : d*G+(K-1)≤3*S := by omega
  have hn' : d*G+d*G+(K-1)≤3*S := by omega
  have hq : (d*G+d*G+(K-1))/K≤3*S := (Nat.div_le_self _ _).trans hn'
  have hd0 := division_cost (d*G+(K-1)) K S hS hn (by omega)
  have hd1 := division_cost (d*G+d*G+(K-1)) K S hS hn' (by omega)
  simp [countOps,CompactChildHeadersArithmetic.scheduleCost,CompactChildHeadersArithmetic.cost,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,initial,rowState,Function.update,Nat.mul_comm G d]
  change _≤210000*S^2
  have hc : RecursiveChildQuotientsConstant.cost 1=9 := by decide
  rw [hc]
  nlinarith

theorem scratch_cost (c m D K rho ell q d G : ℕ) :
    CompactChildHeadersArithmetic.scheduleCost eraseScratch (counts c m D K rho ell q d G)≤
      10000*(scalar c m D K d G)^2 := by
  let S := scalar c m D K d G
  have hS : 0<S := by dsimp [S,scalar]; omega
  have hp : d*G≤S := by dsimp [S,scalar]; omega
  have hK : K≤S := by dsimp [S,scalar]; omega
  have hr : rowAxes c m d≤S := by dsimp [S,scalar]; omega
  have hs : K-1≤S := (Nat.sub_le _ _).trans hK
  have hn : d*G+d*G+(K-1)≤3*S := by omega
  have hq : (d*G+d*G+(K-1))/K≤3*S := (Nat.div_le_self _ _).trans hn
  simp [eraseScratch,counts,countOps,CompactChildHeadersArithmetic.scheduleCost,CompactChildHeadersArithmetic.cost,
    CompactChildHeadersArithmetic.execute,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.cost,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,initial,rowState,Function.update,Nat.mul_comm G d]
  change _≤10000*S^2
  nlinarith

def constant (c m : ℕ) := RecursiveChildQuotientsConstant.cost (Nat.clog 2 c)+
  100*Nat.clog 2 c+2*CompactGlobalRowHeaderPrimitives.logConstant m+230000

theorem setup_cost (c m D K rho ell q d G : ℕ) (hc : 2≤c) :
    CompactReservedHeaders.cost c m D K rho ell q d G≤constant c m*(scalar c m D K d G)^2 := by
  have h0 := row_cost c m D K rho ell q d G
  have h1 := count_cost c m D K rho ell q d G
  have h2 := scratch_cost c m D K rho ell q d G
  have hlog : Nat.clog m (2*d)≤rowAxes c m d :=
    Nat.le_mul_of_pos_left _ (CompactGlobalRowHeaders.logc_positive c hc)
  have hd : d≤scalar c m D K d G := by unfold scalar; omega
  have hr : rowAxes c m d≤scalar c m D K d G := by unfold scalar; omega
  have hS : 0<scalar c m D K d G := by unfold scalar; omega
  have hdS : d≤(scalar c m D K d G)^2 := by nlinarith
  have hm := Nat.mul_le_mul_left (2*CompactGlobalRowHeaderPrimitives.logConstant m) hdS
  have hconst := Nat.mul_le_mul_left (RecursiveChildQuotientsConstant.cost (Nat.clog 2 c)+100*Nat.clog 2 c)
    (show 1≤(scalar c m D K d G)^2 by nlinarith)
  unfold CompactReservedHeaders.cost constant
  nlinarith

end
end IntegerMultBounds.Machine.CompactReservedHeaderBudget
