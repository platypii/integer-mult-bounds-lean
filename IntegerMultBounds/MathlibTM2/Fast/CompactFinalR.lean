module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainChainEntryR
import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedTransformMatchR
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainHost
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainInputDistribution
import IntegerMultBounds.MathlibTM2.Fast.CompactMainDistributionCalls
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedDistributionEntry
import IntegerMultBounds.MathlibTM2.Fast.CompactMainParamCalls
import IntegerMultBounds.MathlibTM2.Fast.CompactMainDispatch
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The complete compact multiplier with the rounded synthetic transforms: input and
distribution under the rounded procedure table, the rounded chain and the carry output. The
time bound needs only the cost bound of the rounded transforms. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.MathlibTM2.Fast.TableVM Filter
open IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Fast.ChirpSt
open Computability
open IntegerMultBounds.MathlibTM2.Cost
noncomputable section

/-- Input preparation executes from the true empty expanded machine; distribution
supplies the actual retuned wires, stage file, and stable chain precondition. -/
theorem compactMainInputDistR_exec_eventually
    (hP : ∀ (R : Regs mnT bdA) (n : ℕ),MnPostParam R n → BdPostParam R n) :
    ∀ᶠ N : ℕ in atTop, ∀ (main : CompactMnPr CompactMainProc bdA) (x y : ℕ),
      (pairEnc (x,y)).length=N →
      ∃ (v : HS compactMnT compactMnQ bdA Unit) (S : Stacks compactMnT bdA) (m : ℕ),
        m≤8*N+14+pmCost N mnUs+(compactBdDist hP).cost N+1 ∧
        Exec (compactMainEntryTableR main) (compactMainInputDist hP)
          (Store.only compactMainV₀ .inp (pairEnc (x,y))) m (mk v S) ∧
        S.inp=[] ∧ S.out=[] ∧ compactMainStablePre N S ∧
        MnDistOut (embStk compactMnLegacyReg S).R N (dsW N) (bdE N)
          (mnσ (blP₀ dsW N) (compactDsyV₀ N)) ∧
        MnMid (embStk compactMnLegacyReg S) x y N := by
  filter_upwards [compactBdDist_entry_eventually hP,Mult.Sizes.eventually_big] with N hdist hN
  intro main x y hlen
  let old : MnPr bdA := .act .done
  obtain ⟨v₁,S₁,m₁,hm₁,he₁,hfront⟩ := mn_front_exec (body := mnBody mnLb old) (A := bdA) x y
  rw [hlen] at hm₁ hfront
  have hA : 4≤bdA := by
    exact (by omega : 4≤96).trans mnKa_alpha
  obtain ⟨v₂,S₂,m₂,hm₂,he₂,hin₂,hout₂,hL₂,hι₂,hpost,hmid₂⟩ :=
    mn_params_exec hN hA v₁ S₁ hfront
  obtain ⟨v₃,S₃,m₃,hm₃,he₃,hin₃,hout₃,hL₃,hfields,hmid₃,hentry⟩ :=
    hdist old x y v₂ S₂ hL₂ hι₂ hpost hmid₂
  have he := (he₁.seq he₂).seq he₃
  have hstart : mk mnV₀ (mnIn (A := bdA) (pairEnc (x,y)))=
      mk (compactMainStateDown compactMainV₀)
        (embStk compactMnLegacyReg (compactMainIn (pairEnc (x,y)))) := by
    rw [compactMainV₀_projection]
    rfl
  rw [hstart] at he
  obtain ⟨v,hv,hu,hex⟩ := compactMainStage_exec (mnBody mnLb old)
    (compactMainNativeTableR Cost.brDirs) compactMainV₀ (compactMainIn (pairEnc (x,y))) he
  have hcall : callsWithin (fun g => g≠compactMainOldProc .main) (compactMainInputDist hP) := by
    unfold compactMainInputDist
    rw [compactMainStage,statePlacedNormalized,callsWithin_embProg_iff]
    refine ⟨True.intro,?_⟩
    rw [callsWithin_stateLiftPr_iff]
    have hd := compactMainDistribution_calls hP
    rw [compactMainStage,statePlacedNormalized,callsWithin_embProg_iff] at hd
    simp only [callsWithin] at hd
    rw [callsWithin_stateLiftPr_iff] at hd
    have hp := compactMainParams_calls (A := bdA)
    rw [compactMainStage,statePlacedNormalized,callsWithin_embProg_iff] at hp
    simp only [callsWithin] at hp
    rw [callsWithin_stateLiftPr_iff] at hp
    exact ⟨⟨by trivial,hp.2⟩,hd.2⟩
  have hex' := compactMainEntryR_exec main old hex hcall
  rw [←compactMain_only_inp] at hex'
  refine ⟨v,compactMainFinalStacks S₃ (compactMainIn (pairEnc (x,y))),1+(m₁+m₂+m₃),
    by omega,hex',?_,?_,?_,?_,?_⟩
  · exact (compactMainFinalStacks_io _ _).1.trans (hin₃.trans hin₂)
  · exact (compactMainFinalStacks_io _ _).2.trans (hout₃.trans hout₂)
  · exact compactMainStablePre_of_mid (hentry _ (fun _ => rfl) (fun _ => rfl))
  · rw [compactMainFinalStacks_projection]
    exact hfields
  · rw [compactMainFinalStacks_projection]
    exact hmid₃

/-- The full cost envelope with the rounded transforms. -/
def compactRetunedTimeR (c extra n : ℕ) : ℕ :=
  compactMainTime compactRetunedDist
    (fun n => compactMainRuns compactRetunedDist compactRetunedCFR compactRetunedCOR n + extra)
    compactMnT c n

def compactCompletedTableR (p : CompactMnPr CompactMainProc (prime+mnKa)) :=
  compactMainEntryTableR (compactCompletedMain p)

/-- One finite constant bounds pushes in both the prefix and every procedure body. -/
def compactCompletedPushR (p : CompactMnPr CompactMainProc (prime+mnKa)) : ℕ :=
  max (mnProgPush p) (mnPushC (compactCompletedTableR p))

def compactRetunedPreTimeR (extra n : ℕ) : ℕ :=
  compactMainPreCost compactRetunedDist
    (fun n => compactMainRuns compactRetunedDist compactRetunedCFR compactRetunedCOR n + extra) n

/-- A prefix with exact output and cleared left stacks gives the clean host contract. -/
theorem compactCompletedR_hostMul
    (p : CompactMnPr CompactMainProc (prime+mnKa)) (extra x y : ℕ)
    {m : ℕ} {v : HS compactMnT compactMnQ (prime+mnKa) Unit}
    {S : Stacks compactMnT (prime+mnKa)}
    (he : Exec (compactCompletedTableR p) p
      (Store.only compactMainV₀ .inp (pairEnc (x,y))) m (mk v S))
    (hm : m ≤ compactRetunedPreTimeR extra (pairEnc (x,y)).length)
    (hi : S.inp=[]) (ho : S.out=encodingNatBool.encode (x*y)) (hL : ∀ k,S.L k=[]) :
    HostMulWithin (compactCompletedTableR p) (compactMainOldProc .main) compactMainV₀
      (compactRetunedTimeR (compactCompletedPushR p) extra) x y := by
  have hp : mnProgPush p ≤ compactCompletedPushR p := le_max_left _ _
  have hb : ∀ f,mnProgPush (compactCompletedTableR p f) ≤ compactCompletedPushR p :=
    fun f => (mn_progPush_le_pushC (compactCompletedTableR p) f).trans (le_max_right _ _)
  obtain ⟨m',hm',he'⟩ := compactMain_finish (compactCompletedTableR p) hb p hp
    (pairEnc (x,y)) (encodingNatBool.encode (x*y)) he hi ho hL
  refine ⟨m',?_,he'⟩
  change m'+2 ≤ compactRetunedPreTimeR extra (pairEnc (x,y)).length +
    2*((pairEnc (x,y)).length+compactCompletedPushR p*compactRetunedPreTimeR extra (pairEnc (x,y)).length)+
    2*compactMnT+4
  have hc := Nat.mul_le_mul_left (compactCompletedPushR p) hm
  omega

/-- The only remaining obligation is the actual arithmetic prefix execution. -/
theorem compactCompletedR_mulInTime
    (hcost : ∃ C : ℝ, ∀ᶠ n in atTop,
      ((compactRetunedCFR n + compactRetunedCOR n : ℕ) : ℝ) ≤ C * CompactTotal.conv n)
    (p : CompactMnPr CompactMainProc (prime+mnKa)) (extra : ℕ)
    (hexec : ∀ᶠ n in atTop, ∀ x y, (pairEnc (x,y)).length=n →
      ∃ m v S, m ≤ compactRetunedPreTimeR extra n ∧
        Exec (compactCompletedTableR p) p (Store.only compactMainV₀ .inp (pairEnc (x,y))) m (mk v S) ∧
        S.inp=[] ∧ S.out=encodingNatBool.encode (x*y) ∧ ∀ k,S.L k=[]) :
    MulInTime (4223103985/2^46:ℝ) := by
  obtain ⟨Cs, hCs⟩ := hcost
  apply compactMulInTime_of_main_exec (compactCompletedTableR p) (compactMainOldProc .main)
    compactMainV₀ compactRetunedDist compactRetunedCFR compactRetunedCOR (compactCompletedPushR p)
    extra hCs
  filter_upwards [hexec] with n hn x y hxy
  obtain ⟨m,v,S,hm,he,hi,ho,hL⟩ := hn x y hxy
  exact compactCompletedR_hostMul p extra x y he (hxy ▸ hm) hi ho hL


/-- Prefix costs include all primitive stages and the actual expanded source runs. -/
theorem compactRetunedPreTimeR_eq (extra n : ℕ) :
    compactRetunedPreTimeR extra n =
      8*n+14+pmCost n mnUs+compactRetunedDist.cost n +
      mnChainCost n (dsW n) (compactMainRuns compactRetunedDist compactRetunedCFR compactRetunedCOR n) +
      carryOutCost (mnWo n) (b n) (S n) + extra := by
  unfold compactRetunedPreTimeR compactMainPreCost mnChainCost mnTail
  change (4*n+6)+(4*n+8)+pmCost n mnUs+compactRetunedDist.cost n+
      2*digitCost (b n) (p n) (dsW n) (S n)+
      (compactMainRuns compactRetunedDist compactRetunedCFR compactRetunedCOR n+extra)+
      mnGlue n (dsW n)+_ = _
  simp only [bdW]
  omega

/-- The sixteen-step allowance covers the combined input wrapper and twelve chain wrappers. -/
theorem compactRetunedR_prefix_cost_le {n a z : ℕ}
    (ha : a ≤ 8*n+14+pmCost n mnUs+compactRetunedDist.cost n+1)
    (hz : z ≤ mnChainCost n (dsW n)
      (compactMainRuns compactRetunedDist compactRetunedCFR compactRetunedCOR n)+12) :
    a+z+carryOutCost (mnWo n) (b n) (S n) ≤ compactRetunedPreTimeR 16 n := by
  rw [compactRetunedPreTimeR_eq]
  omega

/-- Input, retuned distribution, complete arithmetic chain and canonical output. -/
def compactRetunedPrefixR : CompactMnPr CompactMainProc (prime+mnKa) :=
  .seq (compactMainInputDist mn_postParam_bd) (.seq compactMainChainR compactMainOutput)

/-- Exact multiplication prefix on all sufficiently long input pairs. -/
theorem compactRetunedPrefixR_exec : ∀ᶠ n in atTop, ∀ x y, (pairEnc (x,y)).length=n →
    ∃ m v S, m ≤ compactRetunedPreTimeR 16 n ∧
      Exec (compactCompletedTableR compactRetunedPrefixR) compactRetunedPrefixR
        (Store.only compactMainV₀ .inp (pairEnc (x,y))) m (mk v S) ∧
      S.inp=[] ∧ S.out=encodingNatBool.encode (x*y) ∧ ∀ k,S.L k=[] := by
  filter_upwards [compactMainInputDistR_exec_eventually mn_postParam_bd,
    compactRetunedChainR_entry_eventually,compactMainOutputG_exec_eventually]
    with n hinput hchain houtput
  intro x y hxy
  have hlen := length_pairEnc x y
  have hsx : Nat.size x≤n := by omega
  have hsy : Nat.size y≤n := by omega
  let main := compactCompletedMain compactRetunedPrefixR
  obtain ⟨v₁,S₁,m₁,hm₁,he₁,hi₁,ho₁,hs₁,hd₁,hmiddle⟩ := hinput main x y hxy
  obtain ⟨v₂,S₂,m₂,hm₂,he₂,hi₂,ho₂,hL₂,⟨cb,hcb,hdat⟩,hframe⟩ :=
    hchain main x y hsx hsy v₁ S₁ hs₁ hd₁ hmiddle
  obtain ⟨v₃,S₃,he₃,hi₃,ho₃,hL₃⟩ :=
    houtput (compactCompletedTableR compactRetunedPrefixR) x y hsx hsy S₁ hd₁ hmiddle v₂ S₂ cb hcb hdat hframe
  refine ⟨_,v₃,S₃,?_,he₁.seq (he₂.seq he₃),hi₃.trans (hi₂.trans hi₁),?_,?_⟩
  · have h := compactRetunedR_prefix_cost_le hm₁ hm₂
    simpa only [Nat.add_assoc] using h
  · rw [ho₃,ho₂,ho₁,List.append_nil]
  · intro k
    rw [hL₃,hL₂]
    exact hs₁.1 k

/-- **The rounded compact multiplier.** One fixed finite Mathlib machine with the rounded
synthetic transforms multiplies every pair in worst-case time `O(n (log n)^(1-κ))`, given the
cost bound of the rounded transforms. -/
theorem compactR_mulInTime
    (hcost : ∃ C : ℝ, ∀ᶠ n in atTop,
      ((compactRetunedCFR n + compactRetunedCOR n : ℕ) : ℝ) ≤ C * CompactTotal.conv n) :
    MulInTime (4223103985/2^46:ℝ) :=
  compactCompletedR_mulInTime hcost compactRetunedPrefixR 16 compactRetunedPrefixR_exec

/-- **The rounded compact multiplier**, with no remaining hypothesis: one fixed finite Mathlib
machine with the rounded synthetic transforms multiplies every pair in worst-case time
`O(n (log n)^(1-κ))`. -/
theorem compactR_mulInTime_final : MulInTime (4223103985/2^46:ℝ) :=
  compactR_mulInTime compactRetunedR_transform_cost_le

end
end IntegerMultBounds.MathlibTM2.Fast.Main
