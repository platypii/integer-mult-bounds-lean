module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCouplingCoefficientInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedPrepareCouplingIntervalPacket
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCouplingPageCounts
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFinishCouplingCoefficientInterval
public import IntegerMultBounds.MathlibTM2.Host.Embed
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCouplingGuard

/-! Keep binary guard metadata outside the legacy solver bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.NLogN.PhaseCellRationalArgs IntegerMultBounds.MathlibTM2.Fast

def binaryLengthCouplingCoefficientInterval {P U : Type} {Q A : ℕ} : Pr P 168 Q A U :=
  .seq (toUnary 165 166 0 1 2) (.seq preparedCouplingCoefficientInterval (uclear 166))

theorem binaryLengthCouplingCoefficientInterval_exec {P U : Type} {Q A V precision q w s t u band a b origin N : ℕ} [NeZero s]
    {body : P → Pr P 168 Q A U} (value : Fin 117 → ℕ)
    (hs : value 97 = s) (ht : value 98 = t) (hband : value 100 = 2*band)
    (ha : value 101 = a) (hb : value 103 = b) (hi : value 107 = origin)
    (hc : value 108 = origin+N) (hfit : origin+N ≤ s)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V)
    (hbound : ∀ i, value (intervalGuardBankSource i) < 2^V)
    (v : HS 168 Q A U) (S : Stacks 168 A) (hV : ((embStk intervalGuardPlacement S).R 115).length = V)
    (hmeta : ∀ i, (embStk intervalGuardPlacement S).R (intervalGuardBankSource i) = binSyms V (value (intervalGuardBankSource i)))
    (hblank : ∀ r, (embStk intervalGuardPlacement S).R (intervalGuardReg r) = [])
    (hA : 4 ≤ A) (hprecision : 13 ≤ precision) (raw : List (Fin (A+4)))
    (hready : CouplingReady precision q w s t u band a b raw (embStk groupReg (embStk intervalPageReg S)))
    (h140 : S.R 140 = []) (h143 : S.R 143 = []) (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = [])
    (h135 : S.R 135 = []) (hindex : (S.R 107).length = origin) (horigin : origin < s)
    (h139 : S.R 139 = []) :
    let xs := couplingCoefficientPageInterval precision q s t u band a b origin N
    ∃ v' m, v'.user = v.user ∧
      m ≤ 8*N+11*V+8+(buildMarkedRowCoefficientPacketCost precision q w s t u band origin+(prepareCouplingPageCountsCost N band+(144*V+145+((46*N+2)*tblC V 1+66*V+2*N+70)+
        couplingCoefficientPageIntervalLoopCost precision q w s t u band a b origin N+
        transferCountedLineCost xs.length w+24*liftedCoefficientWidth precision q w s t u band+4))) ∧
      Exec body binaryLengthCouplingCoefficientInterval (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update S.R 140 (List.replicate (2*band+1) tick))
          135 []) 138 (cstream A w xs++S.R 138)) 139 (List.replicate xs.length tick)) 143 [])}) := by
  dsimp only
  have hNV : N < 2^V := by nlinarith [Nat.zero_le (t*t)]
  have hsmall (r : Fin 168) (hr : r.val < 3) : S.R r = [] := by
    let k : Fin 117 := ⟨r.val,by omega⟩
    have hk := hready.low k (by dsimp [k]; omega)
    simpa [embStk,groupReg,intervalPageReg,k] using hk
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := toUnary_exec_linear (body := body)
    (a := 165) (z := 166) (w := 0) (t := 1) (t₂ := 2) (by decide) hNV v S h165
    (hsmall 0 (by decide)) (hsmall 1 (by decide)) (hsmall 2 (by decide))
  let B : Stacks 168 A := {S with R := Function.update S.R 166 (List.replicate N tick)}
  have he₁' : Exec body (toUnary 165 166 0 1 2) (mk v S) m₁ (mk v₁ B) := by
    simpa only [h166,List.append_nil] using he₁
  have hreadyB : CouplingReady precision q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg B)) := by
    rw [show embStk groupReg (embStk intervalPageReg B) =
      embStk groupReg (embStk intervalPageReg S) from intervalPageCore_updateR S 166 (by decide) _]
    exact hready
  have hf (r : Fin 117) : intervalGuardPlacement r ≠ 166 := by
    have hr := r.isLt
    simp only [intervalGuardPlacement]; split_ifs <;> simp_all [ne_eq,Fin.ext_iff] <;> omega
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := preparedCouplingCoefficientInterval_exec (body := body) value
    hs ht hband ha hb hi hc hfit hs0 hst haS hbS hwide hbound v₁ B
    (by simpa only [B,embStk,Function.comp_def,Function.update_of_ne (hf 115)] using hV)
    (by intro i; simpa only [B,embStk,Function.comp_def,Function.update_of_ne (hf _)] using hmeta i)
    (by intro r; simpa only [B,embStk,Function.comp_def,Function.update_of_ne (hf _)] using hblank r)
    hA hprecision raw hreadyB (by simpa [B] using h140) (by simpa [B] using h143)
    (by simp [B]) (by simpa [B] using h135) (by simpa [B] using hindex) horigin
    (by simpa [B] using h139)
  let xs := couplingCoefficientPageInterval precision q s t u band a b origin N
  let F : Stacks 168 A := {B with R := (Function.update (Function.update (Function.update (Function.update (Function.update B.R
    140 (List.replicate (2*band+1) tick)) 135 []) 138 (cstream A w xs++B.R 138))
    139 (List.replicate xs.length tick)) 143 [])}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 166 v₂ F
  have hlen : (F.R 166).length = N := by simp [F,B]
  refine ⟨v₃,m₁+(m₂+(2*N+2)),hu₃.trans (hu₂.trans hu₁),by omega,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hlen]) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases h1 : r = 166 <;> by_cases h2 : r = 135 <;> by_cases h3 : r = 138 <;>
    by_cases h4 : r = 139 <;> by_cases h5 : r = 140 <;> by_cases h6 : r = 143 <;>
    simp [F,B,xs,h1,h2,h3,h4,h5,h6,h166]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
