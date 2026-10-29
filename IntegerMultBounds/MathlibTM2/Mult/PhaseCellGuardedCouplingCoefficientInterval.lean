module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedBinaryRecoveryGuardInterval
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

def guardedCouplingCoefficientInterval {P U : Type} {Q A : ℕ} : Pr P 168 Q A U :=
  .seq (placedBinaryRecoveryGuardInterval true) placedFinishCouplingCoefficientInterval

theorem guardedCouplingCoefficientInterval_exec {P U : Type} {Q A V precision q w s t u band a b origin N : ℕ} [NeZero s]
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
    (hrows : (S.R 140).length = 2*band+1) (hcount : (S.R 143).length = N)
    (hpacket : S.R 135 = markedRowCoefficientPacket A
      (liftedCoefficientWidth precision q w s t u band) precision q s t u band origin)
    (h139 : S.R 139 = []) :
    let xs := couplingCoefficientPageInterval precision q s t u band a b origin N
    ∃ v' m, v'.user = v.user ∧
      m ≤ 144*V+145+((46*N+2)*tblC V 1+66*V+2*N+70)+
        couplingCoefficientPageIntervalLoopCost precision q w s t u band a b origin N+
        transferCountedLineCost xs.length w+24*liftedCoefficientWidth precision q w s t u band+4 ∧
      Exec body guardedCouplingCoefficientInterval (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          135 []) 138 (cstream A w xs++S.R 138)) 139 (List.replicate xs.length tick)) 143 [])}) := by
  dsimp only
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := placedBinaryRecoveryGuardInterval_exec (body := body) true value
    hs ht hband ha hb hi hc hfit hs0 hst haS hbS (by omega) hbound v S hV hmeta hblank
  let G : Stacks 168 A := {S with R := (Function.update S.R 136
    (recoveryGuardIntervalSymbols true A s t (2*band) a b origin N++S.R 136))}
  have hreadyG : CouplingReady precision q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg G)) := by
    have heq : embStk groupReg (embStk intervalPageReg G) =
        embStk groupReg (embStk intervalPageReg S) := by
      refine Stacks.ext rfl rfl rfl ?_
      funext r
      have hr : intervalPageReg (groupReg r) ≠ 136 := by
        have hi := r.isLt
        simp only [intervalPageReg,groupReg,ne_eq,Fin.ext_iff]; omega
      simp only [embStk,Function.comp_def,G,Function.update_of_ne hr]
    rw [heq]; exact hready
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := placedFinishCouplingCoefficientInterval_exec (body := body)
    hA hst hprecision hfit raw (S.R 136) v₁ G hreadyG
    (by simpa [G] using hrows) (by simpa [G] using hcount)
    (by simpa [G] using hpacket) (by simpa [G] using h139)
    (by simp only [G,Function.update_self,recoveryGuardIntervalSymbols_coupling _ _ _ _ _ _ _ _ hfit])
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,by omega,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases h135 : r = 135 <;> by_cases h136 : r = 136 <;>
    by_cases h138 : r = 138 <;> by_cases h139 : r = 139 <;> by_cases h143 : r = 143 <;>
    simp [G,h135,h136,h138,h139,h143]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
