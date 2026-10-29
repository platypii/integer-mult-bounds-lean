module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedCouplingCoefficientInterval
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

def preparedCouplingCoefficientInterval {P U : Type} {Q A : ℕ} : Pr P 168 Q A U :=
  .seq placedPrepareCouplingIntervalPacket countedCouplingCoefficientInterval

theorem preparedCouplingCoefficientInterval_exec {P U : Type} {Q A V precision q w s t u band a b origin N : ℕ} [NeZero s]
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
    (h140 : S.R 140 = []) (h143 : S.R 143 = []) (hN : (S.R 166).length = N)
    (h135 : S.R 135 = []) (hindex : (S.R 107).length = origin) (horigin : origin < s)
    (h139 : S.R 139 = []) :
    let xs := couplingCoefficientPageInterval precision q s t u band a b origin N
    ∃ v' m, v'.user = v.user ∧
      m ≤ buildMarkedRowCoefficientPacketCost precision q w s t u band origin+(prepareCouplingPageCountsCost N band+(144*V+145+((46*N+2)*tblC V 1+66*V+2*N+70)+
        couplingCoefficientPageIntervalLoopCost precision q w s t u band a b origin N+
        transferCountedLineCost xs.length w+24*liftedCoefficientWidth precision q w s t u band+4)) ∧
      Exec body preparedCouplingCoefficientInterval (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update S.R 140 (List.replicate (2*band+1) tick))
          135 []) 138 (cstream A w xs++S.R 138)) 139 (List.replicate xs.length tick)) 143 [])}) := by
  dsimp only
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := placedPrepareCouplingIntervalPacket_exec (body := body)
    hprecision horigin raw v S hready hindex
  let B : Stacks 168 A := {S with R := (Function.update S.R 135
    (markedRowCoefficientPacket A (liftedCoefficientWidth precision q w s t u band)
      precision q s t u band origin++S.R 135))}
  have hf (r : Fin 168) (hr : r ≠ 135) : B.R r = S.R r := by simp [B,hr]
  have hreadyB : CouplingReady precision q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg B)) := by
    rw [show embStk groupReg (embStk intervalPageReg B) =
      embStk groupReg (embStk intervalPageReg S) from intervalPageCore_updateR S 135 (by decide) _]
    exact hready
  have hmf (i : Fin 17) : B.R (intervalGuardPlacement (intervalGuardBankSource i)) =
      S.R (intervalGuardPlacement (intervalGuardBankSource i)) := by
    apply hf
    simp only [intervalGuardBankSource]; split_ifs <;> decide
  have hbf (r : TblR 17) : B.R (intervalGuardPlacement (intervalGuardReg r)) =
      S.R (intervalGuardPlacement (intervalGuardReg r)) := by
    apply hf
    have hr := intervalGuardReg_range r
    have hne : intervalGuardReg r ≠ 109 := by
      intro he; have hv := congrArg (fun k : Fin 117 => k.val) he; norm_num at hv; omega
    have hlow : (intervalGuardReg r).val < 96 := by omega
    intro he
    have hv := congrArg (fun k : Fin 168 => k.val) he
    simp [intervalGuardPlacement,hne,hlow] at hv
    omega
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := countedCouplingCoefficientInterval_exec (body := body) value
    hs ht hband ha hb hi hc hfit hs0 hst haS hbS hwide hbound v₁ B
    (by simpa [B,embStk,intervalGuardPlacement] using hV)
    (by intro i; change B.R _ = _; rw [hmf]; exact hmeta i)
    (by intro r; change B.R _ = _; rw [hbf]; exact hblank r)
    hA hprecision raw hreadyB (by simpa [B] using h140) (by simpa [B] using h143)
    (by simpa [B] using hN) (by simp [B,h135]) (by simpa [B] using h139)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,by omega,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases h1 : r = 135 <;> by_cases h2 : r = 138 <;> by_cases h3 : r = 139 <;>
    by_cases h4 : r = 140 <;> by_cases h5 : r = 143 <;> simp [B,h1,h2,h3,h4,h5]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
