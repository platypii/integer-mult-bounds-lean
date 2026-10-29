module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryRecoveryGuardInterval
public import IntegerMultBounds.MathlibTM2.Host.Embed
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCouplingGuard

/-! Keep binary guard metadata outside the legacy solver bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

def intervalGuardPlacement (i : Fin 117) : Fin 168 :=
  if i = 109 then 136 else if i.val < 96 then ⟨i.val,by omega⟩ else ⟨i.val+48,by omega⟩

theorem intervalGuardPlacement_injective : Function.Injective intervalGuardPlacement := by
  intro i j he
  have hv := congrArg Fin.val he
  unfold intervalGuardPlacement at hv
  split_ifs at hv <;> simp_all only
  all_goals omega

/-- The placed stream is the exact guard slice consumed by interval page generation. -/
theorem recoveryGuardIntervalSymbols_coupling (A s t band a b origin N : ℕ)
    (hfit : origin+N ≤ s) :
    recoveryGuardIntervalSymbols true A s t (2*band) a b origin N =
      ((ScalarPlacement.couplingGuardSymbols true A s t band a b).drop origin).take N := by
  rw [recoveryGuardIntervalSymbols_slice _ _ _ _ _ _ _ _ _ hfit]
  rfl

def placedBinaryRecoveryGuardInterval {P U : Type} {Q A : ℕ} (boundary : Bool) : Pr P 168 Q A U :=
  embProg intervalGuardPlacement Empty.elim
    (.seq (loadIntervalGuardBank (P := Empty)) (recoveryGuardIntervalHost boundary))

theorem placedBinaryRecoveryGuardInterval_exec {P U : Type} {Q A V s t band a b origin N : ℕ}
    {body : P → Pr P 168 Q A U} (boundary : Bool) (value : Fin 117 → ℕ)
    (hs : value 97 = s) (ht : value 98 = t) (hband : value 100 = band)
    (ha : value 101 = a) (hb : value 103 = b) (hi : value 107 = origin)
    (hc : value 108 = origin+N) (hfit : origin+N ≤ s)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hbound : ∀ i, value (intervalGuardBankSource i) < 2^V)
    (v : HS 168 Q A U) (S : Stacks 168 A) (hV : ((embStk intervalGuardPlacement S).R 115).length = V)
    (hmeta : ∀ i, (embStk intervalGuardPlacement S).R (intervalGuardBankSource i) = binSyms V (value (intervalGuardBankSource i)))
    (hblank : ∀ r, (embStk intervalGuardPlacement S).R (intervalGuardReg r) = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 144*V+145+((46*N+2)*tblC V 1+66*V+2*N+70) ∧
      Exec body (placedBinaryRecoveryGuardInterval boundary) (mk v S) m
        (mk v' {S with R := (Function.update S.R 136
          (recoveryGuardIntervalSymbols boundary A s t band a b origin N++S.R 136))}) := by
  obtain ⟨v₁,m,hu₁,hm,he⟩ := binaryRecoveryGuardInterval_restored_exec
    (body := fun p : Empty => nomatch p) boundary value hs ht hband ha hb hi hc hfit hs0 hst haS hbS
    hwide hbound (embDn intervalGuardPlacement v) (embStk intervalGuardPlacement S) hV hmeta hblank
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    intervalGuardPlacement_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hu₁,hm,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  rw [embOvr_updR intervalGuardPlacement_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
