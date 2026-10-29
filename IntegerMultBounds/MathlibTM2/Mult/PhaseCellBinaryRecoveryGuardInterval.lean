module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntervalGuardBankLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryGuardIntervalHost

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem binaryRecoveryGuardInterval_exec {P U : Type} {Q A V s t band a b origin N : ℕ}
    {body : P → Pr P 117 Q A U} (boundary : Bool) (value : Fin 117 → ℕ)
    (hs : value 97 = s) (ht : value 98 = t) (hband : value 100 = band)
    (ha : value 101 = a) (hb : value 103 = b) (hi : value 107 = origin)
    (hc : value 108 = origin+N) (hfit : origin+N ≤ s)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hbound : ∀ i, value (intervalGuardBankSource i) < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hV : (S.R 115).length = V)
    (hmeta : ∀ i, S.R (intervalGuardBankSource i) = binSyms V (value (intervalGuardBankSource i)))
    (hblank : ∀ r, S.R (intervalGuardReg r) = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 144*V+145+((46*N+2)*tblC V 1+66*V+2*N+70) ∧
      Exec body (.seq loadIntervalGuardBank (recoveryGuardIntervalHost boundary)) (mk v S) m
        (mk v' {S with R := fun r => if r.val < 32 then [] else if r = 109 then
          recoveryGuardIntervalSymbols boundary A s t band a b origin N++S.R r else S.R r}) := by
  obtain ⟨v₁,hu₁,he₁,hh,hframe⟩ := loadIntervalGuardBank_exec V value hbound v S hV hmeta hblank
  let S₁ : Stacks 117 A := {S with R := chirpBankLoadR intervalGuardReg intervalGuardBankSource V V value S.R}
  let st : TblSt 17 A := ⟨fun i => value (intervalGuardBankSource i),[]⟩
  obtain ⟨v₂,m,hu₂,hm,he₂⟩ := recoveryGuardIntervalHost_exec (body := body) boundary st
    (by simp [st,intervalGuardBankSource,hs]) (by simp [st,intervalGuardBankSource,ht])
    (by simp [st,intervalGuardBankSource,hband]) (by simp [st,intervalGuardBankSource,ha])
    (by simp [st,intervalGuardBankSource,hb]) (by simp [st,intervalGuardBankSource,hi])
    (by simp [st,intervalGuardBankSource,hc]) hfit rfl hs0 hst haS hbS hwide hbound v₁ S₁ hh
  refine ⟨v₂,144*V+145+m,hu₂.trans hu₁,Nat.add_le_add_left hm _,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases hr : r.val < 32
  · simp [hr]
  · have hf : S₁.R r = S.R r := hframe r (by omega)
    by_cases ho : r = 109
    · subst r; simp [S₁,hr,hframe 109 (by decide)]
    · simp [hr,ho,hf]

theorem binaryRecoveryGuardInterval_restored_exec {P U : Type} {Q A V s t band a b origin N : ℕ}
    {body : P → Pr P 117 Q A U} (boundary : Bool) (value : Fin 117 → ℕ)
    (hs : value 97 = s) (ht : value 98 = t) (hband : value 100 = band)
    (ha : value 101 = a) (hb : value 103 = b) (hi : value 107 = origin)
    (hc : value 108 = origin+N) (hfit : origin+N ≤ s)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hbound : ∀ i, value (intervalGuardBankSource i) < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hV : (S.R 115).length = V)
    (hmeta : ∀ i, S.R (intervalGuardBankSource i) = binSyms V (value (intervalGuardBankSource i)))
    (hblank : ∀ r, S.R (intervalGuardReg r) = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 144*V+145+((46*N+2)*tblC V 1+66*V+2*N+70) ∧
      Exec body (.seq loadIntervalGuardBank (recoveryGuardIntervalHost boundary)) (mk v S) m
        (mk v' {S with R := (Function.update S.R 109
          (recoveryGuardIntervalSymbols boundary A s t band a b origin N++S.R 109))}) := by
  obtain ⟨v',m,hu,hm,he⟩ := binaryRecoveryGuardInterval_exec (body := body) boundary value
    hs ht hband ha hb hi hc hfit hs0 hst haS hbS hwide hbound v S hV hmeta hblank
  refine ⟨v',m,hu,hm,he.cast rfl ?_⟩
  apply congrArg (mk v')
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases hr : r.val < 32
  · obtain ⟨k,hk⟩ := intervalGuardReg_covers r hr
    have hz : S.R r = [] := hk ▸ hblank k
    have hne : r ≠ 109 := by intro he; have hv := congrArg Fin.val he; norm_num at hv; omega
    simp [hr,hne,hz]
  · by_cases ho : r = 109 <;> simp [hr,ho]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
