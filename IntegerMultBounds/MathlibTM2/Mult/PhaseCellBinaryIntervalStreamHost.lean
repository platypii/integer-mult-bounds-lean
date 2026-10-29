module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntervalGuardBankLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntervalGuardStreamHost

/-! Load retained binary metadata, execute an interval table and release its
bank. All interval predicates share this host and its exact restoration law. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {P U : Type} {Q A : ℕ} {body : P → Pr P 117 Q A U}

def binaryIntervalStreamHost (code : TblCode 17) : Pr P 117 Q A U :=
  .seq loadIntervalGuardBank (intervalGuardStreamHost code)

theorem binaryIntervalStreamHost_exec {V K : ℕ} (hV : 1 ≤ V)
    (code : TblCode 17) (value : Fin 117 → ℕ) (xs : List (Fin (A+4)))
    (hc : TblDo A V 1 code ⟨fun i => value (intervalGuardBankSource i),[]⟩
      (fun st' => st'.acc = xs.reverse++[]) K)
    (hbound : ∀ i, value (intervalGuardBankSource i) < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hwidth : (S.R 115).length = V)
    (hmeta : ∀ i, S.R (intervalGuardBankSource i) = binSyms V (value (intervalGuardBankSource i)))
    (hblank : ∀ r, S.R (intervalGuardReg r) = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 144*V+145+(K*tblC V 1+66*V+2*xs.length+70) ∧
      Exec body (binaryIntervalStreamHost code) (mk v S) m
        (mk v' {S with R := (Function.update S.R 109 (xs++S.R 109))}) := by
  obtain ⟨v₁,hu₁,he₁,hh,hframe⟩ := loadIntervalGuardBank_exec V value hbound v S hwidth hmeta hblank
  let S₁ : Stacks 117 A := {S with R := chirpBankLoadR intervalGuardReg intervalGuardBankSource V V value S.R}
  obtain ⟨v₂,m,hu₂,hm,he₂⟩ := intervalGuardStreamHost_exec (body := body) hV code
    ⟨fun i => value (intervalGuardBankSource i),[]⟩ xs rfl hc hbound v₁ S₁ hh
  refine ⟨v₂,144*V+145+m,hu₂.trans hu₁,Nat.add_le_add_left hm _,
    (Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases hr : r.val < 32
  · obtain ⟨k,hk⟩ := intervalGuardReg_covers r hr
    have hz : S.R r = [] := hk ▸ hblank k
    have hne : r ≠ 109 := by intro he; have hv := congrArg Fin.val he; norm_num at hv; omega
    simp [hr,hne,hz]
  · have hf : S₁.R r = S.R r := hframe r (by omega)
    by_cases ho : r = 109
    · subst r; simp [S₁,hr,hframe 109 (by decide)]
    · simp [hr,ho,hf]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
