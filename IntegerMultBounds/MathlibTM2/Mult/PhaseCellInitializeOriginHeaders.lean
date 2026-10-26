module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginLoad

/-! Shared initialization and structural loading for numeric geometry queries. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def initializeOriginHeaders (rs : List (Fin 117 × Fin 16)) : Pr P₀ 117 Q A U :=
  .seq initializeOriginBank (loadOriginList rs)

theorem initializeOriginHeaders_exec (rs : List (Fin 117 × Fin 16))
    (hsep : ∀ r ∈ rs, ∀ x, originReg x ≠ r.1) (V : ℕ) (value : Fin 117 → ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsrc : ∀ r ∈ rs, (S.R r.1).length = value r.1)
    (hV : (S.R 115).length = V) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = []) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ 104*V+137+loadOriginListCost V value rs ∧
      Exec body (initializeOriginHeaders rs) (mk v S) m (mk v' S') ∧
      tblHolds originReg S' (tblRho V (List.replicate V tick) (List.replicate V tick)
        (loadedOriginState value rs ⟨fun _ => 0,[]⟩)) ∧ tblFr originReg S S' := by
  obtain ⟨v₁,hu₁,he₁,hh₁⟩ := initializeOriginBank_exec (body := body) V v S hV h106
    (fun x => hblank _ (originReg_range x))
  let S₁ : Stacks 117 A := {S with R := chirpBankLoadR originReg (fun _ => 106) V V (fun _ => 0) S.R}
  have hoff (r : Fin 117) (hr : ∀ x, originReg x ≠ r) : S₁.R r = S.R r :=
    chirpBankLoad_off _ _ _ _ _ _ r (fun x => (hr x).symm)
  obtain ⟨v₂,S₂,m₂,hu₂,hm₂,he₂,hh₂,hf₂⟩ := loadOriginList_exec (body := body)
    rs hsep V V value ⟨fun _ => 0,[]⟩ v₁ S₁
    (fun r hr => (congrArg List.length (hoff r.1 (hsep r hr))).trans (hsrc r hr)) hh₁
  refine ⟨v₂,S₂,(104*V+137)+m₂,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂,hh₂,
    hf₂.1,hf₂.2.1,hf₂.2.2.1,?_⟩
  intro r hr
  exact (hf₂.2.2.2 r hr).trans (hoff r hr)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
