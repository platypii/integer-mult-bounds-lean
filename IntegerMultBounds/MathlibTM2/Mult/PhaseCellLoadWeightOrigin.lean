module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedWeightHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix

/-! Replace the table origin by one fixed-width binary packet, preserving the
initialized arithmetic and all remaining packets. No unary absolute origin is
constructed or scanned. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def loadWeightOrigin : Pr P₀ 117 Q A U := .seq (uclear 47) (takePrefix 115 109 47 104 105)

theorem WeightReady.origin {A V P q s t u L lo : ℕ} {st : TblSt 48 A}
    (h : WeightReady A V P q s t u L st) (hlo : lo < 2^V) :
    WeightReady A V P q s t u L ⟨Function.update st.val 47 lo, st.acc⟩ := by
  refine ⟨?_, h.acc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k = 47
    · simpa [hk] using hlo
    · simpa [hk] using h.bounded k
  · simpa using h.precision
  · simpa using h.modulus
  · simpa using h.period
  · simpa using h.scale
  · simpa using h.rows
  · simpa [WeightInitialized] using h.initialized

theorem loadWeightOrigin_exec (V w lo : ℕ) (st : TblSt 48 A)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A+4)))
    (hS : tblHolds coefficientReg S (tblRho V (List.replicate V tick) (List.replicate w tick) st))
    (hV : (S.R 115).length = V) (hsrc : S.R 109 = binSyms V lo ++ tail)
    (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v', v'.user = v.user ∧ Exec body loadWeightOrigin (mk v S) (8*V+8)
      (mk v' { S with R := (Function.update (Function.update S.R 47 (binSyms V lo)) 109 tail) }) ∧
      tblHolds coefficientReg { S with R := (Function.update (Function.update S.R 47 (binSyms V lo)) 109 tail) }
        (tblRho V (List.replicate V tick) (List.replicate w tick)
          ⟨Function.update st.val 47 lo, st.acc⟩) := by
  obtain ⟨v₁, hu₁, he₁⟩ := uclear_exec body 47 v S
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 47 [] }
  obtain ⟨v₂, hu₂, he₂⟩ := takePrefix_exec (body := body)
    (show [(115 : Fin 117), 109, 47, 104, 105].Nodup by decide) v₁ S₁ (binSyms V lo) tail
    (by simpa [S₁] using hsrc) (by simpa [S₁] using hV)
    (by simpa [S₁] using h104) (by simpa [S₁] using h105)
  have h47 : (S.R 47).length = V := by
    have hh := hS (.v 47)
    simpa [coefficientReg, tblRho] using congrArg List.length hh
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast (by simp [h47]; omega) ?_, ?_⟩
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases hk47 : k = 47
      · subst k; simp [S₁]
      by_cases hk109 : k = 109
      · subst k; simp [S₁]
      simp [S₁, hk47, hk109]
  · intro r
    have hn : coefficientReg r ≠ (109 : Fin 117) := by
      intro he; have hr := coefficientReg_range r; rw [he] at hr; omega
    change Function.update (Function.update S.R 47 (binSyms V lo)) 109 tail (coefficientReg r) = _
    rw [Function.update_of_ne hn]
    have hh := tbl_holds_upd coefficientReg_injective hS (.v 47) (binSyms V lo) r
    have hrho : Function.update (tblRho V (List.replicate V tick) (List.replicate w tick) st)
        (.v 47) (binSyms V lo) r =
        tblRho V (List.replicate V tick) (List.replicate w tick)
          ⟨Function.update st.val 47 lo, st.acc⟩ r := by
      cases r with
      | v i => by_cases hi : i = 47 <;> simp [tblRho, hi]
      | wr => simp [tblRho]
      | wn => simp [tblRho]
      | acc => simp [tblRho]
      | z i => simp [tblRho]
    exact hh.trans hrho

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
