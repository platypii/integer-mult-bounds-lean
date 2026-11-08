module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnaryOriginController
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableRelease

/-! Release the bounded origin-controller table after its packets and count
have been published outside the table bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

open IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def cleanOriginController : Pr P₀ 117 Q A U :=
  .seq unaryOriginController releaseOriginBank

theorem cleanOriginController_exec (P q w s t u band L : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (hbSrc : (S.R 100).length = band) (hLSrc : (S.R 102).length = L)
    (hV : (S.R 115).length = weightWorkspaceWidth P q w t u)
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (hblank : ∀ r, S.R (originReg r) = []) :
    let V := weightWorkspaceWidth P q w t u
    ∃ v' m, v'.user = v.user ∧
      m ≤ unaryOriginControllerCost P q w s t u band L + (62*V+63) ∧
      Exec body cleanOriginController (mk v S) m
        (mk v' { S with R := (Function.update (Function.update S.R 109
          (naturalOriginPackets A V s t band L ++ S.R 109)) 116
          (List.replicate (naturalLengthGroup s t band L).length tick)) }) := by
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨v₁, S₁, m₁, st₁, hu₁, hm₁, he₁, hout, hcount, hh₁, hb₁, hi₁, ho₁, hl₁, hf₁⟩ :=
    unaryOriginController_exec (body := body) P q w s t u band L hP hs hst hu hband hL hLs hA v S
      hsSrc htSrc hbSrc hLSrc hV h104 h106 h116 hblank
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := releaseOriginBank_exec (body := body) V st₁.val v₁ S₁ hh₁
  refine ⟨v₂, m₁+m₂, hu₂.trans hu₁, by omega, (Exec.seq he₁ he₂).cast rfl ?_⟩
  congr 1
  ext1
  · exact hi₁
  · exact ho₁
  · exact hl₁
  · funext k
    by_cases hlo : k.val < 31
    · have hk109 : k ≠ (109 : Fin 117) := by intro he; subst k; norm_num at hlo
      have hk116 : k ≠ (116 : Fin 117) := by intro he; subst k; norm_num at hlo
      obtain ⟨r, rfl⟩ := originReg_covers k hlo
      simp [hlo, hk109, hk116, hblank r]
    by_cases hk116 : k = 116
    · subst k; simp [hcount]
    by_cases hk109 : k = 109
    · subst k; simp [hout]
    have hoff : ∀ r, originReg r ≠ k := by
      intro r he
      have hr := originReg_range r
      rw [he] at hr
      omega
    simp [hlo, hk109, hk116, hf₁ k hk109 hk116 hoff]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
