module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginLoad

/-! Generate origin packets and their count from retained unary geometry headers.
The workspace width source is supplied by the outer width generator. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def unaryOriginController : Pr P₀ 117 Q A U :=
  .seq initializeOriginBank (.seq loadOriginHeaders originCountedController)

def unaryOriginControllerCost (P q w s t u band L : ℕ) : ℕ :=
  let V := weightWorkspaceWidth P q w t u
  104*V+137 + originHeadersCost s t band L V +
    ((27*(t-s+1)+9)*tblC V V + (naturalLengthGroup s t band L).length*(8*V+6)+6)

theorem unaryOriginController_exec (P q w s t u band L : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (hbSrc : (S.R 100).length = band) (hLSrc : (S.R 102).length = L)
    (hV : (S.R 115).length = weightWorkspaceWidth P q w t u)
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (hblank : ∀ r, S.R (originReg r) = []) :
    let V := weightWorkspaceWidth P q w t u
    ∃ v' S' m, ∃ st' : TblSt 16 A, v'.user = v.user ∧
      m ≤ unaryOriginControllerCost P q w s t u band L ∧
      Exec body unaryOriginController (mk v S) m (mk v' S') ∧
      S'.R 109 = naturalOriginPackets A V s t band L ++ S.R 109 ∧
      S'.R 116 = List.replicate (naturalLengthGroup s t band L).length tick ∧
      tblHolds originReg S' (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨st'.val, []⟩) ∧
      (∀ j, st'.val j < 2^V) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 109 → k ≠ 116 → (∀ r, originReg r ≠ k) → S'.R k = S.R k := by
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨v₁, hu₁, he₁, hh₁⟩ := initializeOriginBank_exec (body := body) V v S hV h106 hblank
  let S₁ : Stacks 117 A := { S with R := chirpBankLoadR originReg (fun _ => 106) V V (fun _ => 0) S.R }
  have hoff₁ (k : Fin 117) (hk : ∀ r, originReg r ≠ k) : S₁.R k = S.R k :=
    chirpBankLoad_off originReg (fun _ => 106) V V (fun _ => 0) S.R k
      (fun r => (hk r).symm)
  have hhigh (k : Fin 117) (hk : 31 ≤ k.val) : ∀ r, originReg r ≠ k := by
    intro r he
    have hr := originReg_range r
    rw [he] at hr
    omega
  obtain ⟨v₂, S₂, m₂, hu₂, hm₂, he₂, hh₂, hf₂⟩ := loadOriginHeaders_exec (body := body)
    s t band L V V v₁ S₁
    (by rw [hoff₁ 97 (hhigh 97 (by decide))]; exact hsSrc)
    (by rw [hoff₁ 98 (hhigh 98 (by decide))]; exact htSrc)
    (by rw [hoff₁ 100 (hhigh 100 (by decide))]; exact hbSrc)
    (by rw [hoff₁ 102 (hhigh 102 (by decide))]; exact hLSrc) hh₁
  have hoff₂ (k : Fin 117) (hk : ∀ r, originReg r ≠ k) : S₂.R k = S.R k :=
    (hf₂.2.2.2 k hk).trans (hoff₁ k hk)
  obtain ⟨v₃, S₃, m₃, st₃, hu₃, hm₃, he₃, hout, hcount, hh₃, hb₃, hi₃, ho₃, hl₃, hf₃⟩ :=
    originCountedController_exec (body := body) P q w s t u band L hP hs hst hu hband hL hLs hA v₂ S₂ hh₂
      (by rw [hoff₂ 104 (hhigh 104 (by decide))]; exact h104)
      (by rw [hoff₂ 106 (hhigh 106 (by decide))]; exact h106)
      (by rw [hoff₂ 116 (hhigh 116 (by decide))]; exact h116)
  refine ⟨v₃, S₃, 104*V+137+(m₂+m₃), st₃, hu₃.trans (hu₂.trans hu₁), ?_,
    Exec.seq he₁ (Exec.seq he₂ he₃), ?_, hcount, hh₃, hb₃,
    hi₃.trans hf₂.1, ho₃.trans hf₂.2.1, hl₃.trans hf₂.2.2.1, ?_⟩
  · unfold unaryOriginControllerCost
    dsimp only [V] at *
    omega
  · rw [hout, hoff₂ 109 (hhigh 109 (by decide))]
  · intro k hk109 hk116 hk
    exact (hf₃ k hk109 hk116 hk).trans (hoff₂ k hk)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
