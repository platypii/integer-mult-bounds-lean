module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloDescriptorLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloLengthCandidatesHost

/-! Generate the six halo candidate words from ordinary geometry headers
and release the private table bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def preparedHaloLengthCandidates : Pr P₀ 117 Q A U :=
  .seq initializeOriginBank (.seq (loadOriginList haloHeaderAssignments)
    (.seq haloLengthCandidatesController releaseOriginBank))

def preparedHaloLengthCandidatesCost (s t band a b V : ℕ) : ℕ :=
  (104*V+137)+haloHeadersCost s t band a b V+(139*tblC V V+12*V+2)+(62*V+63)

theorem preparedHaloLengthCandidates_exec (P q w s t u band a b : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b)
    (hV : (S.R 115).length = weightWorkspaceWidth P q w t u) (h106 : S.R 106 = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = []) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ preparedHaloLengthCandidatesCost s t band a b (weightWorkspaceWidth P q w t u) ∧
      Exec body preparedHaloLengthCandidates (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = Function.update S.R 87 (haloLengthCandidatePackets A (weightWorkspaceWidth P q w t u) s t band a b ++ S.R 87) := by
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨v₁, hu₁, he₁, hh₁⟩ := initializeOriginBank_exec (body := body) V v S hV h106
    (fun r => hblank _ (originReg_range r))
  let S₁ : Stacks 117 A := { S with R := chirpBankLoadR originReg (fun _ => 106) V V (fun _ => 0) S.R }
  have hoff₁ (k : Fin 117) (hk : 31 ≤ k.val) : S₁.R k = S.R k := by
    apply chirpBankLoad_off
    intro r he
    have hr := originReg_range r
    rw [he] at hk
    omega
  have hhigh (k : Fin 117) (hk : 31 ≤ k.val) : ∀ r, originReg r ≠ k := by
    intro r he
    have hr := originReg_range r
    rw [he] at hr
    omega
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hh₂, hf₂⟩ := loadHaloHeaders_exec (body := body) s t band a b V v₁ S₁
    (by rw [hoff₁ 97 (by decide)]; exact hsSrc) (by rw [hoff₁ 98 (by decide)]; exact htSrc)
    (by rw [hoff₁ 100 (by decide)]; exact hbSrc)
    (by rw [hoff₁ 111 (by decide)]; exact haSrc) (by rw [hoff₁ 113 (by decide)]; exact hbEndSrc) hh₁
  have hoff₂ (k : Fin 117) (hk : 31 ≤ k.val) : S₂.R k = S.R k :=
    (hf₂.2.2.2 k (hhigh k hk)).trans (hoff₁ k hk)
  obtain ⟨hwide, _⟩ := weightWorkspaceWidth_control (q := q) (w := w) hP hs hst hu hband
  obtain ⟨v₃, S₃, n₃, st₃, hu₃, hn₃, he₃, hout₃, hh₃, hb₃, hi₃, ho₃, hl₃, hf₃⟩ :=
    haloLengthCandidatesController_exec (body := body) hs hst hband has hbs hA hwide v₂ S₂ hh₂
  obtain ⟨v₄, n₄, hu₄, hn₄, he₄⟩ := releaseOriginBank_exec (body := body) V st₃.val v₃ S₃ hh₃
  let S₄ : Stacks 117 A := { S₃ with R := fun k => if k.val < 31 then [] else S₃.R k }
  have hoff₃ (k : Fin 117) (hk : 31 ≤ k.val) (hk87 : k ≠ 87) : S₃.R k = S.R k :=
    (hf₃ k hk87 (hhigh k hk)).trans (hoff₂ k hk)
  refine ⟨v₄, S₄, (104*V+137)+(n₂+(n₃+n₄)), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)), hi₃.trans hf₂.1,
    ho₃.trans hf₂.2.1, hl₃.trans hf₂.2.2.1, ?_⟩
  · unfold preparedHaloLengthCandidatesCost
    dsimp only [V] at *
    omega
  · funext k
    by_cases hk87 : k = 87
    · subst k; simpa [S₄, hoff₂ 87 (by decide), V] using hout₃
    by_cases hk : k.val < 31
    · simp [S₄, hk, hk87, hblank k hk]
    simp [S₄, hk, hk87, hoff₃ k (by omega) hk87]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
