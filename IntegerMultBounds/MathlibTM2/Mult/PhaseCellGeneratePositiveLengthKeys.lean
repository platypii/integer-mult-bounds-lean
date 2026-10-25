module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateLengthCandidates
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectPositiveLengths
public import IntegerMultBounds.NLogN.PhaseCellPositiveLengthKeys

/-! Generate the positive distinct length-key queue from ordinary parameters.
Candidate discovery and selection share width sources; all workspace is released. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def naturalPositiveLengthPackets (A V s t band : ℕ) : List (Fin (A+4)) :=
  (naturalPositiveLengthKeys s t band).flatMap (binSyms V)

@[simp] theorem naturalPositiveLengthPackets_length (A V s t band : ℕ) :
    (naturalPositiveLengthPackets A V s t band).length = (naturalPositiveLengthKeys s t band).length*V := by
  simp [naturalPositiveLengthPackets, List.length_flatMap, binSyms]

def generatePositiveLengthKeys : Pr P₀ 117 Q A U :=
  .seq generateRuntimeWidth (.seq generateWeightWidth
    (.seq preparedLengthCandidates (.seq selectPositiveLengths (clearWords [94, 115]))))

def generatePositiveLengthKeysCost (P q s t u band : ℕ) : ℕ :=
  let V := weightWorkspaceWidth P q (2*q+8) t u
  generateLengthCandidatesCost P q s t u band+(21*tblC V V+230*V+263)

theorem generatePositiveLengthKeys_exec (P q s t u band : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPSrc : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 106, 115, 86], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generatePositiveLengthKeysCost P q s t u band ∧
      Exec body generatePositiveLengthKeys (mk v S) n
        (mk v' { S with R := (Function.update (Function.update S.R 87
          (naturalPositiveLengthPackets A (weightWorkspaceWidth P q (2*q+8) t u) s t band ++ S.R 87))
          86 (List.replicate (naturalPositiveLengthKeys s t band).length tick)) }) := by
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨v₁, hu₁, he₁⟩ := generateRuntimeWidth_exec (body := body) q v S hq
    (hfresh 94 (by simp)) (hfresh 104 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 94 (List.replicate w tick) }
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := generateWeightWidth_exec (body := body) P q w t u v₁ S₁
    (by simpa [S₁] using hPSrc) (by simpa [S₁] using hq) (by simp [S₁])
    (by simpa [S₁] using htSrc) (by simpa [S₁] using huSrc) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [S₁, Function.update_apply]
      all_goals norm_num
      all_goals first | exact hblank _ (by decide) | exact hfresh _ (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 115 (List.replicate V tick) }
  obtain ⟨v₃, S₃, n₃, hu₃, hn₃, he₃, hi₃, ho₃, hl₃, hr₃⟩ := preparedLengthCandidates_exec (body := body)
    P q w s t u band hP hs hst hu hband hA v₂ S₂
    (by simpa [S₂, S₁] using hsSrc) (by simpa [S₂, S₁] using htSrc) (by simpa [S₂, S₁] using hbSrc)
    (by simp [S₂, V]) (by simpa [S₂, S₁] using hfresh 106 (by simp)) (by
      intro k hk
      have h94 : k ≠ (94 : Fin 117) := by intro he; subst k; norm_num at hk
      have h115 : k ≠ (115 : Fin 117) := by intro he; subst k; norm_num at hk
      simpa [S₂, S₁, h94, h115] using hblank k hk)
  have hS₃ : S₃ = { S₂ with R := (Function.update S₂.R 87
      (naturalLengthCandidatePackets A V s t band ++ S₂.R 87)) } := Stacks.ext hi₃ ho₃ hl₃ hr₃
  subst S₃
  let S₃ : Stacks 117 A := { S₂ with R := (Function.update S₂.R 87
    (naturalLengthCandidatePackets A V s t band ++ S₂.R 87)) }
  obtain ⟨hwide, _⟩ := weightWorkspaceWidth_control (q := q) (w := w) hP hs hst hu hband
  have hfit : ∀ L ∈ naturalLengthCandidates s t band, L < 2^V := by
    intro L hL
    exact (naturalLengthCandidates_le hst band hL).trans_lt (by nlinarith only [hwide, hst])
  obtain ⟨v₄, S₄, n₄, hu₄, hn₄, he₄, hi₄, ho₄, hl₄, hr₄⟩ := selectPositiveLengths_exec (body := body)
    V (naturalLength s t band 0) (naturalLength s t band (t-s))
    (s/(t-s)-2*band) ((s/(t-s)+1)-2*band)
    (by dsimp [V, weightWorkspaceWidth, coefficientWorkspaceWidth, w]; omega)
    (hfit _ (by simp [naturalLengthCandidates])) (hfit _ (by simp [naturalLengthCandidates]))
    (hfit _ (by simp [naturalLengthCandidates])) (hfit _ (by simp [naturalLengthCandidates])) hA (S.R 87) v₃ S₃
    (by simp [S₃, S₂, V]) (by simpa [S₃, S₂, S₁] using hfresh 106 (by simp))
    (by simpa [S₃, S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₃, S₂, S₁] using hfresh 86 (by simp)) (by
      intro k hk
      have h87 : k ≠ (87 : Fin 117) := by intro he; subst k; norm_num at hk
      have h94 : k ≠ (94 : Fin 117) := by intro he; subst k; norm_num at hk
      have h115 : k ≠ (115 : Fin 117) := by intro he; subst k; norm_num at hk
      simpa [S₃, S₂, S₁, h87, h94, h115] using hblank k hk)
    (by simp [S₃, S₂, S₁, naturalLengthCandidatePackets, naturalLengthCandidates])
  have hS₄ : S₄ = { S₃ with R := (Function.update (Function.update S₃.R 87
      (naturalPositiveLengthPackets A V s t band ++ S.R 87))
      86 (List.replicate (naturalPositiveLengthKeys s t band).length tick)) } :=
    Stacks.ext hi₄ ho₄ hl₄ (by simpa [naturalPositiveLengthPackets, naturalPositiveLengthKeys, naturalLengthCandidates] using hr₄)
  subst S₄
  let S₄ : Stacks 117 A := { S₃ with R := (Function.update (Function.update S₃.R 87
    (naturalPositiveLengthPackets A V s t band ++ S.R 87))
    86 (List.replicate (naturalPositiveLengthKeys s t band).length tick)) }
  obtain ⟨v₅, hu₅, he₅⟩ := clearWords_exec (body := body) [(94 : Fin 117), 115] (by decide) v₄ S₄
  have hsum : (([(94 : Fin 117), 115]).map (fun k => (S₄.R k).length)).sum = w+V := by
    simp [S₄, S₃, S₂, S₁]
  refine ⟨v₅, (4*q+5)+(n₂+(n₃+(n₄+(2*(w+V)+5)))), hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast (by rw [hsum]; rfl) ?_⟩
  · dsimp only [generatePositiveLengthKeysCost, generateLengthCandidatesCost]
    dsimp only [w, V] at *
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h94 : k = 94
      · subst k; simp [hfresh 94 (by simp)]
      by_cases h115 : k = 115
      · subst k; simp [hfresh 115 (by simp)]
      simp [S₄, S₃, S₂, S₁, h94, h115, Function.update_apply, V, w]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
