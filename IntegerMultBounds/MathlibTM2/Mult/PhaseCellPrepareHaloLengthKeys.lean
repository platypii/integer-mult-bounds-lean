module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloLengthCandidatesLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateOriginControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectSixPositiveLengths
public import IntegerMultBounds.NLogN.PhaseCellHaloLengthKeys

/-! Generate the positive distinct length-key queue and retain the shared widths
for the protected iterator. All arithmetic/table workspace is released. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def haloPositiveLengthPackets (A V s t band a b : ℕ) : List (Fin (A+4)) :=
  (haloLengthKeys s t band a b).flatMap (binSyms V)

@[simp] theorem haloPositiveLengthPackets_length (A V s t band a b : ℕ) :
    (haloPositiveLengthPackets A V s t band a b).length = (haloLengthKeys s t band a b).length*V := by
  simp [haloPositiveLengthPackets, List.length_flatMap, binSyms]

def prepareHaloLengthKeys : Pr P₀ 117 Q A U :=
  .seq generateRuntimeWidth (.seq generateWeightWidth (.seq preparedHaloLengthCandidates selectSixPositiveLengths))

def prepareHaloLengthKeysCost (P q s t u band a b : ℕ) : ℕ :=
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  (4*q+5)+weightWidthCost P q w t u+preparedHaloLengthCandidatesCost s t band a b V+(43*tblC V V+262*V+291)

def preparedHaloLengthR (A P q s t u band a b : ℕ) (R : Fin 117 → List (Fin (A+4))) :=
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  Function.update (Function.update (Function.update (Function.update R 94 (List.replicate w tick))
    115 (List.replicate V tick)) 87 (haloPositiveLengthPackets A V s t band a b++R 87))
    86 (List.replicate (haloLengthKeys s t band a b).length tick)

theorem prepareHaloLengthKeys_exec (P q s t u band a b : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPSrc : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 106, 115, 86], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareHaloLengthKeysCost P q s t u band a b ∧
      Exec body prepareHaloLengthKeys (mk v S) n
        (mk v' { S with R := preparedHaloLengthR A P q s t u band a b S.R }) := by
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
  obtain ⟨v₃, S₃, n₃, hu₃, hn₃, he₃, hi₃, ho₃, hl₃, hr₃⟩ := preparedHaloLengthCandidates_exec (body := body)
    P q w s t u band a b hP hs hst hu hband has hbs hA v₂ S₂
    (by simpa [S₂, S₁] using hsSrc) (by simpa [S₂, S₁] using htSrc) (by simpa [S₂, S₁] using hbSrc)
    (by simpa [S₂, S₁] using haSrc) (by simpa [S₂, S₁] using hbEndSrc)
    (by simp [S₂, V]) (by simpa [S₂, S₁] using hfresh 106 (by simp)) (by
      intro k hk
      have h94 : k ≠ (94 : Fin 117) := by intro he; subst k; norm_num at hk
      have h115 : k ≠ (115 : Fin 117) := by intro he; subst k; norm_num at hk
      simpa [S₂, S₁, h94, h115] using hblank k hk)
  have hS₃ : S₃ = { S₂ with R := (Function.update S₂.R 87
      (haloLengthCandidatePackets A V s t band a b ++ S₂.R 87)) } := Stacks.ext hi₃ ho₃ hl₃ hr₃
  subst S₃
  let S₃ : Stacks 117 A := { S₂ with R := (Function.update S₂.R 87
    (haloLengthCandidatePackets A V s t band a b ++ S₂.R 87)) }
  obtain ⟨hwide, _⟩ := weightWorkspaceWidth_control (q := q) (w := w) hP hs hst hu hband
  have hfit : ∀ L ∈ haloLengthCandidates s t band a b, L < 2^V := by
    intro L hL
    exact ((haloLengthCandidates_uniform hst band a b hL).trans ((Nat.sub_le _ _).trans (Nat.add_le_add_right (Nat.div_le_self _ _) 1))).trans_lt (by nlinarith only [hwide, hst])
  obtain ⟨v₄, S₄, n₄, hu₄, hn₄, he₄, hi₄, ho₄, hl₄, hr₄⟩ := selectSixPositiveLengths_exec (body := body)
    V (naturalLength s t band 0) (naturalLength s t band (t-s))
    (s/(t-s)-2*band) ((s/(t-s)+1)-2*band)
    (haloLength s t band a b (naturalPhase s t (a+band)))
    (haloLength s t band a b (naturalPhase s t (b-band-1)))
    (by dsimp [V, weightWorkspaceWidth, coefficientWorkspaceWidth, w]; omega)
    (hfit _ (by simp [haloLengthCandidates,naturalLengthCandidates])) (hfit _ (by simp [haloLengthCandidates,naturalLengthCandidates]))
    (hfit _ (by simp [haloLengthCandidates,naturalLengthCandidates])) (hfit _ (by simp [haloLengthCandidates,naturalLengthCandidates]))
    (hfit _ (by simp [haloLengthCandidates])) (hfit _ (by simp [haloLengthCandidates])) hA (S.R 87) v₃ S₃
    (by simp [S₃, S₂, V]) (by simpa [S₃, S₂, S₁] using hfresh 106 (by simp))
    (by simpa [S₃, S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₃, S₂, S₁] using hfresh 86 (by simp)) (by
      intro k hk
      have h87 : k ≠ (87 : Fin 117) := by intro he; subst k; norm_num at hk
      have h94 : k ≠ (94 : Fin 117) := by intro he; subst k; norm_num at hk
      have h115 : k ≠ (115 : Fin 117) := by intro he; subst k; norm_num at hk
      simpa [S₃, S₂, S₁, h87, h94, h115] using hblank k hk)
    (by simp [S₃, S₂, S₁, haloLengthCandidatePackets, haloLengthCandidates, naturalLengthCandidates])
  have hS₄ : S₄ = { S₃ with R := (Function.update (Function.update S₃.R 87
      (haloPositiveLengthPackets A V s t band a b ++ S.R 87))
      86 (List.replicate (haloLengthKeys s t band a b).length tick)) } :=
    Stacks.ext hi₄ ho₄ hl₄ (by simpa [haloPositiveLengthPackets, haloLengthKeys, haloLengthCandidates, naturalLengthCandidates] using hr₄)
  subst S₄
  refine ⟨v₄,(4*q+5)+(n₂+(n₃+n₄)),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast rfl ?_⟩
  · dsimp only [prepareHaloLengthKeysCost]
    dsimp only [w,V] at *
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    simp [S₃,S₂,S₁,preparedHaloLengthR,Function.update_apply,V,w]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
