module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloDescriptorLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateOriginControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountWords
public import IntegerMultBounds.NLogN.PhaseCellHaloLengthKeys

/-! Generate positive clipped origin/length descriptors, count the generated
packets and retain both runtime widths. The owned private exponent is consumed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def prepareHaloReplicaSchedule : Pr P₀ 117 Q A U :=
  .seq (uclear 109) (.seq generateRuntimeWidth (.seq generateWeightWidth
    (.seq preparedHaloDescriptors (.seq (moveR 109 106 id) (.seq (moveR 106 87 id)
      (.seq (umul 2 115 105 104) (.seq (countWords 105 87 86 106 104) (uclear 105))))))))

def prepareHaloReplicaScheduleCost (P q l s t u band a b : ℕ) : ℕ :=
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  let K := (haloCellPhases s t band a b).length
  (2*l+2)+(4*q+5)+weightWidthCost P q w t u+preparedHaloDescriptorsCost s t band a b V+
    (8*K*V+4)+(4*V+4)+(K*(12*V+6)+4)+(4*V+2)

def preparedHaloReplicaR (A P q s t u band a b : ℕ) (R : Regs 117 A) : Regs 117 A :=
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  Function.update (Function.update (Function.update (Function.update (Function.update R
    109 []) 94 (List.replicate w tick)) 115 (List.replicate V tick))
    87 (haloDescriptorPackets A V s t band a b)) 86 (List.replicate (haloCellPhases s t band a b).length tick)

theorem prepareHaloReplicaSchedule_exec (P q l s t u band a b : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPSrc : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b)
    (hl : (S.R 109).length = l)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 105, 106, 115, 86, 87], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareHaloReplicaScheduleCost P q l s t u band a b ∧
      Exec body prepareHaloReplicaSchedule (mk v S) n
        (mk v' { S with R := preparedHaloReplicaR A P q s t u band a b S.R }) := by
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  let K := (haloCellPhases s t band a b).length
  let keys := haloDescriptorPackets A V s t band a b
  obtain ⟨v₀,hu₀,he₀⟩ := uclear_exec body 109 v S
  let S₀ : Stacks 117 A := {S with R := Function.update S.R 109 []}
  obtain ⟨v₁,hu₁,he₁⟩ := generateRuntimeWidth_exec (body := body) q v₀ S₀
    (by simpa [S₀] using hq) (by simpa [S₀] using hfresh 94 (by simp))
    (by simpa [S₀] using hfresh 104 (by simp))
  let S₁ : Stacks 117 A := {S₀ with R := Function.update S₀.R 94 (List.replicate w tick)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := generateWeightWidth_exec (body := body) P q w t u v₁ S₁
    (by simpa [S₁,S₀] using hPSrc) (by simpa [S₁,S₀] using hq) (by simp [S₁])
    (by simpa [S₁,S₀] using htSrc) (by simpa [S₁,S₀] using huSrc) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [S₁,S₀,Function.update_apply]
      all_goals norm_num
      all_goals first | exact hblank _ (by decide) | exact hfresh _ (by simp))
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 115 (List.replicate V tick)}
  obtain ⟨v₃,S₃,n₃,hu₃,hn₃,he₃,hi₃,ho₃,hl₃,hr₃⟩ := preparedHaloDescriptors_exec (body := body)
    P q w s t u band a b hP hs hst hu hband has hbs hA v₂ S₂
    (by simpa [S₂,S₁,S₀] using hsSrc) (by simpa [S₂,S₁,S₀] using htSrc)
    (by simpa [S₂,S₁,S₀] using hbSrc) (by simpa [S₂,S₁,S₀] using haSrc)
    (by simpa [S₂,S₁,S₀] using hbEndSrc) (by simp [S₂,V])
    (by simpa [S₂,S₁,S₀] using hfresh 106 (by simp)) (by
      intro k hk
      have h94 : k ≠ 94 := by intro he; subst k; norm_num at hk
      have h109 : k ≠ 109 := by intro he; subst k; norm_num at hk
      have h115 : k ≠ 115 := by intro he; subst k; norm_num at hk
      simpa [S₂,S₁,S₀,h94,h109,h115] using hblank k hk)
  have hS₃ : S₃ = {S₂ with R := Function.update S₂.R 109 keys} :=
    Stacks.ext hi₃ ho₃ hl₃ (by simpa [S₂,S₁,S₀,keys] using hr₃)
  subst S₃
  let S₃ : Stacks 117 A := {S₂ with R := Function.update S₂.R 109 keys}
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec body 109 106 (by decide) id v₃ S₃
  let S₄ : Stacks 117 A := {S₃ with R := movedR S₃.R 109 106 id (S₃.R 109)}
  obtain ⟨v₅,hu₅,he₅⟩ := moveR_exec body 106 87 (by decide) id v₄ S₄
  let S₅ : Stacks 117 A := {S₄ with R := movedR S₄.R 106 87 id (S₄.R 106)}
  obtain ⟨v₆,hu₆,he₆⟩ := umul_exec (body := body) 2 (a := 115) (b := 105) (t := 104)
    (by decide) (by decide) (by decide) v₅ S₅
    (by simpa [S₅,S₄,S₃,S₂,S₁,S₀,movedR] using hfresh 104 (by simp))
  let S₆ : Stacks 117 A := {S₅ with R := Function.update S₅.R 105 (List.replicate (2*V) tick)}
  have he₆' : Exec body (umul 2 115 105 104) (mk v₅ S₅) (4*V+4) (mk v₆ S₆) := by
    simpa [S₆,S₅,S₄,S₃,S₂,S₁,S₀,movedR,hfresh 105 (by simp)] using he₆
  let words : List (List (Fin (A+4))) := (haloCellPhases s t band a b).map (fun phase =>
    binSyms V (haloStart s t band a phase)++binSyms V (haloLength s t band a b phase))
  have hV : 0 < V := by dsimp [V,weightWorkspaceWidth,coefficientWorkspaceWidth]; omega
  obtain ⟨v₇,hu₇,he₇⟩ := countWords_exec (body := body)
    (width := 105) (src := 87) (dst := 86) (saved := 106) (tmp := 104) (by decide)
    (2*V) (by omega) words
    (by intro xs hx; obtain ⟨phase,hphase,rfl⟩ := List.mem_map.mp hx; simp [binSyms]; omega)
    v₆ S₆ (by simp [S₆])
    (by simp [S₆,S₅,S₄,S₃,S₂,S₁,S₀,movedR,words,keys,haloDescriptorPackets,
      hfresh 106 (by simp),hfresh 87 (by simp),List.flatMap])
    (by simp [S₆,S₅,S₄,movedR])
    (by simpa [S₆,S₅,S₄,S₃,S₂,S₁,S₀,movedR] using hfresh 104 (by simp))
  let S₇ : Stacks 117 A := {S₆ with R := Function.update S₆.R 86 (List.replicate K tick)}
  have he₇' : Exec body (countWords 105 87 86 106 104) (mk v₆ S₆) (K*(12*V+6)+4) (mk v₇ S₇) := by
    simpa [S₇,words,K,S₆,S₅,S₄,S₃,S₂,S₁,S₀,movedR,hfresh 86 (by simp),show 6*(2*V) = 12*V by omega] using he₇
  obtain ⟨v₈,hu₈,he₈⟩ := uclear_exec body 105 v₇ S₇
  have hkeys : keys.length = K*(2*V) := haloDescriptorPackets_length A V s t band a b
  refine ⟨v₈,_,hu₈.trans (hu₇.trans (hu₆.trans (hu₅.trans (hu₄.trans
    (hu₃.trans (hu₂.trans (hu₁.trans hu₀))))))),?_,
    (Exec.seq he₀ (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄
      (Exec.seq he₅ (Exec.seq he₆' (Exec.seq he₇' he₈)))))))).cast rfl ?_⟩
  · dsimp only [prepareHaloReplicaScheduleCost]
    simp [S₇,S₆,S₅,S₄,S₃,S₂,S₁,S₀,movedR,hkeys,hfresh 106 (by simp),hl]
    dsimp only [w,V,K] at hn₂ hn₃ ⊢
    nlinarith only [hn₂,hn₃]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h105 : k = 105
      · subst k; simp [preparedHaloReplicaR,hfresh 105 (by simp)]
      by_cases h106 : k = 106
      · subst k; simp [S₇,S₆,S₅,movedR,preparedHaloReplicaR,hfresh 106 (by simp)]
      by_cases h109 : k = 109
      · subst k; simp [S₇,S₆,S₅,S₄,movedR,preparedHaloReplicaR]
      simp [S₇,S₆,S₅,S₄,S₃,S₂,S₁,S₀,movedR,preparedHaloReplicaR,h109,
        Function.update_apply,h105,h106,hfresh 106 (by simp),hfresh 87 (by simp),V,w,K,keys]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
