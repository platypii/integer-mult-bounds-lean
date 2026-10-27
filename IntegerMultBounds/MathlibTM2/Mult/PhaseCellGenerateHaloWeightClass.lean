module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedHaloWeightKey
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyLengthKeyFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseHaloGroupHeaders

/-! Generate one retained page from caller masters, restoring every private
scalar header before the next runtime length class. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 151 Q A U}

def weightFamilyLegacyReg (i : Fin 144) : Fin 151 := weightFamilyCoreReg (cachedGroupLegacyReg i)

theorem weightFamilyLegacyReg_injective : Function.Injective weightFamilyLegacyReg :=
  weightFamilyCoreReg_injective.comp cachedGroupLegacyReg_injective

theorem weightFamilyLegacyReg_off (i : Fin 151) (hi : 144 ≤ i.val) :
    ∀ j, weightFamilyLegacyReg j ≠ i := by
  intro j he
  have hh := congrArg (fun i : Fin 151 => i.val) he
  dsimp [weightFamilyLegacyReg,weightFamilyCoreReg,cachedGroupLegacyReg] at hh
  omega

def generateHaloWeightClass : Pr P₀ 151 Q A U :=
  .seq (embProg weightFamilyLegacyReg Empty.elim (installHaloGroupHeaders (P₀ := Empty)))
    (.seq generatedHaloWeightKey (embProg weightFamilyLegacyReg Empty.elim (releaseGroupHeaders (P := Empty))))

def generateHaloWeightClassCost (P N q l s t u band a b L : ℕ) : ℕ :=
  installHaloGroupHeadersCost P N q l s t u band a b L+
    generatedHaloWeightKeyCost P q s t u band a b L+
    (2*(P+N+q+l+s+t+u+band+2*L)+21)

theorem generateHaloWeightClass_exec (P N q l s t u band a b L : ℕ) [NeZero s]
    (hP : 13 ≤ P) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s)
    (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 151 Q A U) (S : Stacks 151 A)
    (hmasters : ∀ r ∈ groupHeaderCopies, ((weightFamilyLegacyBank S).R r.1).length =
      groupHeaderValue P N q l s t u band L r.1)
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b)
    (hleft : ∀ k : Fin 144, k.val < 117 → (weightFamilyLegacyBank S).L k = [])
    (hblank : ∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → (weightFamilyLegacyBank S).R k = [])
    (h133 : S.R 133 = [])
    (hcache : ∀ i ∈ ([(144 : Fin 151),145,146,147,149] : List (Fin 151)), S.R i = []) :
    let page := batchWeightPage A (2*q+8) q P s t u (haloLengthGroup s t band a b L).length L
      (fun n => (haloGroupOrigin s t band a b L n).val)
    ∃ v' m, v'.user = v.user ∧ m ≤ generateHaloWeightClassCost P N q l s t u band a b L ∧
      Exec body generateHaloWeightClass (mk v S) m
        (mk v' {S with R := Function.update S.R 150 ((weightKeyPacket page).reverse++S.R 150)}) := by
  dsimp only
  let page := batchWeightPage A (2*q+8) q P s t u (haloLengthGroup s t band a b L).length L
    (fun n => (haloGroupOrigin s t band a b L n).val)
  let D := weightFamilyLegacyBank S
  obtain ⟨vi,hui,hei⟩ := installHaloGroupHeaders_exec
    (body := fun p : Empty => nomatch p) P N q l s t u band a b L (embDn weightFamilyLegacyReg v) D
    hmasters ha hb (hblank 111 (by decide) (by decide) (by decide))
    (hblank 113 (by decide) (by decide) (by decide)) h133
  obtain ⟨v₁,T,he₁,hv₁,hu₁,hproj,hoff₁⟩ := exec_emb (body' := body) (ι := Empty.elim)
    weightFamilyLegacyReg_injective (fun p => nomatch p) hei v rfl S rfl
  have hcore : embStk weightCacheCoreReg (embStk weightFamilyGenerateReg T) =
      haloGroupInputBank P N q l s t u band a b L (S.R 110) [] (S.R 93) S.inp S.out := by
    have hv : embStk weightCacheCoreReg (embStk weightFamilyGenerateReg T) =
        embStk groupReg (embStk weightFamilyLegacyReg T) := by
      have he (i : Fin 117) : weightFamilyGenerateReg (weightCacheCoreReg i) = weightFamilyLegacyReg (groupReg i) := by
        apply Fin.ext
        simp [weightFamilyGenerateReg,weightFamilyLegacyReg,weightFamilyCoreReg,cachedGroupReg,
          cachedGroupLegacyReg,weightCacheCoreReg,groupReg,i.isLt]
      exact Stacks.ext rfl rfl (funext fun i => congrArg T.L (he i)) (funext fun i => congrArg T.R (he i))
    rw [hv,hproj]
    exact copiedHaloGroup_project P N q l s t u band a b L D (S.R 110) [] hleft hblank (by simp [D,weightFamilyLegacyBank,embStk,weightFamilyCoreReg,cachedGroupLegacyReg])
  have hhigh (i : Fin 151) (hi : 144 ≤ i.val) : T.R i = S.R i :=
    (hoff₁ i (weightFamilyLegacyReg_off i hi)).2
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := generatedHaloWeightKey_exec (body := body)
    P q s t u band a b L hP hst hu hband has hbs hL hLs hA v₁ T
    (by change ((embStk weightCacheCoreReg (embStk weightFamilyGenerateReg T)).R 114).length = P; rw [hcore]; simp [haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank])
    (by change ((embStk weightCacheCoreReg (embStk weightFamilyGenerateReg T)).R 112).length = q; rw [hcore]; simp [haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank])
    (by change ((embStk weightCacheCoreReg (embStk weightFamilyGenerateReg T)).R 97).length = s; rw [hcore]; simp [haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank])
    (by change ((embStk weightCacheCoreReg (embStk weightFamilyGenerateReg T)).R 98).length = t; rw [hcore]; simp [haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank])
    (by change ((embStk weightCacheCoreReg (embStk weightFamilyGenerateReg T)).R 99).length = u; rw [hcore]; simp [haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank])
    (by change ((embStk weightCacheCoreReg (embStk weightFamilyGenerateReg T)).R 100).length = band; rw [hcore]; simp [haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank])
    (by change ((embStk weightCacheCoreReg (embStk weightFamilyGenerateReg T)).R 111).length = a; rw [hcore]; simp [haloGroupInputBank,haloEndpointR])
    (by change ((embStk weightCacheCoreReg (embStk weightFamilyGenerateReg T)).R 113).length = b; rw [hcore]; simp [haloGroupInputBank,haloEndpointR])
    (by change ((embStk weightCacheCoreReg (embStk weightFamilyGenerateReg T)).R 102).length = L; rw [hcore]; simp [haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank])
    (by change ((embStk weightCacheCoreReg (embStk weightFamilyGenerateReg T)).R 103).length = L; rw [hcore]; simp [haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank])
    (by
      intro k hk
      rw [hcore]
      have hn (n : ℕ) (hh : 63 ≤ n) : k.val ≠ n := by omega
      simp [haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank,Fin.ext_iff,
        hn 111 (by decide),hn 113 (by decide),hn 101 (by decide),hn 102 (by decide),hn 103 (by decide),
        hn 97 (by decide),hn 98 (by decide),hn 99 (by decide),hn 100 (by decide),hn 109 (by decide),
        hn 112 (by decide),hn 114 (by decide),hn 116 (by decide),hn 110 (by decide),hn 93 (by decide)])
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (simpa [embStk,weightCacheCoreReg,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using congrArg (fun B => B.R 64) hcore)
        | (simpa [embStk,weightCacheCoreReg,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using congrArg (fun B => B.R 65) hcore)
        | (simpa [embStk,weightCacheCoreReg,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using congrArg (fun B => B.R 94) hcore)
        | (simpa [embStk,weightCacheCoreReg,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using congrArg (fun B => B.R 96) hcore)
        | (simpa [embStk,weightCacheCoreReg,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using congrArg (fun B => B.R 104) hcore)
        | (simpa [embStk,weightCacheCoreReg,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using congrArg (fun B => B.R 105) hcore)
        | (simpa [embStk,weightCacheCoreReg,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using congrArg (fun B => B.R 106) hcore)
        | (simpa [embStk,weightCacheCoreReg,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using congrArg (fun B => B.R 107) hcore)
        | (simpa [embStk,weightCacheCoreReg,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using congrArg (fun B => B.R 108) hcore)
        | (simpa [embStk,weightCacheCoreReg,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using congrArg (fun B => B.R 115) hcore)
        | (simpa [embStk,weightCacheCoreReg,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using congrArg (fun B => B.R 116) hcore)
        | (change T.R 145 = []; rw [hhigh 145 (by decide)]; exact hcache 145 (by simp))
        | (change T.R 146 = []; rw [hhigh 146 (by decide)]; exact hcache 146 (by simp))
        | (change T.R 147 = []; rw [hhigh 147 (by decide)]; exact hcache 147 (by simp)))
    (by rw [hhigh 144 (by decide)]; exact hcache 144 (by simp))
    (by rw [hhigh 149 (by decide)]; exact hcache 149 (by simp))
  let W : Stacks 151 A := {T with R := (Function.update (Function.update (Function.update T.R
    111 []) 113 []) 150 ((weightKeyPacket page).reverse++T.R 150))}
  have hW : embStk weightFamilyLegacyReg W = {D with R := copiedGroupR P N q l s t u band L D.R} := by
    refine Stacks.ext ?_ ?_ ?_ ?_
    · change T.inp = D.inp
      exact congrArg (fun Z : Stacks 144 A => Z.inp) hproj
    · change T.out = D.out
      exact congrArg (fun Z : Stacks 144 A => Z.out) hproj
    · change (embStk weightFamilyLegacyReg T).L = D.L
      have hh := congrArg (fun Z : Stacks 144 A => Z.L) hproj
      exact hh
    · funext i
      have hh := congrArg (fun B => B.R i) hproj
      change T.R (weightFamilyLegacyReg i) = _ at hh
      have hi150 : weightFamilyLegacyReg i ≠ 150 := by
        intro he
        have hv := congrArg (fun k : Fin 151 => k.val) he
        dsimp [weightFamilyLegacyReg,weightFamilyCoreReg,cachedGroupLegacyReg] at hv
        omega
      by_cases hi111 : i = 111
      · subst i
        simp [W,embStk,weightFamilyLegacyReg,weightFamilyCoreReg,cachedGroupLegacyReg,
          copiedGroupR_endpoint P N q l s t u band L D.R 111 (by simp)]
        exact hblank 111 (by decide) (by decide) (by decide)
      by_cases hi113 : i = 113
      · subst i
        simp [W,embStk,weightFamilyLegacyReg,weightFamilyCoreReg,cachedGroupLegacyReg,
          copiedGroupR_endpoint P N q l s t u band L D.R 113 (by simp)]
        exact hblank 113 (by decide) (by decide) (by decide)
      have hv111 : i.val ≠ 111 := by simpa [Fin.ext_iff] using hi111
      have hv113 : i.val ≠ 113 := by simpa [Fin.ext_iff] using hi113
      have hv150 : i.val ≠ 150 := by omega
      simpa [W,embStk,copiedHaloGroupR,Function.update_apply,hi111,hi113,hi150,
        weightFamilyLegacyReg,weightFamilyCoreReg,cachedGroupLegacyReg,Fin.ext_iff,hv111,hv113,hv150] using hh
  have hdest : ∀ r ∈ groupHeaderCopies, D.R r.2 = [] := by
    intro r hr
    simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hblank _ (by decide) (by decide) (by decide)
  obtain ⟨vr,hur,her⟩ := releaseGroupHeaders_exec (body144 := fun p : Empty => nomatch p)
    P N q l s t u band L (embDn weightFamilyLegacyReg v₂) D hdest
  obtain ⟨v₃,F,he₃,hv₃,hu₃,hfinal,hoff₃⟩ := exec_emb (body' := body) (ι := Empty.elim)
    weightFamilyLegacyReg_injective (fun p => nomatch p) her v₂ rfl W hW
  refine ⟨v₃,installHaloGroupHeadersCost P N q l s t u band a b L+(n₂+(2*(P+N+q+l+s+t+u+band+2*L)+21)),
    hu₃.trans (hur.trans (hu₂.trans (hu₁.trans hui))),by dsimp only [generateHaloWeightClassCost]; omega,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext (congrArg (fun Z : Stacks 144 A => Z.inp) hfinal) (congrArg (fun Z : Stacks 144 A => Z.out) hfinal) ?_ ?_
  · funext i
    by_cases hi : i.val < 144
    · exact congrArg (fun B => B.L (⟨i.val,hi⟩ : Fin 144)) hfinal
    · exact (hoff₃ i (weightFamilyLegacyReg_off i (by omega))).1.trans
        (hoff₁ i (weightFamilyLegacyReg_off i (by omega))).1
  · funext i
    by_cases hi : i.val < 144
    · have hh := congrArg (fun B => B.R (⟨i.val,hi⟩ : Fin 144)) hfinal
      have hi150 : i ≠ 150 := by intro h; subst i; norm_num at hi
      simpa [D,weightFamilyLegacyBank,embStk,weightFamilyLegacyReg,weightFamilyCoreReg,cachedGroupLegacyReg,hi150] using hh
    · rw [(hoff₃ i (weightFamilyLegacyReg_off i (by omega))).2]
      have hi111 : i ≠ 111 := by intro h; subst i; norm_num at hi
      have hi113 : i ≠ 113 := by intro h; subst i; norm_num at hi
      simp [W,Function.update_apply,hi111,hi113,hhigh i (by omega),hhigh 150 (by decide),page]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
