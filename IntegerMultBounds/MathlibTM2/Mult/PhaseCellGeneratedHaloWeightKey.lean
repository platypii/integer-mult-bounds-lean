module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedHaloWeightCache
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightFamilyWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStoreGeneratedWeightKey

/-! Generate one exact numerical family packet in the runtime workspace. The
ordinary unary geometry determines both its origins and its numerical page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 151 Q A U}

def weightFamilyGenerateReg (i : Fin 121) : Fin 151 := weightFamilyCoreReg (cachedGroupReg i)

theorem weightFamilyGenerateReg_injective : Function.Injective weightFamilyGenerateReg :=
  weightFamilyCoreReg_injective.comp cachedGroupReg_injective

def generatedHaloWeightKey : Pr P₀ 151 Q A U :=
  .seq (embProg weightFamilyGenerateReg Empty.elim (generatedHaloWeightCache (P₀ := Empty))) storeGeneratedWeightKey

def generatedHaloWeightKeyCost (P q s t u band a b L : ℕ) : ℕ :=
  generatedHaloWeightCacheCost P q s t u band a b L+
    28*((haloLengthGroup s t band a b L).length*(L*(2*q+8)))+24

theorem generatedHaloWeightKey_exec (P q s t u band a b L : ℕ) [NeZero s]
    (hP : 13 ≤ P) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s)
    (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 151 Q A U) (S : Stacks 151 A)
    (hPSrc : ((embStk weightFamilyGenerateReg S).R 114).length = P)
    (hq : ((embStk weightFamilyGenerateReg S).R 112).length = q)
    (hsSrc : ((embStk weightFamilyGenerateReg S).R 97).length = s)
    (htSrc : ((embStk weightFamilyGenerateReg S).R 98).length = t)
    (huSrc : ((embStk weightFamilyGenerateReg S).R 99).length = u)
    (hbSrc : ((embStk weightFamilyGenerateReg S).R 100).length = band)
    (haSrc : ((embStk weightFamilyGenerateReg S).R 111).length = a)
    (hbEndSrc : ((embStk weightFamilyGenerateReg S).R 113).length = b)
    (hLSrc : ((embStk weightFamilyGenerateReg S).R 102).length = L)
    (hrows : ((embStk weightFamilyGenerateReg S).R 103).length = L)
    (hblank : ∀ k : Fin 117, k.val < 63 →
      (embStk weightCacheCoreReg (embStk weightFamilyGenerateReg S)).R k = [])
    (hfresh : ∀ k ∈ ([(64 : Fin 121),65,94,96,104,105,106,107,108,115,116,118,119,120] : List (Fin 121)),
      (embStk weightFamilyGenerateReg S).R k = [])
    (h144 : S.R 144 = []) (h149 : S.R 149 = []) :
    let B := (haloLengthGroup s t band a b L).length
    let w := 2*q+8
    let page := batchWeightPage A w q P s t u B L (fun n => (haloGroupOrigin s t band a b L n).val)
    ∃ v' m, v'.user = v.user ∧ m ≤ generatedHaloWeightKeyCost P q s t u band a b L ∧
      Exec body generatedHaloWeightKey (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          111 []) 113 []) 150 ((weightKeyPacket page).reverse++S.R 150))}) := by
  dsimp only
  let B := (haloLengthGroup s t band a b L).length
  let w := 2*q+8
  let page := batchWeightPage A w q P s t u B L (fun n => (haloGroupOrigin s t band a b L n).val)
  obtain ⟨vi,n₁,hui,hn₁,hei⟩ := generatedHaloWeightCache_exec
    (body := fun p : Empty => nomatch p) P q s t u band a b L hP hst hu hband has hbs hL hLs hA
    (embDn weightFamilyGenerateReg v) (embStk weightFamilyGenerateReg S)
    hPSrc hq hsSrc htSrc huSrc hbSrc haSrc hbEndSrc hLSrc hrows hblank hfresh
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    weightFamilyGenerateReg_injective (fun p => nomatch p) hei v rfl S rfl
  let T : Stacks 151 A := {S with R := (Function.update (Function.update (Function.update (Function.update S.R
    111 []) 113 []) 144 page) 145 (List.replicate page.length tick))}
  have he₁' : Exec body (embProg weightFamilyGenerateReg Empty.elim (generatedHaloWeightCache (P₀ := Empty)))
      (mk v S) n₁ (mk v₁ T) := by
    refine he₁.cast rfl ?_
    apply congrArg (mk v₁)
    change embOvr weightFamilyGenerateReg
      ({ { { {embStk weightFamilyGenerateReg S with R := Function.update (embStk weightFamilyGenerateReg S).R 111 []}
        with R := Function.update (Function.update (embStk weightFamilyGenerateReg S).R 111 []) 113 []}
        with R := (Function.update (Function.update (Function.update (embStk weightFamilyGenerateReg S).R 111 []) 113 []) 117
          (page++(embStk weightFamilyGenerateReg S).R 117))}
        with R := (Function.update (Function.update (Function.update (Function.update (embStk weightFamilyGenerateReg S).R 111 []) 113 []) 117
          (page++(embStk weightFamilyGenerateReg S).R 117)) 118 (List.replicate page.length tick))} : Stacks 121 A).get S = T
    rw [embOvr_updR weightFamilyGenerateReg_injective,embOvr_updR weightFamilyGenerateReg_injective,
      embOvr_updR weightFamilyGenerateReg_injective,embOvr_updR weightFamilyGenerateReg_injective,embOvr_stk]
    change {S with R := (Function.update (Function.update (Function.update (Function.update S.R
      111 []) 113 []) 144 (page++S.R 144)) 145 (List.replicate page.length tick))} = T
    simp only [h144,List.append_nil]
    rfl
  have h145 : S.R 145 = [] := hfresh 118 (by simp)
  have h146 : S.R 146 = [] := hfresh 119 (by simp)
  have h147 : S.R 147 = [] := hfresh 120 (by simp)
  obtain ⟨v₂,hu₂,he₂⟩ := storeGeneratedWeightKey_exec (body := body) v₁ T page
    (by simp [T]) (by simp [T]) (by simp [T,h146]) (by simp [T,h147]) (by simp [T,h149])
  refine ⟨v₂,n₁+(14*page.length+24),hu₂.trans (hu₁.trans hui),?_,(Exec.seq he₁' he₂).cast rfl ?_⟩
  · simp only [page,batchWeightPage_length] at *
    dsimp only [generatedHaloWeightKeyCost,B,w] at *
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h144' : i = 144 <;> by_cases h145' : i = 145 <;> by_cases h149' : i = 149 <;>
      simp [T,Function.update_apply,h144',h145',h149',h144,h145,h149,page,B,w]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
