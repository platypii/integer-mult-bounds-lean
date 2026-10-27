module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCacheWeightPage
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Generate a numerical weight page once, then retain it for replay. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 121 Q A U}

def weightCacheCoreReg (i : Fin 117) : Fin 121 := ⟨i.val,by omega⟩

theorem weightCacheCoreReg_injective : Function.Injective weightCacheCoreReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 121 => k.val) h)

def generatedWeightCache : Pr P 121 Q A U :=
  .seq (embProg weightCacheCoreReg Empty.elim (retainedWeightPage (P₀ := Empty))) cacheWeightPage

theorem generatedWeightCache_exec {V w q Pbits s t u L lo : ℕ} (st : TblSt 48 A)
    (hready : WeightReady A V Pbits q s t u L st)
    (hP : 13 ≤ Pbits) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hlo : lo < s) (hL : L ≤ s)
    (hV : V = weightWorkspaceWidth Pbits q w t u)
    (v : HS 121 Q A U) (S : Stacks 121 A) (tail : List (Fin (A+4)))
    (hS : tblHolds coefficientReg (embStk weightCacheCoreReg S)
      (tblRho V (List.replicate V tick) (List.replicate w tick) st))
    (hwidth : (S.R 94).length = w) (hrows : (S.R 103).length = L)
    (hcount : (S.R 115).length = V) (hrow : (S.R 64).length = L*w)
    (hsrc : S.R 109 = binSyms V lo++tail)
    (hfresh : ∀ k ∈ ([(96 : Fin 121),104,105,106,108,118,119,120] : List (Fin 121)), S.R k = []) :
    ∃ v' S' m st', v'.user = v.user ∧
      m ≤ retainedWeightPageCost V w Pbits L+20*(L*w)+14 ∧
      Exec body generatedWeightCache (mk v S) m (mk v' S') ∧
      WeightReady A V Pbits q s t u L st' ∧
      tblHolds coefficientReg (embStk weightCacheCoreReg S')
        (tblRho V (List.replicate V tick) (List.replicate w tick) st') ∧
      S'.R 117 = weightPage A w q Pbits s t u lo L++S.R 117 ∧
      S'.R 118 = List.replicate (2*(L*w)) tick ∧
      S'.R 109 = tail ∧ S'.R 110 = S.R 110 ∧
      S'.R 119 = [] ∧ S'.R 120 = [] ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ i, 63 ≤ i.val → i ≠ 109 → i ≠ 117 → i ≠ 118 → S'.R i = S.R i := by
  obtain ⟨vi,E,m,st',hui,hm,he,hr,hh,hpacket,hpage,hin,hout,hleft,hframe⟩ :=
    retainedWeightPage_exec (body := fun p : Empty => nomatch p) st hready hP hs hst hu hlo hL hV
      (embDn weightCacheCoreReg v) (embStk weightCacheCoreReg S) tail hS hwidth hrows hcount hsrc
      (by intro k hk; exact hfresh (weightCacheCoreReg k) (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp [weightCacheCoreReg]))
  obtain ⟨v₁,M,he₁,hv₁,hu₁,hproj,hoff⟩ := exec_emb (body' := body) (ι := Empty.elim)
    weightCacheCoreReg_injective (fun p => nomatch p) he v rfl S rfl
  have hread (i : Fin 117) : M.R (weightCacheCoreReg i) = E.R i :=
    congrArg (fun T => T.R i) hproj
  have hhigh (i : Fin 121) (hi : 117 ≤ i.val) : M.R i = S.R i := by
    exact (hoff i (by intro j hj; have hv := congrArg Fin.val hj; dsimp [weightCacheCoreReg] at hv; omega)).2
  have hlen : (weightPage A w q Pbits s t u lo L).length = 2*(L*w) := by
    simp [weightPage,outputWeightRow,inputWeightRow]
    omega
  obtain ⟨v₂,hu₂,he₂⟩ := cacheWeightPage_exec (body := body) v₁ M
    (weightPage A w q Pbits s t u lo L) (S.R 110) (L*w) hlen
    (by change M.R (weightCacheCoreReg 110) = _; rw [hread 110]; exact hpage)
    (by change (M.R (weightCacheCoreReg 64)).length = _; rw [hread 64,hframe 64 (by decide) (by decide) (by decide)]; exact hrow)
    (by rw [hhigh 118 (by decide)]; exact hfresh 118 (by simp))
    (by rw [hhigh 119 (by decide)]; exact hfresh 119 (by simp))
    (by rw [hhigh 120 (by decide)]; exact hfresh 120 (by simp))
  let T : Stacks 121 A := {M with R := (Function.update (Function.update (Function.update M.R
    110 (S.R 110)) 117 (weightPage A w q Pbits s t u lo L++M.R 117))
      118 (List.replicate (2*(L*w)) tick))}
  refine ⟨v₂,T,m+(20*(L*w)+14),st',hu₂.trans (hu₁.trans hui),by omega,
    Exec.seq he₁ he₂,hr,?_,?_,by simp [T],?_,by simp [T],?_,?_,?_,?_,?_,?_⟩
  · intro r
    have hlow : weightCacheCoreReg (coefficientReg r) ≠ (117 : Fin 121) ∧
        weightCacheCoreReg (coefficientReg r) ≠ (118 : Fin 121) ∧
        weightCacheCoreReg (coefficientReg r) ≠ (110 : Fin 121) := by
      have hlt := coefficientReg_range r
      refine ⟨?_,?_,?_⟩ <;> intro he
      all_goals have hv := congrArg (fun k : Fin 121 => k.val) he
      all_goals dsimp only [weightCacheCoreReg] at hv
      all_goals omega
    simpa only [T,embStk_R,Function.update_of_ne hlow.1,
      Function.update_of_ne hlow.2.1,Function.update_of_ne hlow.2.2,hread] using hh r
  · simp [T,hhigh 117 (by decide)]
  · simpa [T,weightCacheCoreReg] using (hread 109).trans hpacket
  · simpa [T,hhigh 119 (by decide)] using hfresh 119 (by simp)
  · simpa [T,hhigh 120 (by decide)] using hfresh 120 (by simp)

  · exact (congrArg Stacks.inp hproj).trans hin
  · exact (congrArg Stacks.out hproj).trans hout
  · funext i
    change M.L i = S.L i
    by_cases hi : i.val < 117
    · let j : Fin 117 := ⟨i.val,hi⟩
      have heq : weightCacheCoreReg j = i := Fin.ext rfl
      have hview := congrArg (fun T : Stacks 117 A => T.L j) hproj
      rw [← heq]
      exact hview.trans (congrFun hleft j)
    · apply (hoff i ?_).1
      intro j hj
      have hv := congrArg (fun k : Fin 121 => k.val) hj
      dsimp [weightCacheCoreReg] at hv
      omega
  · intro i hi h109 h117 h118
    change Function.update (Function.update (Function.update M.R 110 (S.R 110))
      117 (weightPage A w q Pbits s t u lo L++M.R 117)) 118
        (List.replicate (2*(L*w)) tick) i = S.R i
    rw [Function.update_of_ne h118,Function.update_of_ne h117]
    by_cases h110 : i = 110
    · subst i; exact Function.update_self _ _ _
    rw [Function.update_of_ne h110]
    by_cases hsmall : i.val < 117
    · let j : Fin 117 := ⟨i.val,hsmall⟩
      have heq : weightCacheCoreReg j = i := Fin.ext rfl
      rw [← heq,hread j]
      exact hframe j hi (by intro he; apply h109; rw [← heq,he]; rfl)
        (by intro he; apply h110; rw [← heq,he]; rfl)
    · exact hhigh i (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
