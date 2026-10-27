module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightFamilyWorkspace

/-! Select the matching retained page around one actual parsed-key class execution. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 151 Q A U}

noncomputable def familyProcessHaloLengthKey (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 151 Q A U :=
  .seq loadWeightKey (.seq
    (embProg weightFamilyCoreReg Empty.elim (cachedProcessHaloLengthKey (P₀ := Empty) hR hQ)) collectWeightKey)

def familyProcessHaloLengthKeyCost (p l L s t u target rhsExp V a b : ℕ) : ℕ :=
  let B := (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length
  let w := executionWidth p l target rhsExp
  (6*L+19*V+14)+cachedConditionalHaloClassCost p l L s t u target rhsExp a b+18*(2*(B*(L*w)))+28

theorem familyProcessHaloLengthKey_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp V a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 151 Q A U) (S : Stacks 151 A) (borrowed E outputTail keyTail familyTail : List (Fin (A+4)))
    (hkey : L < 2^V) (hV : ((embStk weightFamilyCoreReg S).R 125).length = V) (hkeys : (embStk weightFamilyCoreReg S).R 126 = binSyms V L++keyTail)
    (hE : E.length = s*executionWidth p l target rhsExp) (hdst : (embStk weightFamilyCoreReg S).R 132 = E++outputTail)
    (hmasters : ∀ r ∈ groupHeaderCopies, ((embStk weightFamilyCoreReg S).R (cachedGroupLegacyReg r.1)).length =
      groupHeaderValue (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 r.1)
    (haMaster : ((embStk weightFamilyCoreReg S).R 141).length = a) (hbMaster : ((embStk weightFamilyCoreReg S).R 142).length = b)
    (hleft : ∀ k : Fin 148, k.val < 117 → (embStk weightFamilyCoreReg S).L k = [])
    (hblank : ∀ k : Fin 148, k.val < 117 → k ≠ 93 → k ≠ 110 → (embStk weightFamilyCoreReg S).R k = [])
    (hsrc : (embStk weightFamilyCoreReg S).R 110 = cstream A (executionWidth p l target rhsExp) (chirpLine s C) ++ borrowed)
    (h129 : (embStk weightFamilyCoreReg S).R 129 = []) (h133 : (embStk weightFamilyCoreReg S).R 133 = [])
    (hwidth : ((embStk weightFamilyCoreReg S).R 130).length = executionWidth p l target rhsExp)
    (hfresh : ∀ k ∈ [(131 : Fin 148),134,135,136,137,140], (embStk weightFamilyCoreReg S).R k = [])
    (hfamily : S.R 148 = weightKeyPacket (batchWeightPage A (executionWidth p l target rhsExp)
      (executionPrecision p l target rhsExp) (2^15*p) s t u
      (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length L
      (fun n => (haloGroupOrigin s t (PhaseCellBand.width p u) a b L n).val))++familyTail)
    (hcacheFresh : ∀ i ∈ ([(144 : Fin 151),145,146,147,149] : List (Fin 151)), S.R i = []) :
    let B := (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length
    let lo := haloGroupOrigin s t (PhaseCellBand.width p u) a b L
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let page := batchWeightPage A w q (2^15*p) s t u B L (fun n => (lo n).val)
    ∃ v' S' m, ∃ ys : BoundedEncodedStream A w q (interiorOutputExponent p l target rhsExp),
      v'.user = v.user ∧ m ≤ familyProcessHaloLengthKeyCost p l L s t u target rhsExp V a b ∧
      Exec body (familyProcessHaloLengthKey hR hQ) (mk v S) m (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ ys.val.length = B*L*w ∧
      (embStk weightFamilyCoreReg S').R = publishedClassR
        (Function.update (embStk weightFamilyCoreReg S).R 126 keyTail)
        (scatterRows (L*w) E (ys++(embStk weightFamilyCoreReg S).R 93)
          (haloScatterGaps s t (PhaseCellBand.width p u) a b L w)++outputTail) ∧
      S'.R 148 = familyTail ∧ S'.R 150 = (weightKeyPacket page).reverse++S.R 150 ∧
      (∀ i ∈ ([(144 : Fin 151),145,146,147,149] : List (Fin 151)), S'.R i = []) ∧
      ∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore (lo n) L)
        (publishedCellRead q w (0 : ZMod s) (S'.R 132)) x (1/(2 : ℝ)^target) := by
  dsimp only
  let B := (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length
  let lo := haloGroupOrigin s t (PhaseCellBand.width p u) a b L
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let page := batchWeightPage A w q (2^15*p) s t u B L (fun n => (lo n).val)
  obtain ⟨v₁,hu₁,he₁⟩ := loadWeightKey_exec (body := body) v S page familyTail hfamily hcacheFresh
  let T := loadedWeightKeyBank S page familyTail
  have hlow (i : Fin 148) (hi : i.val < 144) :
      (embStk weightFamilyCoreReg T).R i = (embStk weightFamilyCoreReg S).R i :=
    loadedWeightKeyBank_low S page familyTail i hi
  have hlen : page.length = 2*(B*(L*w)) := by simp [page]
  have hpage₁ : (embStk weightFamilyCoreReg T).R 144 = page := by
    simp [T,loadedWeightKeyBank,embStk,weightFamilyCoreReg]
  obtain ⟨vi,N,m₂,ys,hui,hm₂,hei,hii,hoi,hli,hylen,hframe,hcacheFrame,herror⟩ := cachedProcessHaloLengthKey_spec
    (body := fun p : Empty => nomatch p) hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hL hLs hpad
    C hC x hx (embDn weightFamilyCoreReg v₁) (embStk weightFamilyCoreReg T) borrowed E outputTail keyTail []
    hkey (by rw [hlow 125 (by decide)]; exact hV) (by rw [hlow 126 (by decide)]; exact hkeys)
    hE (by rw [hlow 132 (by decide)]; exact hdst) (by
      intro r hr
      rw [hlow (cachedGroupLegacyReg r.1) r.1.isLt]
      exact hmasters r hr)
    (by rw [hlow 141 (by decide)]; exact haMaster) (by rw [hlow 142 (by decide)]; exact hbMaster)
    hleft (by intro k hk hk93 hk110; rw [hlow k (by omega)]; exact hblank k hk hk93 hk110)
    (by rw [hlow 110 (by decide)]; exact hsrc) (by rw [hlow 129 (by decide)]; exact h129)
    (by rw [hlow 133 (by decide)]; exact h133) (by rw [hlow 130 (by decide)]; exact hwidth) (by
      intro k hk
      have hk144 : k.val < 144 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hlow k hk144]
      exact hfresh k hk)
    (by intro _; simpa only [List.append_nil] using hpage₁)
    (by intro _; simp [T,loadedWeightKeyBank,embStk,weightFamilyCoreReg,hlen,B,w])
    (by intro _; simp [T,loadedWeightKeyBank,embStk,weightFamilyCoreReg,hcacheFresh 146 (by simp)])
    (by intro _; simp [T,loadedWeightKeyBank,embStk,weightFamilyCoreReg,hcacheFresh 147 (by simp)])
  obtain ⟨v₂,U,he₂,hv₂,hu₂,hproj,hoff⟩ := exec_emb (body' := body) (ι := Empty.elim)
    weightFamilyCoreReg_injective (fun p => nomatch p) hei v₁ rfl T rfl
  have hread (i : Fin 148) : U.R (weightFamilyCoreReg i) = N.R i :=
    congrArg (fun S : Stacks 148 A => S.R i) hproj
  have hpage₂ : U.R 144 = page := by
    have h := (hread 144).trans (hcacheFrame 144 (by decide)).2
    simpa [T,loadedWeightKeyBank,embStk,weightFamilyCoreReg] using h
  have hclock : U.R 145 = List.replicate page.length tick := by
    have h := (hread 145).trans (hcacheFrame 145 (by decide)).2
    simpa [T,loadedWeightKeyBank,embStk,weightFamilyCoreReg] using h
  have h146 : U.R 146 = [] := by
    have h := (hread 146).trans (hcacheFrame 146 (by decide)).2
    simpa [T,loadedWeightKeyBank,embStk,weightFamilyCoreReg,hcacheFresh 146 (by simp)] using h
  have h147 : U.R 147 = [] := by
    have h := (hread 147).trans (hcacheFrame 147 (by decide)).2
    simpa [T,loadedWeightKeyBank,embStk,weightFamilyCoreReg,hcacheFresh 147 (by simp)] using h
  have hheader : U.R 149 = blank::List.replicate page.length tick := by
    simpa [T,loadedWeightKeyBank] using (hoff 149 (weightFamilyCoreReg_off 149 (by decide))).2
  have hqueue : U.R 148 = familyTail := by
    simpa [T,loadedWeightKeyBank] using (hoff 148 (weightFamilyCoreReg_off 148 (by decide))).2
  have hcomplete : U.R 150 = S.R 150 := by
    simpa [T,loadedWeightKeyBank] using (hoff 150 (weightFamilyCoreReg_off 150 (by decide))).2
  obtain ⟨v₃,hu₃,he₃⟩ := collectWeightKey_exec (body := body) v₂ U page hpage₂ hclock hheader h146 h147
  let F := collectedWeightKeyBank U page
  refine ⟨v₃,F,(8*page.length+9)+(m₂+(10*page.length+19)),ys,
    hu₃.trans (hu₂.trans (hui.trans hu₁)),?_,Exec.seq he₁ (Exec.seq he₂ he₃),?_,?_,?_,hylen,?_,?_,?_,?_,?_⟩
  · dsimp only [familyProcessHaloLengthKeyCost]
    rw [hlen]
    dsimp only [B,q,w] at hm₂ ⊢
    omega
  · exact (congrArg (fun S : Stacks 148 A => S.inp) hproj).trans hii
  · exact (congrArg (fun S : Stacks 148 A => S.out) hproj).trans hoi
  · funext i
    by_cases hi : i.val < 148
    · let j : Fin 148 := ⟨i.val,hi⟩
      have heq : weightFamilyCoreReg j = i := Fin.ext rfl
      have h := (congrArg (fun S : Stacks 148 A => S.L j) hproj).trans (congrFun hli j)
      simpa only [F,collectedWeightKeyBank,embStk_L,heq,T,loadedWeightKeyBank] using h
    · exact (hoff i (weightFamilyCoreReg_off i (by omega))).1
  · change (embStk weightFamilyCoreReg (collectedWeightKeyBank U page)).R = _
    rw [collectedWeightKeyBank_projectR,congrArg (fun S : Stacks 148 A => S.R) hproj,hframe]
    rw [hlow 93 (by decide),loadedWeightKeyBank_project]
    exact weightFamily_release_published _ _ _ _ _
      (by simpa [embStk,weightFamilyCoreReg] using hcacheFresh 144 (by simp))
      (by simpa [embStk,weightFamilyCoreReg] using hcacheFresh 145 (by simp))
  · simpa [F,collectedWeightKeyBank] using hqueue
  · simp only [F,collectedWeightKeyBank,Function.update_self,hcomplete]
    rfl
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    all_goals simp [F,collectedWeightKeyBank,h146,h147]
  · have h132 : F.R 132 = N.R 132 := by
      simpa [F,collectedWeightKeyBank,weightFamilyCoreReg] using hread 132
    intro n
    rw [h132]
    exact herror n

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
