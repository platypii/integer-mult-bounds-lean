module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyHaloLengthKeyTraversal

/-! A single counted loop executes all selected length classes. Its invariant
keeps earlier classes' physical reads unchanged, so the final accuracy has no
key-count factor. The borrowed key/output suffixes remain outside loop ownership. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 151 Q A U}

theorem familyHaloLengthKeyLoop_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp V a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (keys : List ℕ) (hnodup : keys.Nodup)
    (hbounds : ∀ L ∈ keys, 0 < L ∧ L ≤ s ∧ L+L ≤ 2^l+1 ∧ L < 2^V)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 151 Q A U) (S : Stacks 151 A) (borrowed E outputTail keyTail familyTail : List (Fin (A+4)))
    (hE : E.length = s*executionWidth p l target rhsExp) (hdst : S.R 132 = E++outputTail)
    (hkeys : S.R 126 = lengthKeyPackets A V keys++keyTail)
    (hcount : S.R 127 = List.replicate keys.length tick)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) V
      (executionWidth p l target rhsExp) (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) (weightFamilyLegacyBank S))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hfamily : S.R 148 = weightKeyFamily (haloWeightKeyPages A (executionWidth p l target rhsExp)
      (executionPrecision p l target rhsExp) (2^15*p) s t u (PhaseCellBand.width p u) a b keys)++familyTail)
    (hcacheFresh : ∀ i ∈ ([(144 : Fin 151),145,146,147,149] : List (Fin 151)), S.R i = [])
    (hcomplete : S.R 150 = [])
    (hflag : v.flag = keys.head?.isSome) :
    let band := PhaseCellBand.width p u
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' S' n, ∃ E' : List (Fin (A+4)), v'.user = v.user ∧
      n ≤ familyHaloLengthKeyLoopCost A p l s t u target rhsExp V a b keys ∧
      Exec body (familyHaloLengthKeyLoop hR hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ E'.length = s*w ∧
      (weightFamilyLegacyBank S').R = keyLoopR (weightFamilyLegacyBank S).R keyTail [] (E'++outputTail) ∧
      S'.R 148 = S.R 148 ∧ S'.R 150 = [] ∧
      (∀ i ∈ ([(144 : Fin 151),145,146,147,149] : List (Fin 151)), S'.R i = []) ∧
      (∀ L ∈ keys, ∀ n : Fin (haloLengthGroup s t band a b L).length,
        PhaseCellInterface.ErrorOn (publishedCellCore (haloGroupOrigin s t band a b L n) L)
          (publishedCellRead q w (0 : ZMod s) (S'.R 132)) x (1/(2 : ℝ)^target)) ∧
      (∀ K, K ∉ keys → ∀ n : Fin (haloLengthGroup s t band a b K).length, ∀ j ∈ publishedCellCore
        (haloGroupOrigin s t band a b K n) K,
        publishedCellRead q w (0 : ZMod s) (S'.R 132) j = publishedCellRead q w (0 : ZMod s) (S.R 132) j) ∧
      (EncodedRange A w q (interiorOutputExponent p l target rhsExp) E →
        EncodedRange A w q (interiorOutputExponent p l target rhsExp) E') := by
  dsimp only
  obtain ⟨v₁,T,n,E',hu₁,hn,he₁,hi,ho,hl,hE',hframe,hs,hc,hfresh,herror,hkeep,hbound⟩ :=
    familyHaloLengthKeyTraversal_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs
      keys hnodup hbounds C hC x hx v S borrowed E outputTail keyTail familyTail hE hdst hkeys hcount
      hready haMaster hbMaster hfamily hcacheFresh hflag
  let pages := haloWeightKeyPages A (executionWidth p l target rhsExp)
    (executionPrecision p l target rhsExp) (2^15*p) s t u (PhaseCellBand.width p u) a b keys
  obtain ⟨v₂,hu₂,he₂⟩ := restoreWeightKeyFamily_exec (body := body) v₁ T pages familyTail
    (by simpa [hcomplete,pages] using hc) hs
  let F : Stacks 151 A := {T with R := (Function.update (Function.update T.R
    148 (weightKeyFamily pages++familyTail)) 150 [])}
  have hlow (i : Fin 151) (hi : i.val < 148) : F.R i = T.R i := by
    have h148 : i ≠ 148 := by intro h; subst i; norm_num at hi
    have h150 : i ≠ 150 := by intro h; subst i; norm_num at hi
    simp [F,h148,h150]
  have hlegacy : weightFamilyLegacyBank F = weightFamilyLegacyBank T := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    exact hlow (weightFamilyCoreReg (cachedGroupLegacyReg i)) (by
      dsimp [weightFamilyCoreReg,cachedGroupLegacyReg]; omega)
  refine ⟨v₂,F,n+(2*(weightKeyFamily pages).length+2),E',hu₂.trans hu₁,?_,
    Exec.seq he₁ he₂,hi,ho,hl,hE',?_,?_,?_,?_,?_,?_,hbound⟩
  · dsimp only [familyHaloLengthKeyLoopCost]
    dsimp only [pages] at *
    omega
  · rw [hlegacy]
    exact hframe
  · simpa [F,pages] using hfamily.symm
  · simp [F]
  · intro i hi
    have hi148 : i ≠ 148 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
    have hi150 : i ≠ 150 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [F,hi148,hi150] using hfresh i hi
  · simpa only [hlow 132 (by decide)] using herror
  · simpa only [hlow 132 (by decide)] using hkeep

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
