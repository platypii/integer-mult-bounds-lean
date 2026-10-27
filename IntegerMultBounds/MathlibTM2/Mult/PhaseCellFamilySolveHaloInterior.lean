module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareHaloWeightFamily
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyHaloLengthKeyLoopSpec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunGeneratedHaloKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseKeyRuntime

/-! Execute a complete interior pass using a retained generated weight family.
Only the ambient publication changes; the family is available for the next pass. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 151 Q A U}

noncomputable def familySolveHaloInterior (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 151 Q A U :=
  .seq initializeFamilyHaloKeys (.seq (.act (peekR 127))
    (.seq (familyHaloLengthKeyLoop hR hQ) (clearWords [125,130])))

def familySolveHaloInteriorCost (A p l s t u target rhsExp a b : ℕ) : ℕ :=
  let band := PhaseCellBand.width p u
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let V := weightWorkspaceWidth P q w t u
  initializeHaloLengthKeysCost P N q l s t u band a b+1+
    familyHaloLengthKeyLoopCost A p l s t u target rhsExp V a b (haloLengthKeys s t band a b)+2*(V+w)+5

theorem familySolveHaloInterior_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 151 Q A U) (S : Stacks 151 A) (borrowed E outputTail familyTail : List (Fin (A+4)))
    (hE : E.length = s*executionWidth p l target rhsExp) (hdst : S.R 132 = E++outputTail)
    (h127 : S.R 127 = []) (h138 : S.R 138 = [])
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) (weightFamilyLegacyBank S))
    (hfamily : S.R 148 = weightKeyFamily (haloWeightKeyPages A (executionWidth p l target rhsExp)
      (executionPrecision p l target rhsExp) (2^15*p) s t u (PhaseCellBand.width p u) a b
      (haloLengthKeys s t (PhaseCellBand.width p u) a b))++familyTail)
    (hcache : ∀ i ∈ ([(144 : Fin 151),145,146,147,149] : List (Fin 151)), S.R i = [])
    (h150 : S.R 150 = []) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' n, ∃ E' : List (Fin (A+4)), v'.user = v.user ∧
      n ≤ familySolveHaloInteriorCost A p l s t u target rhsExp a b ∧ E'.length = s*w ∧
      Exec body (familySolveHaloInterior hR hQ) (mk v S) n
        (mk v' { S with R := Function.update S.R 132 (E'++outputTail) }) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
        (publishedCellRead q w (0 : ZMod s) (E'++outputTail)) x (1/(2 : ℝ)^target) ∧
      (EncodedRange A w q (interiorOutputExponent p l target rhsExp) E →
        EncodedRange A w q (interiorOutputExponent p l target rhsExp) E') := by
  dsimp only
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let V := weightWorkspaceWidth P q w t u
  let keys := haloLengthKeys s t band a b
  let packets := haloPositiveLengthPackets A V s t band a b
  have hw : 2*q+8 = w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  have hP : 13 ≤ P := by dsimp [P]; omega
  have h125 : (weightFamilyLegacyBank S).R 125 = [] := List.eq_nil_of_length_eq_zero hready.keyWidth
  have h130 : (weightFamilyLegacyBank S).R 130 = [] := List.eq_nil_of_length_eq_zero hready.wordWidth
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := initializeFamilyHaloKeys_exec (body := body)
    P N q l s t u band a b hP (NeZero.pos s) hst hu hband has hbs (by omega) v S
    (cstream A w (chirpLine s C)++borrowed) hready haMaster hbMaster h127 h138
  simp only [hw] at he₁
  let T : Stacks 151 A := {S with R := initializedFamilyKeyR S.R V w keys.length packets}
  have hr : LengthKeyReady P N q l s t u band V w
      (cstream A w (chirpLine s C)++borrowed) (weightFamilyLegacyBank T) := hready.initialized_family packets
  have hwide : s < 2^V := by
    obtain ⟨hb,_⟩ := weightWorkspaceWidth_control (q := q) (w := w) hP (NeZero.pos s) hst hu hband
    dsimp only [V]
    nlinarith only [hb,hst,NeZero.pos s]
  have hbounds : ∀ L ∈ keys, 0 < L ∧ L ≤ s ∧ L+L ≤ 2^l+1 ∧ L < 2^V := by
    intro L hL
    have hpos : 0 < L := of_decide_eq_true (List.mem_filter.mp hL).2
    have hc := List.mem_dedup.mp (List.mem_filter.mp hL).1
    have huniform := haloLengthCandidates_uniform hst band a b hc
    have hdiv := Nat.div_le_self s (t-s)
    have hb := PhaseCellBand.width_pos p u
    have hLs : L ≤ s := by dsimp only [band] at *; omega
    exact ⟨hpos,hLs,haloLengthKeys_pad hst band a b l hpad L hL,hLs.trans_lt hwide⟩
  have hp₁ := Exec.act (body := body) (peekR 127) (mk v₁ T)
  have hc : T.R 127 = List.replicate keys.length tick := by simp [T,initializedFamilyKeyR]
  rw [peekR_run,hc,count_head_isSome keys] at hp₁
  have flagUpdate (flag : Bool) : ({v₁ with flag := flag} : HS 151 Q A U).flag = flag := rfl
  obtain ⟨v₂,W,n₂,E',hu₂,hn₂,he₂,hi,ho,hl,hlen,hframe,h148,h150',hfresh,herror,hkeep,hbound⟩ :=
    familyHaloLengthKeyLoop_spec (body := body) (p := p) (l := l) (s := s) (t := t) (u := u)
      (target := target) (rhsExp := rhsExp) (V := V) (a := a) (b := b) hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs
      keys (haloLengthKeys_nodup s t band a b) hbounds C hC x hx {v₁ with flag := keys.head?.isSome} T
      borrowed E outputTail (S.R 126) familyTail hE (by simpa [T,initializedFamilyKeyR] using hdst)
      (by simp [T,initializedFamilyKeyR,packets,lengthKeyPackets,haloPositiveLengthPackets,keys]) hc hr
      (by simpa [T,initializedFamilyKeyR] using haMaster) (by simpa [T,initializedFamilyKeyR] using hbMaster)
      (by simpa [T,initializedFamilyKeyR] using hfamily) (by
        intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl
        all_goals simpa [T,initializedFamilyKeyR] using hcache _ (by simp))
      (by simpa [T,initializedFamilyKeyR] using h150) (flagUpdate _)
  have h125W : (W.R 125).length = V := by
    have hh := congrArg (fun R => (R 125).length) hframe
    simpa [keyLoopR,T,initializedFamilyKeyR,weightFamilyLegacyBank,embStk,weightFamilyCoreReg,cachedGroupLegacyReg] using hh
  have h130W : (W.R 130).length = w := by
    have hh := congrArg (fun R => (R 130).length) hframe
    simpa [keyLoopR,T,initializedFamilyKeyR,weightFamilyLegacyBank,embStk,weightFamilyCoreReg,cachedGroupLegacyReg] using hh
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [(125 : Fin 151),130] (by decide) v₂ W
  let F : Stacks 151 A := {W with R := fun i => if i ∈ ([(125 : Fin 151),130] : List (Fin 151)) then [] else W.R i}
  have hlegacy : (weightFamilyLegacyBank F).R = Function.update (weightFamilyLegacyBank S).R 132 (E'++outputTail) := by
    have hh := released_keyLoop_initialized (weightFamilyLegacyBank S).R V w keys.length packets (E'++outputTail) h125 h127 h130
    have hreleased : (weightFamilyLegacyBank F).R = releasedKeyRuntimeR (weightFamilyLegacyBank W).R := by
      funext i
      simp [F,weightFamilyLegacyBank,embStk,weightFamilyCoreReg,cachedGroupLegacyReg,releasedKeyRuntimeR,Fin.ext_iff]
      rfl
    have ht := congrArg (fun Z : Stacks 144 A => Z.R) (initializedFamilyKeyR_legacy S V w keys.length packets)
    change (weightFamilyLegacyBank T).R = initializedKeyRuntimeR (weightFamilyLegacyBank S).R V w keys.length packets at ht
    rw [hreleased,hframe,ht]
    exact hh
  have hfinal : F = {S with R := Function.update S.R 132 (E'++outputTail)} := by
    refine Stacks.ext hi ho hl ?_
    funext i
    by_cases hi144 : i.val < 144
    · have hh := congrArg (fun R => R (⟨i.val,hi144⟩ : Fin 144)) hlegacy
      simpa [weightFamilyLegacyBank,embStk,weightFamilyCoreReg,cachedGroupLegacyReg,Function.update_apply,Fin.ext_iff] using hh
    · have hic : i = 144 ∨ i = 145 ∨ i = 146 ∨ i = 147 ∨ i = 148 ∨ i = 149 ∨ i = 150 := by omega
      rcases hic with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (simpa [F] using (hfresh 144 (by simp)).trans (hcache 144 (by simp)).symm)
        | (simpa [F] using (hfresh 145 (by simp)).trans (hcache 145 (by simp)).symm)
        | (simpa [F] using (hfresh 146 (by simp)).trans (hcache 146 (by simp)).symm)
        | (simpa [F] using (hfresh 147 (by simp)).trans (hcache 147 (by simp)).symm)
        | (simpa [F] using (hfresh 149 (by simp)).trans (hcache 149 (by simp)).symm)
        | (simpa [F,T,initializedFamilyKeyR] using h148)
        | (simpa [F,h150] using h150')
  have h132 : W.R 132 = E'++outputTail := by
    have hh := congrArg (fun R => R 132) hframe
    simpa [keyLoopR,weightFamilyLegacyBank,embStk,weightFamilyCoreReg,cachedGroupLegacyReg] using hh
  refine ⟨v₃,n₁+(1+(n₂+(2*(V+w)+5))),E',hu₃.trans (hu₂.trans hu₁),?_,hlen,
    (Exec.seq he₁ (Exec.seq hp₁ (Exec.seq he₂ he₃))).cast ?_ (congrArg (mk v₃) hfinal),?_,hbound⟩
  · dsimp only [familySolveHaloInteriorCost]
    dsimp only [P,N,q,w,band,V,keys] at *
    omega
  · simp [h125W,h130W]
  · apply haloLengthKeys_errorOn hst band a b _ x _
    simpa only [h132] using herror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
