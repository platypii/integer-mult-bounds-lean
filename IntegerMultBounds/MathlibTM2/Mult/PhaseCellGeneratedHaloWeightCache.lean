module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareHaloClassControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBatchWeightCache

/-! Generate a halo class's origins from ordinary unary geometry, then generate
its numerical weight page. Origin packets and temporary headers are consumed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 121 Q A U}

def generatedHaloWeightCache : Pr P₀ 121 Q A U :=
  .seq (embProg weightCacheCoreReg Empty.elim (prepareHaloClassControls (P₀ := Empty)))
    (.seq (clearWords [111,113,115]) (.seq generatedBatchWeightCache (clearWords [94,116])))

def generatedHaloWeightCacheCost (P q s t u band a b L : ℕ) : ℕ :=
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  let B := (haloLengthGroup s t band a b L).length
  prepareHaloClassControlsCost P q s t u band a b L+2*(a+b+V)+7+
    generatedBatchWeightCacheCost P s t u q L w B+2*(w+B)+5

theorem generatedHaloWeightCache_exec (P q s t u band a b L : ℕ) [NeZero s]
    (hP : 13 ≤ P) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s)
    (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 121 Q A U) (S : Stacks 121 A)
    (hPSrc : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b)
    (hLSrc : (S.R 102).length = L) (hrows : (S.R 103).length = L)
    (hblank : ∀ k : Fin 117, k.val < 63 → (embStk weightCacheCoreReg S).R k = [])
    (hfresh : ∀ k ∈ ([(64 : Fin 121),65,94,96,104,105,106,107,108,115,116,118,119,120] : List (Fin 121)), S.R k = []) :
    let B := (haloLengthGroup s t band a b L).length
    let w := 2*q+8
    let page := batchWeightPage A w q P s t u B L (fun n => (haloGroupOrigin s t band a b L n).val)
    ∃ v' m, v'.user = v.user ∧ m ≤ generatedHaloWeightCacheCost P q s t u band a b L ∧
      Exec body generatedHaloWeightCache (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          111 []) 113 []) 117 (page++S.R 117)) 118 (List.replicate page.length tick))}) := by
  dsimp only
  let B := (haloLengthGroup s t band a b L).length
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  let origins := haloOriginPackets A V s t band a b L
  let page := batchWeightPage A w q P s t u B L (fun n => (haloGroupOrigin s t band a b L n).val)
  obtain ⟨vi,n₁,hui,hn₁,hei⟩ := prepareHaloClassControls_exec
    (body := fun p : Empty => nomatch p) P q s t u band a b L hP (NeZero.pos s) hst hu hband has hbs hL hLs hA
    (embDn weightCacheCoreReg v) (embStk weightCacheCoreReg S)
    hPSrc hq hsSrc htSrc huSrc hbSrc haSrc hbEndSrc hLSrc
    (fun k hk => hblank k (by omega)) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      all_goals exact hfresh _ (by simp [weightCacheCoreReg]))
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    weightCacheCoreReg_injective (fun p => nomatch p) hei v rfl S rfl
  let T : Stacks 121 A := {S with R := (Function.update (Function.update (Function.update
    (Function.update S.R 94 (List.replicate w tick)) 115 (List.replicate V tick))
    109 (origins++S.R 109)) 116 (List.replicate B tick))}
  have he₁' : Exec body (embProg weightCacheCoreReg Empty.elim (prepareHaloClassControls (P₀ := Empty)))
      (mk v S) n₁ (mk v₁ T) := by
    refine he₁.cast rfl ?_
    apply congrArg (mk v₁)
    change embOvr weightCacheCoreReg
      ({ { { {embStk weightCacheCoreReg S with R := Function.update (embStk weightCacheCoreReg S).R 94 (List.replicate w tick)}
        with R := Function.update (Function.update (embStk weightCacheCoreReg S).R 94 (List.replicate w tick)) 115 (List.replicate V tick)}
        with R := Function.update (Function.update (Function.update (embStk weightCacheCoreReg S).R 94 (List.replicate w tick)) 115 (List.replicate V tick)) 109 (origins++S.R 109)}
        with R := Function.update (Function.update (Function.update (Function.update (embStk weightCacheCoreReg S).R 94 (List.replicate w tick)) 115 (List.replicate V tick)) 109 (origins++S.R 109)) 116 (List.replicate B tick)} : Stacks 117 A).get S = T
    rw [embOvr_updR weightCacheCoreReg_injective,embOvr_updR weightCacheCoreReg_injective,
      embOvr_updR weightCacheCoreReg_injective,embOvr_updR weightCacheCoreReg_injective,embOvr_stk]
    rfl
  obtain ⟨v₂,hu₂,he₂⟩ := clearWords_exec (body := body) [(111 : Fin 121),113,115] (by decide) v₁ T
  let U : Stacks 121 A := {T with R := fun k => if k ∈ ([(111 : Fin 121),113,115] : List (Fin 121)) then [] else T.R k}
  have hblankU : ∀ r, (embStk weightCacheCoreReg U).R (coefficientReg r) = [] := by
    intro r
    have hr := coefficientReg_range r
    have hh := hblank (coefficientReg r) hr
    simpa [U,T,embStk,weightCacheCoreReg,Function.update_apply,Fin.ext_iff,
      show (coefficientReg r).val ≠ 94 by omega,show (coefficientReg r).val ≠ 115 by omega,
      show (coefficientReg r).val ≠ 109 by omega,show (coefficientReg r).val ≠ 116 by omega,
      show (coefficientReg r).val ≠ 111 by omega,show (coefficientReg r).val ≠ 113 by omega] using hh
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := generatedBatchWeightCache_exec (body := body)
    P s t u q L w B (fun n => (haloGroupOrigin s t band a b L n).val) v₂ U (S.R 109)
    (by simpa [U,T] using hPSrc) (by simpa [U,T] using hsSrc)
    (by simpa [U,T] using htSrc) (by simpa [U,T] using huSrc)
    (by simpa [U,T] using hq) (by simpa [U,T] using hLSrc)
    (by simpa [U,T] using hrows) (by simp [U,T])
    (by simp [U,T,B]) (by simp [U,T,origins,haloOriginPackets_eq_rows,B,V]) hblankU (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [U,T]
      all_goals exact hfresh _ (by simp)) hP (NeZero.pos s) hst hu
    (fun n _ => (haloGroupOrigin s t band a b L n).val_lt) hLs
  let W : Stacks 121 A := {U with R := (Function.update (Function.update (Function.update U.R
    109 (S.R 109)) 117 (page++U.R 117)) 118 (List.replicate (2*(B*(L*w))) tick))}
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) [(94 : Fin 121),116] (by decide) v₃ W
  refine ⟨v₄,n₁+((2*(a+b+V)+7)+(n₃+(2*(w+B)+5))),hu₄.trans (hu₃.trans (hu₂.trans (hu₁.trans hui))),?_,?_⟩
  · dsimp only [generatedHaloWeightCacheCost] at *
    dsimp only [B,w,V] at *
    omega
  · have e := Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ he₄))
    refine e.cast ?_ ?_
    · simp [U,T,W,haSrc,hbEndSrc,w,V]
      omega
    · apply congrArg (mk v₄)
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases h94 : i = 94
      · subst i
        simp [hfresh 94 (by simp)]
      by_cases h109 : i = 109
      · subst i
        simp [W,U,T,Function.update_apply]
      by_cases h115 : i = 115
      · subst i
        simp [W,U,T,Function.update_apply,hfresh 115 (by simp)]
      by_cases h116 : i = 116
      · subst i
        simp [hfresh 116 (by simp)]
      by_cases h111 : i = 111 <;> by_cases h113 : i = 113 <;>
        simp [W,U,T,Function.update_apply,h94,h109,h115,h116,h111,h113,page,B,w]


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
