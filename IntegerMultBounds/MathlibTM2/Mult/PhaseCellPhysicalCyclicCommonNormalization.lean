module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicNormalizationLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicNormalizationControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhysicalCyclicNormalization
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizePublishCyclicInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWithCyclicNormalizationControls

/-! Physical common-width output shares the computed rounding bank and restores routing metadata. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 280 Q A U}

def physicalCyclicCommonNormalization : Pr P 280 Q A U :=
  withCyclicNormalizationControls
    (normalizePublishCyclicInterval cyclicRoundReg cyclicRoundPorts
      264 265 266 267 268 117 119 95 94 277 147 273 274 275 276 278 279 0)

def physicalCyclicCommonNormalizationCost (p q a n W : ℕ) : ℕ :=
  physicalCyclicNormalizationCost p q a n+
    publishRoundedScalarCost (cyclicNormalizationWidth (2^15*p) q) p W n

theorem physicalCyclicCommonNormalization_exec (hA : 4 ≤ A) (p q a n W : ℕ) (hW : 2*p+13 ≤ W)
    (hpq : p ≤ q) (hsize : q-p+inverseNormalizationShift p+(2*p+13) ≤ 2*q+8)
    {s : ℕ} [NeZero s] (ha : a < s) (hn : n ≤ s)
    (D : ZMod s → GaussianInt) (z : ZMod s → ℂ) (e : ℝ) (he : e ≤ 1)
    (hz : ∀ i ∈ cyclicPrincipalVertices s a n, ‖z i‖ ≤ 4*(2 : ℝ)^(p+8))
    (oldTail tail : List (Fin (A+4)))
    (hgood : PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (cyclicIntervalRead q (2*q+8) a (cstream A (2*q+8) (cyclicInterval a n D)++oldTail)) z e)
    (v : HS 280 Q A U) (S : Stacks 280 A)
    (hP : (S.R 117).length = 2^15*p) (hq : (S.R 119).length = q)
    (haMaster : (S.R 144).length = a) (hleft : (S.R 145).length = a+min n (s-a))
    (hright : (S.R 146).length = n-min n (s-a))
    (hfresh : ∀ k ∈ ([(0 : Fin 280),1,2,3,4,7,94,95]), S.R k = [])
    (hnew : ∀ k : Fin 280, 224 ≤ k.val → k ≠ 279 → S.R k = [])
    (hwide : (S.R 279).length = W)
    (hsrc : S.R 147 = cstream A (2*q+8) (cyclicInterval a n D)++tail) :
    ∃ v' m, v'.user = v.user ∧ m ≤ physicalCyclicCommonNormalizationCost p q a n W ∧
      Exec body physicalCyclicCommonNormalization (mk v S) m
        (mk v' {S with R := (Function.update S.R 147
          (cstream A W (cyclicInterval a n
            (fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i)))++tail))}) ∧
      (∀ x ∈ cyclicInterval a n
        (fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i)), Fits (2*p+13) x) ∧
      PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
        (cyclicIntervalRead p W a
          (cstream A W (cyclicInterval a n
            (fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i)))++tail))
        (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*z i)
        (2/(2 : ℝ)^p+e/(2 : ℝ)^inverseNormalizationShift p) := by
  let B := cyclicNormalizationWidth (2^15*p) q
  let F := cyclicNormalizationPrepared (2^15*p) q n S
  let core : Pr P 280 Q A U := normalizePublishCyclicInterval cyclicRoundReg cyclicRoundPorts
    264 265 266 267 268 117 119 95 94 277 147 273 274 275 276 278 279 0
  let coreCost := (1+(2^15*p+q)*(4*B+10)+2*(8*B+12))+25*(4*B+4)+2*(8*B+8)+2+
    (18+(4*Nat.size (4*p)+31))*tblC B 0+
    roundPackedKeyCost B (2*q+8) (2*p+13) n (2*q+8) n+
    publishRoundedScalarCost B p W n+(2*(25*B)+2*25+1)
  let ys := cstream A W (cyclicInterval a n
    (fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i)))++tail
  have hregSep (r : TblR 25) (k : Fin 280) (hk : k.val < 224 ∨ 264 ≤ k.val) : cyclicRoundReg r ≠ k := by
    intro heq
    have hv := congrArg Fin.val heq
    have hr := cyclicRoundReg_range r
    rcases hk with hk | hk <;> omega
  have hfreshF (k : Fin 280) (hk : 264 ≤ k.val) (hne : k ≠ 279) : F.R k = [] := by
    have h249 : k ≠ 249 := by intro heq; subst k; norm_num at hk
    have h94 : k ≠ 94 := by intro heq; subst k; norm_num at hk
    have h95 : k ≠ 95 := by intro heq; subst k; norm_num at hk
    simp [F,cyclicNormalizationPrepared,h249,h94,h95,hnew k (by omega) hne]
  have hblank : ∀ r : TblR 25, r ≠ .wr → F.R (cyclicRoundReg r) = [] := by
    intro r hr
    have h249 : cyclicRoundReg r ≠ 249 := cyclicRoundReg_injective.ne hr
    have h94 : cyclicRoundReg r ≠ 94 := hregSep r 94 (by decide)
    have h95 : cyclicRoundReg r ≠ 95 := hregSep r 95 (by decide)
    have h279 : cyclicRoundReg r ≠ 279 := hregSep r 279 (by decide)
    simpa [F,cyclicNormalizationPrepared,h249,h94,h95] using
      hnew (cyclicRoundReg r) (cyclicRoundReg_range r).1 h279
  have hroom := cyclicNormalizationWidth_room p q
  have hrun : ∀ v₀ : HS 280 Q A U, ∃ v' m, v'.user = v₀.user ∧ m ≤ coreCost ∧
      Exec body core (mk v₀ F) m (mk v' {F with R := Function.update F.R 147 ys}) := by
    intro v₀
    obtain ⟨v',m,hu,hm,hexec,_⟩ := normalizePublishCyclicInterval_exec (body := body) hA
      cyclicRoundReg cyclicRoundReg_injective cyclicRoundPorts cyclicRoundPorts_injective
      264 265 266 267 268 117 119 95 94 277 147 273 274 275 276
      (by intro r; exact hregSep r 264 (by decide))
      (by intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl <;> decide)
      (by decide)
      (by intro k hk r
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals apply hregSep r; decide +kernel)
      278 279 0 (by decide)
      (by intro k hk r
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals apply hregSep r; decide +kernel)
      B p q W hW (List.replicate B tick) (by simp) hroom.1 hroom.2.1 hroom.2.2 hpq hsize
      a n ha hn D z e he hz oldTail tail hgood v₀ F
      (by simp [F,cyclicNormalizationPrepared,cyclicRoundReg,B])
      (by simpa [F,cyclicNormalizationPrepared] using hP)
      (by simpa [F,cyclicNormalizationPrepared] using hq)
      (by simp [F,cyclicNormalizationPrepared]) (by simp [F,cyclicNormalizationPrepared]) hblank
      (by intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl <;> exact hfreshF _ (by decide) (by decide))
      (by intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hfreshF _ (by decide) (by decide))
      (by intro i; exact hfreshF (cyclicRoundPorts i) (by fin_cases i <;> decide) (by fin_cases i <;> decide))
      (by simpa [F,cyclicNormalizationPrepared] using hwide)
      (by intro k hk
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hfreshF _ (by decide) (by decide)
          · simpa [F,cyclicNormalizationPrepared] using hfresh 0 (by simp)
          all_goals exact hfreshF _ (by decide) (by decide))
      (by simpa [F,cyclicNormalizationPrepared] using hsrc)
    have hc : binaryHeaderQueueCost F.R B [117,119] =
        1+(2^15*p+q)*(4*B+10)+2*(8*B+12) := by
      simp [binaryHeaderQueueCost,F,cyclicNormalizationPrepared,hP,hq]
      ring
    refine ⟨v',m,hu,?_,hexec⟩
    simpa only [coreCost,hc] using hm
  obtain ⟨v',m,hu,hm,hexec⟩ := withCyclicNormalizationControls_exec (body := body)
    core (2^15*p) q a n s coreCost ys v S hP hq haMaster hleft hright
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | exact hnew 249 (by decide) (by decide) | exact hfresh _ (by simp)) hrun
  refine ⟨v',m,hu,?_,hexec,?_,?_⟩
  · dsimp only [physicalCyclicCommonNormalizationCost,physicalCyclicNormalizationCost,coreCost,B] at hm ⊢
    omega
  · exact cyclicFinalRound_fits hA p q (inverseNormalizationShift p) (2*q+8) (2*p+13) (p+8)
      a n hpq (by omega) (by omega) ha hn D z e he hz oldTail hgood
  · exact cyclicFinalRound_accuracy hA p q (inverseNormalizationShift p) (2*q+8) W (p+8)
      a n hpq (by omega) (by omega) ha D z e he hz oldTail tail hgood

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
