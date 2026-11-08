module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicNormalizationLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicNormalizationControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizeCyclicInterval

/-! Physical cyclic normalization owns its scalar width, row rulers and cleanup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 280 Q A U}

def cyclicRoundPorts : Fin 4 → Fin 280 := ![269,270,271,272]

theorem cyclicRoundPorts_injective : Function.Injective cyclicRoundPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [cyclicRoundPorts]

def physicalCyclicNormalization : Pr P 280 Q A U :=
  .seq (generateCyclicNormalizationWidth 117 119 249 0 1 2 3 4)
    (.seq cyclicNormalizationControls
      (.seq (normalizeCyclicInterval cyclicRoundReg cyclicRoundPorts
        264 265 266 267 268 117 119 95 94 277 147 273 274 275 276)
        (clearWords [94,95,249])))

def physicalCyclicNormalizationCost (p q a n : ℕ) : ℕ :=
  let P₀ := 2^15*p
  let B := cyclicNormalizationWidth P₀ q
  (19*P₀+19*q+17)+(8*q+4*(2*a+n)+21)+
    ((1+(P₀+q)*(4*B+10)+2*(8*B+12))+25*(4*B+4)+2*(8*B+8)+2+
      (18+(4*Nat.size (4*p)+31))*tblC B 0+
      roundPackedKeyCost B (2*q+8) (2*p+13) n (2*q+8) n+(2*(25*B)+2*25+1))+
    (2*((2*q+8)+n+B)+7)

theorem physicalCyclicNormalization_exec (hA : 4 ≤ A) (p q a n : ℕ)
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
    (hnew : ∀ k : Fin 280, 224 ≤ k.val → S.R k = [])
    (hsrc : S.R 147 = cstream A (2*q+8) (cyclicInterval a n D)++tail) :
    ∃ v' m, v'.user = v.user ∧ m ≤ physicalCyclicNormalizationCost p q a n ∧
      Exec body physicalCyclicNormalization (mk v S) m
        (mk v' {S with R := (Function.update S.R 147
          (cstream A (2*p+13) (cyclicInterval a n
            (fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i)))++tail))}) ∧
      (∀ x ∈ cyclicInterval a n
        (fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i)), Fits (2*p+13) x) ∧
      PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
        (cyclicIntervalRead p (2*p+13) a
          (cstream A (2*p+13) (cyclicInterval a n
            (fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i)))++tail))
        (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*z i)
        (2/(2 : ℝ)^p+e/(2 : ℝ)^inverseNormalizationShift p) := by
  let B := cyclicNormalizationWidth (2^15*p) q
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := generateCyclicNormalizationWidth_exec (body := body)
    (kernel := 117) (precision := 119) (width := 249) (a := 0) (h := 1) (par := 2) (bits := 3) (saved := 4)
    (by decide) (2^15*p) q v S hP hq (hnew 249 (by decide))
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp))
  let S₁ : Stacks 280 A := {S with R := Function.update S.R 249 (List.replicate B tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := cyclicNormalizationControls_exec (body := body) q a (min n (s-a)) (n-min n (s-a))
    v₁ S₁ (by simpa [S₁] using hq) (by simpa [S₁] using haMaster)
    (by simpa [S₁] using hleft) (by simpa [S₁] using hright)
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl
        · simpa [S₁] using hfresh 4 (by simp)
        · simpa [S₁] using hfresh 7 (by simp)
        · simpa [S₁] using hfresh 94 (by simp)
        · simpa [S₁] using hfresh 95 (by simp))
  have hparts : min n (s-a)+(n-min n (s-a)) = n := Nat.add_sub_of_le (min_le_left ..)
  let S₂ : Stacks 280 A := {S₁ with R := (Function.update (Function.update S₁.R 94
    (List.replicate (2*q+8) tick)) 95 (List.replicate n tick))}
  have he₂' : Exec body cyclicNormalizationControls (mk v₁ S₁) (8*q+4*(2*a+n)+21) (mk v₂ S₂) := by
    simpa only [S₂,hparts,Nat.add_assoc] using he₂
  have hregSep (r : TblR 25) (k : Fin 280) (hk : k.val < 224 ∨ 264 ≤ k.val) : cyclicRoundReg r ≠ k := by
    intro heq
    have hv := congrArg Fin.val heq
    have hr := cyclicRoundReg_range r
    rcases hk with hk | hk <;> omega
  have hfresh₂ (k : Fin 280) (hk : 264 ≤ k.val) : S₂.R k = [] := by
    have h249 : k ≠ 249 := by intro heq; subst k; norm_num at hk
    have h94 : k ≠ 94 := by intro heq; subst k; norm_num at hk
    have h95 : k ≠ 95 := by intro heq; subst k; norm_num at hk
    simp [S₂,S₁,h249,h94,h95,hnew k (by omega)]
  have hblank : ∀ r : TblR 25, r ≠ .wr → S₂.R (cyclicRoundReg r) = [] := by
    intro r hr
    have h249 : cyclicRoundReg r ≠ 249 := cyclicRoundReg_injective.ne hr
    have h94 : cyclicRoundReg r ≠ 94 := hregSep r 94 (by decide)
    have h95 : cyclicRoundReg r ≠ 95 := hregSep r 95 (by decide)
    simpa [S₂,S₁,h249,h94,h95] using hnew (cyclicRoundReg r) (cyclicRoundReg_range r).1
  have hroom := cyclicNormalizationWidth_room p q
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃,hfits,haccuracy⟩ := normalizeCyclicInterval_exec (body := body) hA
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
    B p q (List.replicate B tick) (by simp) hroom.1 hroom.2.1 hroom.2.2 hpq hsize
    a n ha hn D z e he hz oldTail tail hgood v₂ S₂
    (by simp [S₂,S₁,cyclicRoundReg]) (by simpa [S₂,S₁] using hP)
    (by simpa [S₂,S₁] using hq) (by simp [S₂]) (by simp [S₂]) hblank
    (by intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact hfresh₂ _ (by decide))
    (by intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hfresh₂ _ (by decide))
    (by intro i; exact hfresh₂ (cyclicRoundPorts i) (by fin_cases i <;> decide))
    (by simpa [S₂,S₁] using hsrc)
  let ys := cstream A (2*p+13) (cyclicInterval a n
    (fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i)))++tail
  let S₃ : Stacks 280 A := {S₂ with R := Function.update S₂.R 147 ys}
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) [94,95,249] (by decide) v₃ S₃
  have hcost : binaryHeaderQueueCost S₂.R B [117,119] =
      1+(2^15*p+q)*(4*B+10)+2*(8*B+12) := by
    simp [binaryHeaderQueueCost,S₂,S₁,hP,hq]
    ring
  rw [hcost] at hm₃
  refine ⟨v₄,m₁+((8*q+4*(2*a+n)+21)+(m₃+(2*((2*q+8)+n+B)+7))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ he₄))).cast ?_ ?_,hfits,haccuracy⟩
  · dsimp only [physicalCyclicNormalizationCost]
    dsimp only [B] at hm₃ ⊢
    omega
  · simp [S₃,S₂,S₁,List.sum_cons,List.sum_nil]
    omega
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h94 : k = 94 <;> by_cases h95 : k = 95 <;> by_cases h249 : k = 249 <;>
      simp [S₃,S₂,S₁,ys,Function.update_apply,h94,h95,h249,hfresh 94 (by simp),hfresh 95 (by simp),hnew 249 (by decide)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
