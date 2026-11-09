module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedWeightPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedWeightHostStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefixStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Retained page generation separates numerical scratch from native layout traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem loadWeightOrigin_native :
    mnNativePushBound 2 (loadWeightOrigin (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  exact ⟨by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush],
    takePrefix_native _ _ _ _ _⟩

theorem pairLayout_native :
    mnNativePushBound 3 (pairLayout (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [pairLayout,splitPairs,splitPair,packPairBanks,takePrefix,releasePrefix,copyPrefix,copyR,copyStep,
    reverseWords,reverseLoopBody,reverseNext,unaryProduct,transfer,transferAct,
    scanP,scanR,ucopy,umulSym,uclear,drainR,popDo,keepIn,pushN,
    moveR,moveStep,whileR,peekR,popPush,mnNativePushBound,mnActPush]

def retainedWeightPageWorkspace (V w L : ℕ) : ℕ :=
  2*(8*V+8)+(6*L*w+3*tblC V w+2)+3*pairLayoutCost L w

/-- Compose over abstract stores before instantiating concrete table updates. -/
theorem retainedWeightPage_trace_within (V w L m₂ m₃ : ℕ)
    (v₀ v₁ v₂ v₃ : HS 117 Q A U) (S₀ S₁ S₂ S₃ : Stacks 117 A)
    (h₁ : Exec body loadWeightOrigin (mk v₀ S₀) (8*V+8) (mk v₁ S₁))
    (h₂ : ∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+depth+6*L*w+3*tblC V w+2)
      depth retainedWeightRows (mk v₁ S₁) m₂ (mk v₂ S₂))
    (h₃ : Exec body pairLayout (mk v₂ S₂) m₃ (mk v₃ S₃))
    (hm₃ : m₃ ≤ pairLayoutCost L w) (depth : ℕ) :
    ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+retainedWeightPageWorkspace V w L)
      depth retainedWeightPage (mk v₀ S₀) ((8*V+8)+(m₂+m₃)) (mk v₃ S₃) := by
  have ht₁ := mn_native_exec_within h₁ 2 loadWeightOrigin_native depth
    (mnSize (mk v₀ S₀)+depth+2*(8*V+8)) (by omega)
  have ht₃ := mn_native_exec_within h₃ 3 pairLayout_native depth
    (mnSize (mk v₂ S₂)+depth+3*pairLayoutCost L w) (by omega)
  have ht₂ : ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+depth+(6*L*w+3*tblC V w+2))
      depth retainedWeightRows (mk v₁ S₁) m₂ (mk v₂ S₂) :=
    (h₂ depth).mono (by intro d z hz; omega)
  have ht := mn_seq_within_add ht₁ (mn_seq_within_add ht₂ ht₃)
  exact ht.mono (by intro d z hz; simpa only [retainedWeightPageWorkspace, Nat.add_assoc] using hz)

theorem retainedWeightPage_exec_within {V w q P s t u L lo : ℕ} (st : TblSt 48 A)
    (hready : WeightReady A V P q s t u L st)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hlo : lo < s) (hL : L ≤ s)
    (hV : V = weightWorkspaceWidth P q w t u) (v : HS 117 Q A U) (S : Stacks 117 A)
    (tail : List (Fin (A+4)))
    (hS : tblHolds coefficientReg S (tblRho V (List.replicate V tick) (List.replicate w tick) st))
    (hwidth : (S.R 94).length = w) (hrows : (S.R 103).length = L) (hcount : (S.R 115).length = V)
    (hsrc : S.R 109 = binSyms V lo ++ tail)
    (hfresh : ∀ k ∈ [(96 : Fin 117), 104, 105, 106, 108], S.R k = []) :
    ∃ v' S' m st', v'.user = v.user ∧ m ≤ retainedWeightPageCost V w P L ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+retainedWeightPageWorkspace V w L)
        depth retainedWeightPage (mk v S) m (mk v' S')) ∧
      WeightReady A V P q s t u L st' ∧
      tblHolds coefficientReg S' (tblRho V (List.replicate V tick) (List.replicate w tick) st') ∧
      S'.R 109 = tail ∧ S'.R 110 = weightPage A w q P s t u lo L ++ S.R 110 ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k.val ≥ 63 → k ≠ 109 → k ≠ 110 → S'.R k = S.R k := by
  obtain ⟨v₁, hu₁, he₁, hh₁⟩ := loadWeightOrigin_exec (body := body) V w lo st v S tail hS hcount hsrc
    (hfresh 104 (by simp)) (hfresh 105 (by simp))
  let S₁ : Stacks 117 A := { S with R := (Function.update (Function.update S.R 47 (binSyms V lo)) 109 tail) }
  have hloV : lo < 2^V := by
    obtain ⟨_, _, _, hh, _⟩ := weightWorkspaceWidth_facts (q := q) (w := w) hP hs hst hu hlo hL
    rw [← hV] at hh
    omega
  obtain ⟨v₂, S₂, m₂, st₂, hu₂, hm₂, he₂, hr₂, hh₂, hout₂, hi₂, ho₂, hl₂, hf₂⟩ :=
    retainedWeightRows_exec_within (body := body) ⟨Function.update st.val 47 lo, st.acc⟩
      (hready.origin hloV) (by simp) hP hs hst hu hlo hL hV v₁ S₁ hh₁
  have hkeep (k : Fin 117) (hk : 63 ≤ k.val) (hk109 : k ≠ 109) (hk110 : k ≠ 110) : S₂.R k = S.R k := by
    rw [hf₂ k hk hk110]
    have hk47 : k ≠ (47 : Fin 117) := by intro he; have hv := congrArg Fin.val he; omega
    simp [S₁, hk109, hk47]
  let X := fun i => rationalWord q (ambientWeightSample P s t u lo i)
  let Y := fun i => reciprocalWeightWord q (ambientWeightSample P s t u lo i)
  have hpair : pairStream A w L X Y = (List.range L).flatMap (weightPairSymbols A w q P s t u lo) := rfl
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := pairLayout_exec (body := body) w L X Y v₂ S₂ (S.R 110)
    (by rw [hkeep 94 (by decide) (by decide) (by decide)]; exact hwidth)
    (by rw [hkeep 103 (by decide) (by decide) (by decide)]; exact hrows)
    (by rw [hpair]; simpa [S₁] using hout₂) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      all_goals rw [hkeep _ (by decide) (by decide) (by decide)]; exact hfresh _ (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 110 (weightPage A w q P s t u lo L ++ S.R 110) }
  have he₃' : Exec body pairLayout (mk v₂ S₂) m₃ (mk v₃ S₃) := by
    simpa [S₃, X, Y, weightPage, List.append_assoc] using he₃
  refine ⟨v₃, S₃, (8*V+8)+(m₂+m₃), st₂, hu₃.trans (hu₂.trans hu₁),
    by dsimp only [retainedWeightPageCost]; omega, ?_, hr₂, ?_, ?_,
    by simp [S₃], hi₂, ho₂, hl₂, ?_⟩
  · intro depth
    exact retainedWeightPage_trace_within V w L m₂ m₃ v v₁ v₂ v₃ S S₁ S₂ S₃
      he₁ he₂ he₃' hm₃ depth
  · intro r
    have hn : coefficientReg r ≠ (110 : Fin 117) := by
      intro he; have hh := coefficientReg_range r; rw [he] at hh; omega
    simpa [S₃, hn] using hh₂ r
  · simpa [S₃, S₁] using hf₂ 109 (by decide) (by decide)
  · intro k hk hk109 hk110
    simpa [S₃, hk110] using hkeep k hk hk109 hk110

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
