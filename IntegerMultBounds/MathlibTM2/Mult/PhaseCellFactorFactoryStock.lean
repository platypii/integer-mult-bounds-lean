module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorFactory
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientHostStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixReleaseStock

/-! The factor factory shares coefficient arithmetic and pays native page assembly by volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem constructFactorPage_native :
    mnNativePushBound 3 (constructFactorPage (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [constructFactorPage,factorRowStep,constructFactorRow,copyAfterPrefix,
    reverseWords,reverseLoopBody,reverseNext,copyPrefix,copyR,copyStep,
    unaryProduct,transfer,transferAct,clearWords,usub,dropTop,ucopy,umulSym,scanP,scanR,
    drainR,popDo,keepIn,pushN,popPush,moveR,moveStep,whileR,peekR,uclear,
    mnNativePushBound,mnActPush]


@[irreducible] def factorFactoryWorkspace (L V W : ℕ) : ℕ :=
  (3*(L*W)+3*tblC V W+2)+(3*constructFactorPageCost L W+3*(12*(L*W)+9*L+12))

theorem factorFactory_trace_within (L V W m₁ m₂ m₃ : ℕ)
    (v₀ v₁ v₂ v₃ : HS 117 Q A U) (S₀ S₁ S₂ S₃ : Stacks 117 A)
    (h₁ : ∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+3*(L*W)+3*tblC V W+2)
      depth coefficientHost (mk v₀ S₀) m₁ (mk v₁ S₁))
    (h₂ : Exec body constructFactorPage (mk v₁ S₁) m₂ (mk v₂ S₂))
    (h₃ : Exec body (releaseFromDimensions 102 94 99 110 104 105 106)
      (mk v₂ S₂) m₃ (mk v₃ S₃))
    (hm₂ : m₂ ≤ constructFactorPageCost L W) (hm₃ : m₃ ≤ 12*(L*W)+9*L+12) (depth : ℕ) :
    ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+factorFactoryWorkspace L V W)
      depth factorFactory (mk v₀ S₀) (m₁+(m₂+m₃)) (mk v₃ S₃) := by
  have ht₁ : ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+(3*(L*W)+3*tblC V W+2))
      depth coefficientHost (mk v₀ S₀) m₁ (mk v₁ S₁) :=
    (h₁ depth).mono (by intro d z hz; omega)
  have ht₂ := mn_native_exec_within h₂ 3 constructFactorPage_native depth
    (mnSize (mk v₁ S₁)+depth+3*constructFactorPageCost L W) (by omega)
  have ht₃ := mn_native_exec_within h₃ 3 (releaseFromDimensions_native ..) depth
    (mnSize (mk v₂ S₂)+depth+3*(12*(L*W)+9*L+12)) (by omega)
  exact (mn_seq_within_add ht₁ (mn_seq_within_add ht₂ ht₃)).mono (by
    intro d z hz
    simpa only [factorFactoryWorkspace] using hz)

theorem factorFactory_exec_within {V W P s t u band L : ℕ} (st : TblSt 48 A)
    (hP' : st.val 19 = P) (hs' : st.val 34 = s) (ht' : st.val 35 = t)
    (hu' : st.val 36 = u) (hb' : st.val 38 = band) (hL' : st.val 42 = L)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u)
    (hV : u * t * (L + 1) ^ 2 * 2 ^ (13 * P + 8) < 2 ^ V)
    (hstV : ∀ j, st.val j < 2 ^ V) (hacc : st.acc = [])
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = V) (hnl : nl.length = W) (hw : W ≤ V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hS : tblHolds coefficientReg S (tblRho V wl nl st))
    (hwidth : (S.R 94).length = W) (hrows : (S.R 102).length = L) (hcount : (S.R 103).length = L)
    (hfresh : ∀ k ∈ [(97 : Fin 117), 98, 99, 100, 104, 105, 106, 107, 108], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ factorFactoryCost P L V W ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+factorFactoryWorkspace L V W)
        depth factorFactory (mk v S) m
        (mk v' { S with R := (fun k => if k.val < 63 then [] else if k = 109 then
          (cstream A W ((List.range L).reverse.flatMap (rowFactorWords P s t u band L)) ++ S.R 109) else S.R k) })) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := coefficientHost_exec_within (body := body) st hP' hs' ht' hu' hb' hL'
    hP hs hst hu hV hstV hacc wl nl hwl hnl hw v S hS
  let S₁ : Stacks 117 A := { S with R := (fun k => if k.val < 63 then [] else if k = 110 then
    (cstream A W (distanceFactorWords P s t u band L) ++ S.R 110) else S.R k) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := constructFactorPage_exec (body := body) P s t u band L W v₁ S₁ (S.R 110)
    (by simpa [S₁] using hwidth) (by simpa [S₁] using hrows) (by simpa [S₁] using hcount)
    (by simp [S₁]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [S₁] using hfresh _ (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := (Function.update S₁.R 109
    (cstream A W ((List.range L).reverse.flatMap (rowFactorWords P s t u band L)) ++ S₁.R 109)) }
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := releaseFromDimensions_exec (body := body)
    (show [(102 : Fin 117), 94, 99, 110, 104, 105, 106].Nodup by decide) v₂ S₂
    (cstream A W (distanceFactorWords P s t u band L)) (S.R 110)
    (by simp [S₂, S₁]) (by simp [S₂, S₁, hrows, hwidth])
    (by simpa [S₂, S₁] using hfresh 99 (by simp)) (by simpa [S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₂, S₁] using hfresh 105 (by simp)) (by simpa [S₂, S₁] using hfresh 106 (by simp))
  have hm₃' : m₃ ≤ 12 * (L * W) + 9 * L + 12 := by
    simpa [S₂, S₁, hrows] using hm₃
  refine ⟨v₃, m₁ + (m₂ + m₃), hu₃.trans (hu₂.trans hu₁), ?_,
    (fun depth => (factorFactory_trace_within L V W m₁ m₂ m₃ v v₁ v₂ v₃ S S₁ S₂ _
      he₁ he₂ he₃ hm₂ hm₃' depth).cast rfl ?_)⟩
  · unfold factorFactoryCost
    nlinarith only [hm₁, hm₂, hm₃']
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hc : k.val < 63
    · have h110 : k ≠ 110 := by intro he; have hv := congrArg Fin.val he; omega
      have h109 : k ≠ 109 := by intro he; have hv := congrArg Fin.val he; omega
      simp [S₂, S₁, hc, h110, h109]
    by_cases h110 : k = 110
    · subst k; simp
    by_cases h109 : k = 109
    · subst k; simp [S₂, S₁]
    simp [S₂, S₁, hc, h110, h109]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
