module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchInverseSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderGeneratorSetupStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseConstructionStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareBatchGeneratorPageStock

/-! Shared inverse construction is paid once; each additional cell pays only encoded traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

@[irreducible] def batchInverseSetupWorkspace (C P N q s t u band L B : ℕ) : ℕ :=
  headerGeneratorSetupWorkspace C P N q s t u band L+
    (3*releaseConstructionCost L (integerSetupWidth P q (N+1) 0) (N+1)+
      prepareBatchGeneratorPageWorkspace B L q)

theorem batchInverseSetupWorkspace_affine (C P N q s t u band L B : ℕ) :
    batchInverseSetupWorkspace C P N q s t u band L B =
      batchInverseSetupWorkspace C P N q s t u band L 0+B*(8*(38*(L*(2*q+8))+43)) := by
  unfold batchInverseSetupWorkspace
  rw [prepareBatchGeneratorPageWorkspace_affine B L q]
  omega

theorem batchInverseSetup_trace_within (hQ : SS.states ≤ Q) (C P N q s t u band L B m₁ m₂ m₃ : ℕ)
    (v₀ v₁ v₂ v₃ : HS 117 Q A U) (S₀ S₁ S₂ S₃ : Stacks 117 A)
    (h₁ : ∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+headerGeneratorSetupWorkspace C P N q s t u band L)
      depth (headerGeneratorSetup hQ) (mk v₀ S₀) m₁ (mk v₁ S₁))
    (h₂ : ∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+depth+
        3*releaseConstructionCost L (integerSetupWidth P q (N+1) 0) (N+1))
      depth releaseConstruction (mk v₁ S₁) m₂ (mk v₂ S₂))
    (h₃ : ∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₂ S₂)+depth+prepareBatchGeneratorPageWorkspace B L q)
      depth prepareBatchGeneratorPage (mk v₂ S₂) m₃ (mk v₃ S₃)) (depth : ℕ) :
    ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+batchInverseSetupWorkspace C P N q s t u band L B)
      depth (batchInverseSetup hQ) (mk v₀ S₀) (m₁+(m₂+m₃)) (mk v₃ S₃) := by
  exact (mn_seq_within_add (h₁ depth) (mn_seq_within_add (h₂ depth) (h₃ depth))).mono (by
    intro d z hz; simpa only [batchInverseSetupWorkspace] using hz)

theorem batchInverseSetup_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q N B : ℕ} (hP : 13 ≤ P) (hqMax : q ≤ 2 * (N + 1))
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C)
    (v : HS 117 Q A U) (S : Stacks 117 A) (controlTail : List (Fin (A + 4)))
    (hprecision : (S.R 114).length = P) (hsR : (S.R 97).length = s) (htR : (S.R 98).length = t)
    (huR : (S.R 99).length = u) (hband : (S.R 100).length = band)
    (hrows : (S.R 102).length = L) (hrowCount : (S.R 103).length = L)
    (hq : (S.R 112).length = q) (hcount : (S.R 101).length = N)
    (hpacket : S.R 109 = List.replicate B tick ++ blank :: controlTail)
    (hclean : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 96, 104, 105, 106, 107, 108, 113, 115, 116], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ batchInverseSetupCost P N q s t u band L B ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+batchInverseSetupWorkspace C P N q s t u band L B)
        depth (batchInverseSetup hQ) (mk v S) m
        (mk v' (batchInverseBank S B P s t u band L q N controlTail))) := by
  let W := integerSetupWidth P q (N + 1) 0
  let U₀ := unaryGeometryBase S P q N
  have hcore (k : Fin 117) (hk : k.val < 63) : S.R k = [] := by
    have hh := (hclean ⟨k.val, by omega⟩).2
    simpa [mul] using hh
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := headerGeneratorSetup_exec_within (body := body) (band := band)
    hQ hA hP hqMax hs hst hu hL C hpush v S hprecision hsR htR huR hband hrows hrowCount hq hcount hclean hblank hfresh
  have hb : ∀ r, U₀.R (cr r) = [] := by
    intro r
    have hr := cr_range r
    have hg : cr r ∉ geometryHeaderPorts := by
      intro hk
      simp only [geometryHeaderPorts, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with he | he | he | he | he <;> have hv := congrArg Fin.val he <;> omega
    have h94 : cr r ≠ (94 : Fin 117) := by intro he; exact hr.2.2.2 (congrArg Fin.val he)
    simpa [U₀, unaryGeometryBase, setupWidthBank, hg, h94] using hblank r
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := releaseConstruction_exec_within (body := body)
    P s t u band L q W (N + 1) v₁ U₀
    (by simpa [U₀, unaryGeometryBase, setupWidthBank, geometryHeaderPorts] using hrows)
    (by simpa [U₀, unaryGeometryBase, setupWidthBank, geometryHeaderPorts] using hrowCount)
    (by simp [U₀, unaryGeometryBase, setupWidthBank, geometryHeaderPorts, W]) hb
    (by simpa [U₀, unaryGeometryBase, setupWidthBank, geometryHeaderPorts] using hfresh 116 (by simp)) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      · simp [U₀, unaryGeometryBase, geometryHeaderPorts]
      · simp [U₀, unaryGeometryBase, geometryHeaderPorts]
      all_goals simpa [U₀, unaryGeometryBase, setupWidthBank, geometryHeaderPorts] using hfresh _ (by simp))
  let T₀ := retainedGeneratorBank U₀ P s t u band L q (N + 1)
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := prepareBatchGeneratorPage_exec_within (body := body)
    B P s t u band L q (N + 1) v₂ T₀ controlTail (S.R 110)
    (by simpa [T₀, retainedGeneratorBank, U₀, unaryGeometryBase, setupWidthBank, geometryHeaderPorts] using hrowCount)
    (by simpa [T₀, retainedGeneratorBank, U₀, unaryGeometryBase, setupWidthBank, geometryHeaderPorts] using hq)
    (by simpa [T₀, retainedGeneratorBank, U₀, unaryGeometryBase, setupWidthBank, geometryHeaderPorts] using hpacket)
    (by simp [T₀, retainedGeneratorBank, U₀, unaryGeometryBase, setupWidthBank, geometryHeaderPorts]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [T₀, retainedGeneratorBank]
      · simpa [T₀, retainedGeneratorBank, U₀, unaryGeometryBase, setupWidthBank, geometryHeaderPorts] using hfresh 96 (by simp)
      · simp [T₀, retainedGeneratorBank, U₀, unaryGeometryBase, geometryHeaderPorts]
      · simp [T₀, retainedGeneratorBank, U₀, unaryGeometryBase, geometryHeaderPorts]
      · simp [T₀, retainedGeneratorBank, U₀, unaryGeometryBase, geometryHeaderPorts]
      all_goals simpa [T₀, retainedGeneratorBank, U₀, unaryGeometryBase, setupWidthBank, geometryHeaderPorts] using hfresh _ (by simp))
  refine ⟨v₃, m₁ + (m₂ + m₃), hu₃.trans (hu₂.trans hu₁),
    by dsimp only [batchInverseSetupCost, W] at *; omega,
    (fun depth => (batchInverseSetup_trace_within hQ C P N q s t u band L B _ _ _
    v v₁ v₂ v₃ S _ T₀ _ he₁ he₂ he₃ depth).cast rfl ?_)⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases hk : k ∈ [(96 : Fin 117), 94, 109, 110]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;>
        simp [T₀, retainedGeneratorBank, batchInverseBank, consumedGeometryBank,
          U₀, unaryGeometryBase, setupWidthBank, geometryHeaderPorts]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    by_cases hlo : k.val < 63
    · have hgeo : k ∉ geometryHeaderPorts := by
        intro hg
        simp only [geometryHeaderPorts, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with he | he | he | he | he <;> have hv := congrArg Fin.val he <;> omega
      simp [T₀, retainedGeneratorBank, batchInverseBank, consumedGeometryBank,
        U₀, unaryGeometryBase, setupWidthBank, Function.update_apply, hk.1, hk.2.1, hk.2.2.1, hk.2.2.2,
        hlo, hgeo, hcore k hlo]
    simp [T₀, retainedGeneratorBank, batchInverseBank, consumedGeometryBank,
      U₀, unaryGeometryBase, setupWidthBank, Function.update_apply, hk.1, hk.2.1, hk.2.2.1, hk.2.2.2, hlo]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
