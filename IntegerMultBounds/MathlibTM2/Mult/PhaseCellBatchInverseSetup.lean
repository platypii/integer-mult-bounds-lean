module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareBatchGeneratorPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderGeneratorRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseConstruction

/-! Compute one numerical inverse from unary geometry and precision headers,
release construction storage, then expand its two columns for the whole batch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def batchInverseSetup (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq (headerGeneratorSetup hQ) (.seq releaseConstruction prepareBatchGeneratorPage)

def batchInverseSetupCost (P N q s t u band L B : ℕ) : ℕ :=
  let W := integerSetupWidth P q (N + 1) 0
  headerGeneratorSetupCost P N q s t u band L + releaseConstructionCost L W (N + 1) +
    prepareBatchGeneratorPageCost B L q

def batchInverseBank {A : ℕ} (S : Stacks 117 A) (B P s t u band L q N : ℕ)
    (controlTail : List (Fin (A + 4))) : Stacks 117 A :=
  let C := consumedGeometryBank S
  { C with R := (Function.update (Function.update (Function.update (Function.update C.R
    96 (List.replicate B tick)) 94 (List.replicate (2 * q + 8) tick)) 109 controlTail)
    110 (batchGeneratorPage A B P s t u band L q (N + 1) ++ S.R 110)) }

theorem batchInverseSetup_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q N B : ℕ} (hP : 13 ≤ P) (hqMax : q ≤ 2 * (N + 1))
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L)
    (v : HS 117 Q A U) (S : Stacks 117 A) (controlTail : List (Fin (A + 4)))
    (hprecision : (S.R 114).length = P) (hsR : (S.R 97).length = s) (htR : (S.R 98).length = t)
    (huR : (S.R 99).length = u) (hband : (S.R 100).length = band)
    (hrows : (S.R 102).length = L) (hrowCount : (S.R 103).length = L)
    (hq : (S.R 112).length = q) (hcount : (S.R 101).length = N)
    (hpacket : S.R 109 = List.replicate B tick ++ blank :: controlTail)
    (hclean : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 96, 104, 105, 106, 107, 108, 113, 115, 116], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ batchInverseSetupCost P N q s t u band L B ∧
      Exec body (batchInverseSetup hQ) (mk v S) m
        (mk v' (batchInverseBank S B P s t u band L q N controlTail)) := by
  let W := integerSetupWidth P q (N + 1) 0
  let U₀ := unaryGeometryBase S P q N
  have hcore (k : Fin 117) (hk : k.val < 63) : S.R k = [] := by
    have hh := (hclean ⟨k.val, by omega⟩).2
    simpa [mul] using hh
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := headerGeneratorSetup_exec (body := body) (band := band)
    hQ hA hP hqMax hs hst hu hL v S hprecision hsR htR huR hband hrows hrowCount hq hcount hclean hblank hfresh
  have hb : ∀ r, U₀.R (cr r) = [] := by
    intro r
    have hr := cr_range r
    have hg : cr r ∉ geometryHeaderPorts := by
      intro hk
      simp only [geometryHeaderPorts, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with he | he | he | he | he <;> have hv := congrArg Fin.val he <;> omega
    have h94 : cr r ≠ (94 : Fin 117) := by intro he; exact hr.2.2.2 (congrArg Fin.val he)
    simpa [U₀, unaryGeometryBase, setupWidthBank, hg, h94] using hblank r
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := releaseConstruction_exec (body := body)
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
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := prepareBatchGeneratorPage_exec (body := body)
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
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
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

/-- All expensive numerical construction is outside the replica loop. -/
theorem batchInverseSetupCost_affine (P N q s t u band L B : ℕ) :
    batchInverseSetupCost P N q s t u band L B =
      batchInverseSetupCost P N q s t u band L 0 + B * (38 * (L * (2 * q + 8)) + 43) := by
  simp only [batchInverseSetupCost, prepareBatchGeneratorPageCost, replicateGeneratorsCost]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
