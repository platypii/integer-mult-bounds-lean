module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchWeightedSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchInverseSetupStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedBatchWeightSetupStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchSetupHeadersStock
public import IntegerMultBounds.MathlibTM2.StackDepthInvariant

/-! The full batch setup shares weight and inverse numerical reserves across all cells. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

@[irreducible] def batchWeightedSetupWorkspace (C P N q s t u band L B : ℕ) : ℕ :=
  8*(4*q+5)+(sharedBatchWeightSetupWorkspace P s t u q L (2*q+8) B+
    (2*(6*B+2*(2*q+8)+10)+batchInverseSetupWorkspace C P N q s t u band L B))

theorem batchWeightedSetup_trace_within (hQ : SS.states ≤ Q) (C P N q s t u band L B m₂ m₄ : ℕ)
    (v₀ v₁ v₂ v₃ v₄ : HS 117 Q A U) (S₀ S₁ S₂ S₃ S₄ : Stacks 117 A)
    (h₁ : Exec body generateRuntimeWidth (mk v₀ S₀) (4*q+5) (mk v₁ S₁))
    (h₂ : ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+0+sharedBatchWeightSetupWorkspace P s t u q L (2*q+8) B)
      0 sharedBatchWeightSetup (mk v₁ S₁) m₂ (mk v₂ S₂))
    (h₃ : Exec body saveBatchInverseHeader (mk v₂ S₂) (6*B+2*(2*q+8)+10) (mk v₃ S₃))
    (h₄ : ∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₃ S₃)+depth+batchInverseSetupWorkspace C P N q s t u band L B)
      depth (batchInverseSetup hQ) (mk v₃ S₃) m₄ (mk v₄ S₄)) (depth : ℕ) :
    ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+batchWeightedSetupWorkspace C P N q s t u band L B)
      depth (batchWeightedSetup hQ) (mk v₀ S₀) ((4*q+5)+(m₂+((6*B+2*(2*q+8)+10)+m₄))) (mk v₄ S₄) := by
  have ht₁ := mn_native_exec_within h₁ 8 generateRuntimeWidth_native depth _ (Nat.le_refl _)
  have ht₃ := mn_native_exec_within h₃ 2 saveBatchInverseHeader_native depth _ (Nat.le_refl _)
  exact (mn_seq_within_add ht₁ (mn_seq_within_add (mn_execWithin_add_depth h₂ depth)
    (mn_seq_within_add ht₃ (h₄ depth)))).mono (by
      intro d z hz; simpa only [batchWeightedSetupWorkspace] using hz)

theorem batchWeightedSetup_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q N B : ℕ} (lo : ℕ → ℕ)
    (hP : 13 ≤ P) (hqMax : q ≤ 2*(N+1)) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hL : 0 < L) (hLs : L ≤ s) (hlo : ∀ i < B, lo i < s)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A+4)))
    (hprecision : (S.R 114).length = P) (hsR : (S.R 97).length = s) (htR : (S.R 98).length = t)
    (huR : (S.R 99).length = u) (hband : (S.R 100).length = band)
    (hrows : (S.R 102).length = L) (hcount : (S.R 103).length = L)
    (hq : (S.R 112).length = q) (hN : (S.R 101).length = N)
    (hB : S.R 116 = List.replicate B tick)
    (hpacket : S.R 109 = (List.range B).flatMap (fun i => binSyms (weightWorkspaceWidth P q (2*q+8) t u) (lo i)) ++ tail)
    (hclean : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(64 : Fin 117), 65, 94, 96, 104, 105, 106, 107, 108, 111, 113, 115], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ batchWeightedSetupCost P N q s t u band L B ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+batchWeightedSetupWorkspace C P N q s t u band L B)
        depth (batchWeightedSetup hQ) (mk v S) m
        (mk v' (batchWeightedBank S P s t u band L q N B lo tail))) := by
  obtain ⟨v₁, hu₁, he₁⟩ := generateRuntimeWidth_exec (body := body) q v S hq
    (hfresh 94 (by simp)) (hfresh 104 (by simp))
  let Sw : Stacks 117 A := { S with R := Function.update S.R 94 (List.replicate (2*q+8) tick) }
  have htable : ∀ r, Sw.R (coefficientReg r) = [] := by
    intro r
    have hr := coefficientReg_range r
    have hn : coefficientReg r ≠ (94 : Fin 117) := by intro he; rw [he] at hr; omega
    have hh := (hclean ⟨(coefficientReg r).val, by omega⟩).2
    simpa [Sw, hn, mul] using hh
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := sharedBatchWeightSetup_exec_within (body := body)
    P s t u q L (2*q+8) B lo v₁ Sw tail
    (by simpa [Sw] using hprecision) (by simpa [Sw] using hsR) (by simpa [Sw] using htR)
    (by simpa [Sw] using huR) (by simpa [Sw] using hq) (by simpa [Sw] using hrows)
    (by simpa [Sw] using hcount) (by simp [Sw]) (by simp [Sw, hB])
    (by simpa [Sw] using hpacket) htable (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simpa [Sw] using hfresh _ (by simp)) hP hs hst hu hlo hLs
  let T : Stacks 117 A := { Sw with R := (Function.update (Function.update Sw.R 109 tail)
    110 (batchWeightPage A (2*q+8) q P s t u B L lo ++ S.R 110)) }
  obtain ⟨v₃, hu₃, he₃⟩ := saveBatchInverseHeader_exec (body := body) B (2*q+8) v₂ T
    (by simpa [T, Sw] using hB) (by simp [T, Sw])
    (by simpa [T, Sw] using hfresh 107 (by simp))
  let V : Stacks 117 A := { T with R := (Function.update (Function.update (Function.update T.R
    109 (List.replicate B tick ++ blank :: tail)) 94 []) 116 []) }
  have hcleanV : CClean mul V := by
    intro i
    refine ⟨(hclean i).1, ?_⟩
    have hn (n : Fin 117) (hh : 64 ≤ n.val) : mul i ≠ n := by
      intro he; have hv := congrArg Fin.val he; have hi := i.isLt; simp only [mul] at hv; omega
    simpa [V, T, Sw, hn 109 (by decide), hn 110 (by decide), hn 94 (by decide), hn 116 (by decide)]
      using (hclean i).2
  have hblankV : ∀ r, V.R (cr r) = [] := by
    intro r
    have hr := cr_range r
    have h94 : cr r ≠ (94 : Fin 117) := by intro he; exact hr.2.2.2 (congrArg Fin.val he)
    have hn (n : Fin 117) (hh : 96 ≤ n.val) : cr r ≠ n := by intro he; rw [he] at hr; omega
    simpa [V, T, Sw, h94, hn 109 (by decide), hn 110 (by decide), hn 116 (by decide)] using hblank r
  obtain ⟨v₄, m₄, hu₄, hm₄, he₄⟩ := batchInverseSetup_exec_within (body := body) (band := band) (B := B)
    hQ hA hP hqMax hs hst.le hu hL C hpush v₃ V tail
    (by simpa [V, T, Sw] using hprecision) (by simpa [V, T, Sw] using hsR)
    (by simpa [V, T, Sw] using htR) (by simpa [V, T, Sw] using huR)
    (by simpa [V, T, Sw] using hband) (by simpa [V, T, Sw] using hrows)
    (by simpa [V, T, Sw] using hcount) (by simpa [V, T, Sw] using hq)
    (by simpa [V, T, Sw] using hN) (by simp [V, T, Sw]) hcleanV hblankV (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [V]
      · simpa [V, T, Sw] using hfresh 96 (by simp)
      · simpa [V, T, Sw] using hfresh 104 (by simp)
      · simpa [V, T, Sw] using hfresh 105 (by simp)
      · simpa [V, T, Sw] using hfresh 106 (by simp)
      · simpa [V, T, Sw] using hfresh 107 (by simp)
      · simpa [V, T, Sw] using hfresh 108 (by simp)
      · simpa [V, T, Sw] using hfresh 113 (by simp)
      · simpa [V, T, Sw] using hfresh 115 (by simp)
      · simp [V])
  refine ⟨v₄, (4*q+5) + (m₂ + ((6*B+2*(2*q+8)+10) + m₄)),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), by dsimp only [batchWeightedSetupCost]; omega,
    (fun depth => (batchWeightedSetup_trace_within hQ C P N q s t u band L B _ _
    v v₁ v₂ v₃ v₄ S Sw T V _ he₁ he₂ he₃ he₄ depth).cast rfl ?_)⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases hk94 : k = 94
    · subst k; simp [batchWeightedBank, batchInverseBank]
    by_cases hk109 : k = 109
    · subst k; simp [batchWeightedBank, batchInverseBank]
    by_cases hk110 : k = 110
    · subst k; simp [batchWeightedBank, batchInverseBank, batchWeightedBase, V, T, Sw]
    by_cases hk116 : k = 116
    · subst k; simp [batchWeightedBank, batchInverseBank, batchWeightedBase, V, T, Sw,
        consumedGeometryBank, geometryHeaderPorts]
    simp [batchWeightedBank, batchInverseBank, batchWeightedBase, V, T, Sw,
      consumedGeometryBank, Function.update_apply, hk94, hk109, hk110, hk116]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
