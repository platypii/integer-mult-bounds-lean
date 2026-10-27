module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchSetupHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedBatchWeightSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchInverseSetup

/-! Finish a weighted batch from an already installed exact weight page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def preparedBatchWeightedSetup (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq generateRuntimeWidth (.seq saveBatchInverseHeader (batchInverseSetup hQ))

def preparedBatchWeightedSetupCost (P N q s t u band L B : ℕ) : ℕ :=
  (4*q+5)+(6*B+2*(2*q+8)+10)+batchInverseSetupCost P N q s t u band L B

def preparedBatchWeightedBank {A : ℕ} (S : Stacks 117 A) (P s t u band L q N B : ℕ)
    (tail : List (Fin (A+4))) : Stacks 117 A :=
  batchInverseBank {S with R := Function.update S.R 116 []} B P s t u band L q N tail

theorem preparedBatchWeightedSetup_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q N B : ℕ}
    (hP : 13 ≤ P) (hqMax : q ≤ 2*(N+1)) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hL : 0 < L)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A+4)))
    (hprecision : (S.R 114).length = P) (hsR : (S.R 97).length = s) (htR : (S.R 98).length = t)
    (huR : (S.R 99).length = u) (hband : (S.R 100).length = band)
    (hrows : (S.R 102).length = L) (hcount : (S.R 103).length = L)
    (hq : (S.R 112).length = q) (hN : (S.R 101).length = N)
    (hB : S.R 116 = List.replicate B tick)
    (hpacket : S.R 109 = tail)
    (hclean : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(64 : Fin 117), 65, 94, 96, 104, 105, 106, 107, 108, 111, 113, 115], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ preparedBatchWeightedSetupCost P N q s t u band L B ∧
      Exec body (preparedBatchWeightedSetup hQ) (mk v S) m
        (mk v' (preparedBatchWeightedBank S P s t u band L q N B tail)) := by
  obtain ⟨v₁, hu₁, he₁⟩ := generateRuntimeWidth_exec (body := body) q v S hq
    (hfresh 94 (by simp)) (hfresh 104 (by simp))
  let Sw : Stacks 117 A := { S with R := Function.update S.R 94 (List.replicate (2*q+8) tick) }
  let T := Sw
  obtain ⟨v₃, hu₃, he₃⟩ := saveBatchInverseHeader_exec (body := body) B (2*q+8) v₁ T
    (by simpa [T, Sw] using hB) (by simp [T, Sw])
    (by simpa [T, Sw] using hfresh 107 (by simp))
  let V : Stacks 117 A := { T with R := (Function.update (Function.update (Function.update T.R
    109 (List.replicate B tick ++ blank :: tail)) 94 []) 116 []) }
  have he₃' : Exec body saveBatchInverseHeader (mk v₁ T) (6*B+2*(2*q+8)+10) (mk v₃ V) := by
    simpa only [V,T,Sw,Function.update_of_ne (show (109 : Fin 117) ≠ 94 by decide),hpacket] using he₃
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
  obtain ⟨v₄, m₄, hu₄, hm₄, he₄⟩ := batchInverseSetup_exec (body := body) (band := band) (B := B)
    hQ hA hP hqMax hs hst.le hu hL v₃ V tail
    (by simpa [V, T, Sw,hpacket] using hprecision) (by simpa [V, T, Sw,hpacket] using hsR)
    (by simpa [V, T, Sw,hpacket] using htR) (by simpa [V, T, Sw,hpacket] using huR)
    (by simpa [V, T, Sw,hpacket] using hband) (by simpa [V, T, Sw,hpacket] using hrows)
    (by simpa [V, T, Sw,hpacket] using hcount) (by simpa [V, T, Sw,hpacket] using hq)
    (by simpa [V, T, Sw,hpacket] using hN) (by simp [V, T, Sw,hpacket]) hcleanV hblankV (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [V]
      · simpa [V, T, Sw,hpacket] using hfresh 96 (by simp)
      · simpa [V, T, Sw,hpacket] using hfresh 104 (by simp)
      · simpa [V, T, Sw,hpacket] using hfresh 105 (by simp)
      · simpa [V, T, Sw,hpacket] using hfresh 106 (by simp)
      · simpa [V, T, Sw,hpacket] using hfresh 107 (by simp)
      · simpa [V, T, Sw,hpacket] using hfresh 108 (by simp)
      · simpa [V, T, Sw,hpacket] using hfresh 113 (by simp)
      · simpa [V, T, Sw,hpacket] using hfresh 115 (by simp)
      · simp [V])
  refine ⟨v₄, (4*q+5) + ((6*B+2*(2*q+8)+10) + m₄),
    hu₄.trans (hu₃.trans hu₁), by dsimp only [preparedBatchWeightedSetupCost]; omega,
    (Exec.seq he₁ (Exec.seq he₃' he₄)).cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases hk94 : k = 94
    · subst k; simp [preparedBatchWeightedBank, batchInverseBank]
    by_cases hk109 : k = 109
    · subst k; simp [preparedBatchWeightedBank, batchInverseBank]
    by_cases hk110 : k = 110
    · subst k; simp [preparedBatchWeightedBank, batchInverseBank,  V, T, Sw]
    by_cases hk116 : k = 116
    · subst k; simp [preparedBatchWeightedBank, batchInverseBank,  V, T, Sw,
        consumedGeometryBank, geometryHeaderPorts]
    simp [preparedBatchWeightedBank, batchInverseBank,  V, T, Sw,
      consumedGeometryBank, Function.update_apply, hk94, hk109, hk110, hk116]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
