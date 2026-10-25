module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerStep

/-! # Generate readiness once before an integer generator iteration

The prepared counters survive all row calls and remain installed afterward.
Coefficient/RHS pages are explicit consumed inputs, not setup-generation oracles.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellIntegerGenerators

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def prepareIntegerStep (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq prepare (integerRows hQ)

/-- Counter generation, every row and publication execute without a supplied
readiness hypothesis. The installed bank is preserved for later iterations. -/
theorem prepareIntegerStep_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L n w : ℕ} (hW : P * (n + 1) + 3 ≤ w) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A + 4)))
    (hL : (S.R 102).length = L) (hwR : (S.R 94).length = w) (hqR : (S.R 100).length = 0)
    (hcount : (S.R 103).length = L) (hsaved : S.R 108 = [])
    (hx : S.R 110 = cstream A w (rowColumnWords P s t u band L n) ++ tailX)
    (ha : S.R 111 = cstream A w ((generatorRowJobs P s t u band L n).flatMap Prod.fst) ++ tailA)
    (hr : S.R 112 = cstream A w ((generatorRowJobs P s t u band L n).map Prod.snd) ++ tailR)
    (hc : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(96 : Fin 117), 97, 98, 99, 104, 105, 106], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCost 0 w + L * (integerRowCost L w + 5) + 4 ∧
      Exec body (prepareIntegerStep hQ) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update (Function.update (counterR 0 w S.R)
          111 tailA) 112 tailR) 113
            (cstream A w (rowColumnWords P s t u band L (n + 1)) ++ S.R 113)) }) ∧
      ∀ i < L, Fits w (⟨(columnNumerators P s t u band L (n + 1)).getD i 0, 0⟩ : GaussianInt) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := prepare_exec_of_width (body := body) 0 w (by nlinarith) (by nlinarith)
    v S hqR hwR (by
      intro k hk
      exact (hc ⟨k.val, by omega⟩).2) (fun r _ => hblank r)
  let SP : Stacks 117 A := { S with R := counterR 0 w S.R }
  have hcleanP : CClean mul SP := by
    intro i
    refine ⟨(hc i).1, ?_⟩
    simpa [SP, counterR, (cr_mul .wn i).symm, (cr_mul .pn i).symm, (cr_mul .nn i).symm] using (hc i).2
  have hworkP : ∀ k ∈ integerRowWork, SP.R k = [] := by
    intro k hk
    have hb : S.R k = [] := by
      simp only [integerRowWork, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact hblank _ | exact hfresh _ (by simp)
    have hd : integerRowWork.Disjoint [cr .wn, cr .pn, cr .nn] := by
      simp [integerRowWork, cr, OutputPlacement.code]
    have hne (r : CR) (hr : r ∈ [CR.wn, .pn, .nn]) : k ≠ cr r := by
      intro he
      subst k
      apply List.disjoint_left.mp hd hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp
    simpa [SP, counterR, hne .wn (by simp), hne .pn (by simp), hne .nn (by simp)] using hb
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, hfits⟩ := integerGeneratorStep_exec (body := body)
    hQ hA hW hP hs hst hu hn v₁ SP tailX tailA tailR
    (by simpa [SP, counterR, cr, OutputPlacement.code] using hL)
    (by simpa [SP, counterR, cr, OutputPlacement.code] using hwR)
    (by simpa [SP, counterR, cr, OutputPlacement.code] using hcount)
    (by simpa [SP, counterR, cr, OutputPlacement.code] using hsaved)
    (by simpa [SP, counterR, cr, OutputPlacement.code] using hx)
    (by simpa [SP, counterR, cr, OutputPlacement.code] using ha)
    (by simpa [SP, counterR, cr, OutputPlacement.code] using hr)
    hcleanP (counterR_ready 0 w S.R hblank) hworkP
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, ?_, hfits⟩
  simpa [SP, counterR, cr, OutputPlacement.code, prepareIntegerStep] using Exec.seq he₁ he₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
