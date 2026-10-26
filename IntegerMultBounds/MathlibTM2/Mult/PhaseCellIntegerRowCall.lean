module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRowStage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRowFinish

/-! # Borrow, execute and release one integer generator row

The column, factor row and RHS are borrowed with arbitrary suffixes. All staging
counts are generated and released. Installed multiplication readiness is reused;
only the output prefix changes, so this call is ready for row-loop composition.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def integerRowCall (hQ : SS.states ≤ Q) : Pr P 117 Q A U :=
  .seq stageIntegerRow (.seq (integerRowPrepared hQ) finishIntegerRow)

def integerRowWork : List (Fin 117) :=
  [cr .xs, cr .ys, cr .xsv, cr .ysv, cr .acc, cr .out, 96, 97, 98, 99, 104, 105, 106]

theorem fixedPointRowCall_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {L q w : ℕ} (hw : 1 ≤ w) (hqw : q ≤ w) (xs as : List GaussianInt) (rhs : GaussianInt)
    (hxlen : xs.length = L) (halen : as.length = L)
    (hxs : ∀ x ∈ xs, Fits w x) (has : ∀ a ∈ as, Fits w a ∧ a.im = 0)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A + 4)))
    (hL : (S.R 102).length = L) (hwR : (S.R 94).length = w)
    (hx : S.R 110 = cstream A w xs ++ tailX) (ha : S.R 111 = cstream A w as ++ tailA)
    (hrhs : S.R 112 = csyms A w rhs ++ tailR) (hc : CClean mul S)
    (hready : Ready (fun r => S.R (cr r)) w q)
    (hwork : ∀ k ∈ integerRowWork, S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ L * (rmulCost w + 43 * w + 21) + 14 * w + 55 ∧
      Exec body (integerRowCall hQ) (mk v S) m
        (mk v' { S with R := (Function.update S.R 113
          (csyms A w (rhs - (List.zipWith (fun x a => tdivN q (x*a)) xs as).sum) ++ S.R 113)) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := stageIntegerRow_exec (body := body) L w xs as rhs hxlen halen
    v S tailX tailA tailR hL hwR hx ha hrhs (fun k hk => hwork k
      ((by decide : [cr .xs, cr .ys, (96 : Fin 117), 99, 104, 105].Sublist integerRowWork).subset hk))
  let SL := stagedIntegerRow S w xs as rhs
  have h96 (r : CR) : cr r ≠ 96 := by
    have hh := (cr_range r).2.1
    intro he
    have hv := congrArg Fin.val he
    omega
  have hreadyL : Ready (fun r => SL.R (cr r)) w q := by
    have hrho : (fun r => SL.R (cr r)) = Function.update (Function.update
        (fun r => S.R (cr r)) .xs (cstream A w xs)) .ys (cstream A w as) := by
      funext r
      simp [SL, stagedIntegerRow, Function.update_apply, h96 r, cr_injective.eq_iff]
    rw [hrho]
    exact (hready.update .xs (by simp) _).update .ys (by simp) _
  have hcleanL : CClean mul SL := by
    intro i
    refine ⟨(hc i).1, ?_⟩
    have hi : mul i ≠ 96 := by
      intro he
      have hv := congrArg Fin.val he
      have hil := i.isLt
      simp only [mul] at hv
      omega
    simpa [SL, stagedIntegerRow, hi, (cr_mul .xs i).symm, (cr_mul .ys i).symm] using (hc i).2
  have hports (r : CR) (hrx : r ≠ .xs) (hry : r ≠ .ys) : SL.R (cr r) = S.R (cr r) := by
    simp [SL, stagedIntegerRow, h96 r, cr_injective.eq_iff, hrx, hry]
  have hcrwork (r : CR) (hr : r ∈ [CR.xs, .ys, .xsv, .ysv, .acc, .out]) : S.R (cr r) = [] := by
    apply hwork
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [integerRowWork]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := fixedPointRowPrepared_exec (body := body) hQ hA hw hqw xs as
    (hxlen.trans halen.symm) hxs has v₁ SL rhs hcleanL hreadyL
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        rw [hports _ (by decide) (by decide)] <;> exact hcrwork _ (by simp))
    (by simpa [SL, stagedIntegerRow, cr, OutputPlacement.code] using hwR)
    (by simp [SL, stagedIntegerRow, cr, OutputPlacement.code])
    (by simp [SL, stagedIntegerRow, cr, OutputPlacement.code])
    (by simp [SL, stagedIntegerRow])
    (by simpa [SL, stagedIntegerRow, cr, OutputPlacement.code] using hwork 97 (by simp [integerRowWork]))
    (by simpa [SL, stagedIntegerRow, cr, OutputPlacement.code] using hwork 98 (by simp [integerRowWork]))
  let z := rhs - (List.zipWith (fun x a => tdivN q (x*a)) xs as).sum
  let SA : Stacks 117 A := { SL with R := Function.update SL.R 96 (csyms A w z) }
  obtain ⟨v₃, hu₃, he₃⟩ := finishIntegerRow_exec (body := body) L w xs as z hxlen halen v₂ SA
    (by simp [SA, SL, stagedIntegerRow, cr, OutputPlacement.code])
    (by simp [SA, SL, stagedIntegerRow, cr, OutputPlacement.code])
    (by simp [SA])
    (by simpa [SA, SL, stagedIntegerRow, cr, OutputPlacement.code] using hwork 106 (by simp [integerRowWork]))
  refine ⟨v₃, m₁ + (m₂ + (4 * (L * w) + 4 * w + 9)), hu₃.trans (hu₂.trans hu₁), ?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · rw [hxlen] at hm₂
    nlinarith only [hm₁, hm₂]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    have hx0 := hcrwork .xs (by simp)
    have hy0 := hcrwork .ys (by simp)
    have hr0 := hwork 96 (by simp [integerRowWork])
    funext k
    by_cases ho : k = 113
    · subst k; simp [SA, SL, stagedIntegerRow, cr, OutputPlacement.code, z]
    by_cases hr : k = 96
    · subst k; simp [SA, SL, stagedIntegerRow, cr, OutputPlacement.code, hr0]
    by_cases hx' : k = cr .xs
    · subst k; simpa [SA, SL, stagedIntegerRow, cr, OutputPlacement.code] using hx0.symm
    by_cases hy' : k = cr .ys
    · subst k; simpa [SA, SL, stagedIntegerRow, cr, OutputPlacement.code] using hy0.symm
    simp [SA, SL, stagedIntegerRow, ho, hr, hx', hy']

theorem integerRowCall_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {L w : ℕ} (hw : 1 ≤ w) (xs as : List GaussianInt) (rhs : GaussianInt)
    (hxlen : xs.length = L) (halen : as.length = L)
    (hxs : ∀ x ∈ xs, Fits w x) (has : ∀ a ∈ as, Fits w a ∧ a.im = 0)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A + 4)))
    (hL : (S.R 102).length = L) (hwR : (S.R 94).length = w)
    (hx : S.R 110 = cstream A w xs ++ tailX) (ha : S.R 111 = cstream A w as ++ tailA)
    (hrhs : S.R 112 = csyms A w rhs ++ tailR) (hc : CClean mul S)
    (hready : Ready (fun r => S.R (cr r)) w 0)
    (hwork : ∀ k ∈ integerRowWork, S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ L * (rmulCost w + 43 * w + 21) + 14 * w + 55 ∧
      Exec body (integerRowCall hQ) (mk v S) m
        (mk v' { S with R := (Function.update S.R 113
          (csyms A w (rhs - (List.zipWith (· * ·) xs as).sum) ++ S.R 113)) }) := by
  simpa only [tdivN_precision_zero] using
    fixedPointRowCall_exec (body := body) hQ hA hw (by omega : 0 ≤ w) xs as rhs hxlen halen hxs has
      v S tailX tailA tailR hL hwR hx ha hrhs hc hready hwork

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
