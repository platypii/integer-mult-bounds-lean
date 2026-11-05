module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryCropCounters

/-! Restore the small metadata bank after exporting the two seam masters.
The three original inputs and accumulator are retained. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.BoundaryCropMetadata
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def restoreCode : TblCode 9 :=
  tblBlock 9 [.zero 3,.zero 4,.zero 5,.zero 6,.zero 7] (.zero 8)

theorem restoreCode_do {A W e : ℕ} (st initial : TblSt 9 A)
    (hkeep : ∀ i : Fin 9, i.val < 3 → st.val i = initial.val i)
    (hzero : ∀ i : Fin 9, 3 ≤ i.val → initial.val i = 0)
    (hacc : st.acc = initial.acc) :
    TblDo A W e restoreCode st (fun z => z = initial) 6 := by
  have hr : TblDo A W e restoreCode st
      (fun z => z.val = initial.val ∧ z.acc = initial.acc) 6 := by
    apply TblDo.block
    · simp [tblFitsList,TblIns.fits,TblIns.exact]
    · refine ⟨?_,hacc⟩
      funext i
      fin_cases i <;> simp only [tblExactList,TblIns.exact,Function.update_apply,Fin.reduceEq,ite_true,ite_false]
      all_goals first | exact hkeep _ (by decide) | exact (hzero _ (by decide)).symm
  exact hr.mono (fun z ⟨hv,ha⟩ => by
    cases z
    cases initial
    dsimp only at hv ha
    cases hv
    cases ha
    rfl) (le_refl _)

open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main

/-- Execute cleanup while leaving exported master tapes outside the table intact. -/
theorem restoreCode_exec {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (rg : TblR 9 → Fin T) (hinj : Function.Injective rg)
    (D : ℕ) (st initial : TblSt 9 A)
    (hkeep : ∀ i : Fin 9, i.val < 3 → st.val i = initial.val i)
    (hzero : ∀ i : Fin 9, 3 ≤ i.val → initial.val i = 0) (hacc : st.acc = initial.acc)
    (hvalues : ∀ i, st.val i < 2^D)
    (wl : List (Fin (A+4))) (hwl : wl.length = D)
    (v : HS T Q A U) (S : Stacks T A)
    (hholds : tblHolds rg S (tblRho D wl [] st)) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ 6*tblC D 0 ∧
      Exec body (tblCompile rg restoreCode) (mk v S) n (mk v' F) ∧
      tblHolds rg F (tblRho D wl [] initial) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, (∀ r, rg r ≠ k) → F.R k = S.R k := by
  obtain ⟨z,hz,hrun⟩ := (restoreCode_do (W := D) (e := 0) st initial hkeep hzero hacc).host
    (body := body) hinj wl [] hwl rfl (Nat.zero_le D) hvalues
  subst z
  obtain ⟨v',F,n,hu,hn,he,hh,hframe⟩ := hrun v S hholds
  refine ⟨v',F,n,hu,?_,he,hh,hframe⟩
  simpa only [List.length_nil] using hn

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.BoundaryCropMetadata
