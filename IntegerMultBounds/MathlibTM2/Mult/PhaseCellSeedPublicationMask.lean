module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedPublicationMerge

/-! Copy a retained selector master into disposable count and mask stacks.
The master survives, and one reversal restores the mask's coordinate order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def complementSelector (A : ℕ) (z : Fin (A+4)) : Fin (A+4) :=
  pairSym A (!pairRe z) (!pairRe z)

theorem boundaryMask_complement (hA : 4 ≤ A) (s t band a N : ℕ) :
    (couplingSourceIntervalMaskSymbols true A s t band a (a+N) a N).map (complementSelector A) =
      couplingSourceIntervalMaskSymbols false A s t band a (a+N) a N := by
  simp only [couplingSourceIntervalMaskSymbols,List.map_map]
  apply List.map_congr_left
  intro j hj
  have hjN := List.mem_range.mp hj
  simp [Function.comp_def,complementSelector,pairRe_pairSym hA,haloMaskAt,
    hjN,show a ≤ a+j by omega,show a+j < a+N by omega]

def seedPublicationMask (master count mask reversed tmp : Fin T)
    (f : Fin (A+4) → Fin (A+4)) : Pr P T Q A U :=
  .seq (copyR master count tmp id)
    (.seq (copyR master reversed tmp f) (moveR reversed mask id))

theorem seedPublicationMask_exec (master count mask reversed tmp : Fin T)
    (hreg : [master,count,mask,reversed,tmp].Nodup) (f : Fin (A+4) → Fin (A+4))
    (v : HS T Q A U) (S : Stacks T A)
    (hcount : S.R count = []) (hmask : S.R mask = [])
    (hreversed : S.R reversed = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (seedPublicationMask master count mask reversed tmp f) (mk v S)
        (10*(S.R master).length+10)
        (mk v' {S with R := (Function.update (Function.update S.R count (S.R master).reverse)
          mask ((S.R master).map f))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := copyR_exec (body := body) master count tmp
    ‹master ≠ count› ‹master ≠ tmp› ‹count ≠ tmp› id v S htmp
  let M : Stacks T A := {S with R := Function.update S.R count (S.R master).reverse}
  have he₁' : Exec body (copyR master count tmp id) (mk v S) (4*(S.R master).length+4) (mk v₁ M) := by
    simpa only [List.map_id,hcount,List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := copyR_exec (body := body) master reversed tmp
    ‹master ≠ reversed› ‹master ≠ tmp› ‹reversed ≠ tmp› f v₁ M
    (by simpa [M,‹count ≠ tmp›.symm] using htmp)
  let K : Stacks T A := {M with R := Function.update M.R reversed ((S.R master).map f).reverse}
  have he₂' : Exec body (copyR master reversed tmp f) (mk v₁ M) (4*(S.R master).length+4) (mk v₂ K) := by
    simpa [M,‹master ≠ count›,‹count ≠ reversed›.symm,hreversed] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body reversed mask ‹mask ≠ reversed›.symm id v₂ K
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),(Exec.seq he₁' (Exec.seq he₂' he₃)).cast ?_ ?_⟩
  · simp [K,M,Function.update_apply,‹count ≠ reversed›.symm]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = mask
    · subst k
      simp [K,M,movedR,Function.update_apply,‹mask ≠ reversed›,‹count ≠ reversed›.symm,
        ‹count ≠ mask›.symm,hmask]
    by_cases hr : k = reversed
    · subst k
      simp [K,M,movedR,Function.update_apply,hreversed,‹mask ≠ reversed›.symm,‹count ≠ reversed›.symm]
    · simp [K,M,movedR,Function.update_apply,hk,hr]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
