module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedClassCallerReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryHeaderFormat

/-! Export the generated halo in the geometry format and establish the selected
call's physical readiness with an independently wider table format. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  CommonClassGeometry
variable {N Q A : ℕ} {P U : Type}

theorem generatedHeaderReady_exec_within (body : P → Pr P N Q A U)
    (bank : ComputedClassBank → Fin N) (rg : TblR 12 → Fin N)
    (src : Fin 4 → Fin N) (masters : Fin 12 → Fin N)
    (hinj : Function.Injective masters) (widthMaster zeroMaster count saved tmp : Fin N)
    (hcopy : [count,masters 11,src 3,saved,tmp].Nodup)
    (B D : ℕ) (hBD : B ≤ D) (clipped : Bool)
    (p u l target s t W rowCount radius width : ℕ) (value : Fin N → ℕ)
    (v : HS N Q A U) (S : Stacks N A)
    (hvalues : ∀ j, value (masters j) =
      commonInputValues p u l target s t B W rowCount radius (haloRows clipped s width radius) j)
    (hprefix : ∀ j, j ≠ 10 → j ≠ 11 → S.R (masters j) =
      binSyms D (seedValues p u l target s t B W rowCount radius width (Fin.castAdd 1 j)))
    (hgeometryOff : ∀ j, j ≠ 3 → src j ≠ masters 10 ∧ src j ≠ masters 11 ∧ src j ≠ src 3)
    (hgeometry : ∀ j, j ≠ 3 → S.R (src j) =
      binSyms B (![s,width,radius,haloRows clipped s width radius] j))
    (hmastersOff : ∀ j, masters j ≠ src 3)
    (hwidthOff : widthMaster ≠ masters 10 ∧ widthMaster ≠ masters 11 ∧ widthMaster ≠ src 3)
    (hzeroOff : zeroMaster ≠ masters 10 ∧ zeroMaster ≠ masters 11 ∧ zeroMaster ≠ src 3)
    (htableOff : ∀ r, rg r ≠ masters 10 ∧ rg r ≠ masters 11 ∧ rg r ≠ src 3)
    (hbankOff : ∀ j, bank j ≠ masters 10 ∧ bank j ≠ masters 11 ∧ bank j ≠ src 3)
    (hwidth : (S.R widthMaster).length = D) (hzero : S.R zeroMaster = [])
    (htable : ∀ r, S.R (rg r) = [])
    (hbank : ∀ j, j ≠ .control .source → S.R (bank j) = [])
    (hleft : ∀ j, S.L (recovery bank (.work j)) = [])
    (hworkOff : ∀ k ∈ [count,saved,tmp], k ≠ masters 10 ∧ k ≠ masters 11)
    (hcount : (S.R count).length = B) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hdst : S.R (src 3) = []) (depth : ℕ) :
    let M := masterLoaded (masters 10) (masters 11) D clipped s width radius S
    let F := {M with R := Function.update M.R (src 3) (binSyms B (haloRows clipped s width radius))}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v M)+depth+3*(10*B+10)) depth
        (copyPrefix count (masters 11) (src 3) saved tmp) (mk v M) (10*B+10) (mk v' F) ∧
      ClassCallerReady bank rg src masters widthMaster zeroMaster B D s width radius
        (haloRows clipped s width radius) value F := by
  dsimp only
  let M := masterLoaded (masters 10) (masters 11) D clipped s width radius S
  let F : Stacks N A := {M with R := Function.update M.R (src 3) (binSyms B (haloRows clipped s width radius))}
  have hM (k : Fin N) (hk : k ≠ masters 10 ∧ k ≠ masters 11) : M.R k = S.R k :=
    masterLoaded_right_off _ _ _ _ _ _ _ _ _ hk.1 hk.2
  have hF (k : Fin N) (hk : k ≠ masters 10 ∧ k ≠ masters 11 ∧ k ≠ src 3) : F.R k = S.R k :=
    (Function.update_of_ne hk.2.2 _ _).trans (hM k ⟨hk.1,hk.2.1⟩)
  have hword := masterLoaded_words masters hinj D clipped p u l target s t B W rowCount radius width S hprefix
  obtain ⟨v',hu,he⟩ := copyBinaryHeader_exec_within body count (masters 11) (src 3) saved tmp hcopy
    B D (haloRows clipped s width radius) hBD v M
    (by rw [hM count (hworkOff count (by simp))]; exact hcount)
    (by simp [M,masterLoaded])
    ((hM (src 3) ⟨(hmastersOff 10).symm,(hmastersOff 11).symm⟩).trans hdst)
    ((hM saved (hworkOff saved (by simp))).trans hsaved)
    ((hM tmp (hworkOff tmp (by simp))).trans htmp) depth
  refine ⟨v',hu,he,?_,?_,?_,?_,?_,?_,hleft⟩
  · intro j
    by_cases hj : j = 3
    · subst j; simp
    · exact (hF _ (hgeometryOff j hj)).trans (hgeometry j hj)
  · rw [hF _ hwidthOff]; exact hwidth
  · exact (hF _ hzeroOff).trans hzero
  · intro j
    change Function.update M.R (src 3) _ (masters j) = _
    rw [Function.update_of_ne (hmastersOff j),hvalues j]
    exact hword j
  · intro r; exact (hF _ (htableOff r)).trans (htable r)
  · intro j hj; exact (hF _ (hbankOff j)).trans (hbank j hj)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
