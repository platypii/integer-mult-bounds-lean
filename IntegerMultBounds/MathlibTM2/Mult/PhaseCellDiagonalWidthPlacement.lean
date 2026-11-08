module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalPageWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalPageInputs
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Place the existing coefficient width generator on retained diagonal inputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
noncomputable section

@[simp] theorem diagonalWidthTableIndex_ne (i : Fin 392) (hi : 300 ≤ i.val) :
    diagonalTableIndex .wr ≠ i := by
  intro h
  exact diagonalTable_ne_work .wr i hi (congrArg (fun j => recovery (.work j)) h)

@[simp] theorem diagonalWidthTableIndex_ne_symm (i : Fin 392) (hi : 300 ≤ i.val) :
    i ≠ diagonalTableIndex .wr := (diagonalWidthTableIndex_ne i hi).symm

def diagonalWidthSwaps : Role ≃ Role :=
  (Equiv.swap (.inl 0) (.inr (.inl (.work 320)))).trans
  ((Equiv.swap (.inl 1) (.inr (.inl (.work 321)))).trans
  ((Equiv.swap (.inl 2) (.inr (.inl (.work 322)))).trans
  ((Equiv.swap (.inl 3) (.inr (.inl (.work 323)))).trans
  ((Equiv.swap (.inl 4) (.inr (.inl (.work 324)))).trans
  ((Equiv.swap (.inl 94) (.inr (.inl (.control .packet)))).trans
  ((Equiv.swap (.inl 98) (.inr (.inl (.work 311)))).trans
  ((Equiv.swap (.inl 99) (.inr (.inl (.parameter 1)))).trans
  ((Equiv.swap (.inl 100) (.inr (.inl (.work 312)))).trans
  ((Equiv.swap (.inl 102) (.inr (.inl (.parameter 5)))).trans
  ((Equiv.swap (.inl 104) (.inr (.inl (.work 325)))).trans
  ((Equiv.swap (.inl 114) (.inr (.inl (.control .precision)))).trans
    (Equiv.swap (.inl 115) (.inr (.inl (.work (diagonalTableIndex .wr))))))))))))))))

def diagonalWidthReg (i : Fin 117) : Fin tapes :=
  port (diagonalWidthSwaps (.inl i))

theorem diagonalWidthReg_injective : Function.Injective diagonalWidthReg := by
  intro i j h
  exact Sum.inl_injective (diagonalWidthSwaps.injective ((Fintype.equivFin Role).injective h))

def diagonalWidthOne : Fin tapes := recovery (.work 311)
def diagonalWidthZero : Fin tapes := recovery (.work 312)
def diagonalPageRuler : Fin tapes := diagonalTable .wr

def generateLocalDiagonalWidth {Q A : ℕ} {P U : Type} : Pr P tapes Q A U :=
  embProg diagonalWidthReg Empty.elim (generateDiagonalPageWidth (P := Empty))

theorem generateLocalDiagonalWidth_exec {Q A : ℕ} {P U : Type}
    {body : P → Pr P tapes Q A U} (p w u t : ℕ)
    (v : HS tapes Q A U) (S : Stacks tapes A)
    (hp : (S.R (recovery (.control .precision))).length = p)
    (hw : (S.R (recovery (.control .packet))).length = w)
    (hu : (S.R (recovery (.parameter 1))).length = u)
    (ht : (S.R (recovery (.parameter 5))).length = t)
    (hone : (S.R diagonalWidthOne).length = 1)
    (hzero : S.R diagonalWidthZero = [])
    (hblank : S.R diagonalPageRuler = [])
    (hfresh : ∀ i ∈ [(320 : Fin 392),321,322,323,324,325], S.R (recovery (.work i)) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ coefficientWidthCost p w 1 u 0 t + 1 ∧
      Exec body generateLocalDiagonalWidth (mk v S) m
        (mk v' {S with R := (Function.update S.R diagonalPageRuler
          (List.replicate (diagonalPageWidth p w u t) tick))}) := by
  obtain ⟨v₀,m,hv,hm,he⟩ := generateDiagonalPageWidth_exec
    (body := fun f : Empty => nomatch f) p w u t (embDn diagonalWidthReg v)
    (embStk diagonalWidthReg S)
    (by simpa [embStk,diagonalWidthReg,diagonalWidthSwaps,Equiv.swap_apply_def,recovery] using hp)
    (by simpa [embStk,diagonalWidthReg,diagonalWidthSwaps,Equiv.swap_apply_def,recovery] using hw)
    (by simpa [embStk,diagonalWidthReg,diagonalWidthSwaps,Equiv.swap_apply_def,diagonalWidthOne,recovery] using hone)
    (by simpa [embStk,diagonalWidthReg,diagonalWidthSwaps,Equiv.swap_apply_def,recovery] using hu)
    (by simp [embStk,diagonalWidthReg,diagonalWidthSwaps,Equiv.swap_apply_def,diagonalWidthZero,recovery] at hzero ⊢; exact hzero)
    (by simpa [embStk,diagonalWidthReg,diagonalWidthSwaps,Equiv.swap_apply_def,recovery] using ht)
    (by
      intro k hk
      by_cases hk115 : k = 115
      · subst k
        simpa [embStk,diagonalWidthReg,diagonalWidthSwaps,Equiv.swap_apply_def,diagonalPageRuler,diagonalTable,recovery]
          using hblank
      have hk' : k ∈ [(0 : Fin 117),1,2,3,4,104] := by simpa [hk115] using hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk'
      rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simpa [embStk,diagonalWidthReg,diagonalWidthSwaps,Equiv.swap_apply_def,recovery]
        using hfresh _ (by simp))
  obtain ⟨v',_,hv',hex⟩ := exec_emb_ovr (e := diagonalWidthReg)
    diagonalWidthReg_injective (body' := body) (ι := Empty.elim) (fun f => nomatch f)
    he v rfl S rfl
  rw [embOvr_stream diagonalWidthReg diagonalWidthReg_injective] at hex
  refine ⟨v',m,hv'.trans hv,hm,?_⟩
  simpa [generateLocalDiagonalWidth,diagonalPageRuler,diagonalWidthReg,
    diagonalWidthSwaps,Equiv.swap_apply_def,diagonalTable,recovery] using hex

def prepareLocalDiagonalWidth {Q A : ℕ} {P U : Type} : Pr P tapes Q A U :=
  .seq (.act (pushN diagonalWidthOne (fun _ => tick) 1 .done))
    (.seq generateLocalDiagonalWidth (uclear diagonalWidthOne))

theorem prepareLocalDiagonalWidth_native {Q A : ℕ} {P U : Type} :
    mnNativePushBound 16 (prepareLocalDiagonalWidth (P := P) (Q := Q) (A := A) (U := U)) := by
  have hg := embProg_native (e := diagonalWidthReg) (Empty.elim : Empty → P)
    (generateDiagonalPageWidth (P := Empty) (Q := Q) (A := A) (U := U))
    generateDiagonalPageWidth_native
  change mnNativePushBound 16 generateLocalDiagonalWidth at hg
  exact ⟨by simp [mnNativePushBound,mnActPush,pushN],
    hg,by simp [uclear,drainR,peekR,popDo,mnNativePushBound,mnActPush]⟩

theorem prepareLocalDiagonalWidth_exec {Q A : ℕ} {P U : Type}
    {body : P → Pr P tapes Q A U} (p w u t : ℕ)
    (v : HS tapes Q A U) (S : Stacks tapes A)
    (hp : (S.R (recovery (.control .precision))).length = p)
    (hw : (S.R (recovery (.control .packet))).length = w)
    (hu : (S.R (recovery (.parameter 1))).length = u)
    (ht : (S.R (recovery (.parameter 5))).length = t)
    (hfresh : DiagonalFresh S) :
    ∃ v' m, v'.user = v.user ∧ m ≤ coefficientWidthCost p w 1 u 0 t + 6 ∧
      Exec body prepareLocalDiagonalWidth (mk v S) m
        (mk v' {S with R := (Function.update S.R diagonalPageRuler
          (List.replicate (diagonalPageWidth p w u t) tick))}) := by
  let M : Stacks tapes A := {S with R := Function.update S.R diagonalWidthOne [tick]}
  have hone : S.R diagonalWidthOne = [] := hfresh.work 311
  have hpush := Exec.act (body := body) (pushN diagonalWidthOne (fun _ => tick) 1 .done) (mk v S)
  rw [pushN_run] at hpush
  have hpush' : Exec body (.act (pushN diagonalWidthOne (fun _ => tick) 1 .done))
      (mk v S) 1 (mk v M) := by simpa [M,Action.run,hone] using hpush
  have hcontrol (c : RecoveryControl) : recovery (.control c) ≠ diagonalWidthOne := by
    simp [diagonalWidthOne,recovery_injective.eq_iff]
  have hparameter (i : Fin 8) : recovery (.parameter i) ≠ diagonalWidthOne := by
    simp [diagonalWidthOne,recovery_injective.eq_iff]
  obtain ⟨v₁,m,hv,hm,he⟩ := generateLocalDiagonalWidth_exec (body := body) p w u t v M
    (by simpa [M,Function.update_of_ne (hcontrol _)] using hp)
    (by simpa [M,Function.update_of_ne (hcontrol _)] using hw)
    (by simpa [M,Function.update_of_ne (hparameter _)] using hu)
    (by simpa [M,Function.update_of_ne (hparameter _)] using ht)
    (by simp [M])
    (by simpa [M,diagonalWidthZero,diagonalWidthOne,recovery_injective.eq_iff] using hfresh.work 312)
    (by
      have hne : diagonalPageRuler ≠ diagonalWidthOne := diagonalTable_ne_work _ 311 (by decide)
      change Function.update S.R diagonalWidthOne [tick] diagonalPageRuler = []
      rw [Function.update_of_ne hne]
      exact hfresh.table .wr)
    (by
      intro i hi
      have hne : recovery (.work i) ≠ diagonalWidthOne := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        simp [diagonalWidthOne,recovery_injective.eq_iff]
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [M,Function.update_of_ne hne] using hfresh.work i)
  let F : Stacks tapes A := {M with R := (Function.update M.R diagonalPageRuler
    (List.replicate (diagonalPageWidth p w u t) tick))}
  have hne : diagonalWidthOne ≠ diagonalPageRuler := by
    exact (diagonalTable_ne_work _ 311 (by decide)).symm
  obtain ⟨v₂,hv₂,hclear⟩ := uclear_exec (body := body) diagonalWidthOne v₁ F
  have hlen : (F.R diagonalWidthOne).length = 1 := by simp [F,M,hne]
  have hrestore : Function.update F.R diagonalWidthOne [] =
      Function.update S.R diagonalPageRuler (List.replicate (diagonalPageWidth p w u t) tick) := by
    funext k
    by_cases hk : k = diagonalWidthOne
    · subst k; simp [hne,hone]
    · by_cases hr : k = diagonalPageRuler
      · subst k; simp [F,Function.update_of_ne hk]
      · simp [F,M,Function.update_of_ne hk,Function.update_of_ne hr]
  refine ⟨v₂,1+(m+4),hv₂.trans hv,by omega,Exec.seq hpush' (Exec.seq he ?_)⟩
  simpa only [hlen,show 2*1+2 = 4 by decide,hrestore] using hclear

theorem prepareLocalDiagonalWidth_within {Q A : ℕ} {P U : Type}
    {body : P → Pr P tapes Q A U} (p w u t : ℕ)
    (v : HS tapes Q A U) (S : Stacks tapes A)
    (hp : (S.R (recovery (.control .precision))).length = p)
    (hw : (S.R (recovery (.control .packet))).length = w)
    (hu : (S.R (recovery (.parameter 1))).length = u)
    (ht : (S.R (recovery (.parameter 5))).length = t)
    (hfresh : DiagonalFresh S) :
    ∃ v' m, v'.user = v.user ∧ m ≤ coefficientWidthCost p w 1 u 0 t + 6 ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (mk v S)+depth+
        16*(coefficientWidthCost p w 1 u 0 t+6)) depth prepareLocalDiagonalWidth
        (mk v S) m (mk v' {S with R := (Function.update S.R diagonalPageRuler
          (List.replicate (diagonalPageWidth p w u t) tick))}) := by
  obtain ⟨v',m,hv,hm,he⟩ := prepareLocalDiagonalWidth_exec (body := body) p w u t v S hp hw hu ht hfresh
  refine ⟨v',m,hv,hm,fun depth => ?_⟩
  exact mn_native_exec_within he 16 prepareLocalDiagonalWidth_native depth
    (mnSize (mk v S)+depth+16*(coefficientWidthCost p w 1 u 0 t+6)) (by omega)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
