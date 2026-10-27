module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedFactorFamilyComplexBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFactorBatchReleaseCost

/-! Reuse the existing factor release below the retained-family ports. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 263 Q A U}

noncomputable def familyFactorBatchRelease : Pr P 263 Q A U :=
  embProg familyInverseLegacyReg Empty.elim (placedFactorBatchRelease (P := Empty))

def familyFactorBatchOwnedRegs : List (Fin 263) :=
  placedFactorBatchOwnedRegs.map familyInverseLegacyReg

def familyFactorBatchReleaseResult {A : ℕ} (S : Stacks 263 A) (rows : ℕ)
    (result tail : List (Fin (A+4))) : Stacks 263 A :=
  embOvr familyInverseLegacyReg
    (placedFactorBatchReleaseResult (embStk familyInverseLegacyReg S) rows result tail).get S

theorem familyFactorBatchRelease_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (N W w V D H : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (result tail : List (Fin (A+4))) (hresult : result.length = (N*s)*w)
    (v : HS 263 Q A U) (S : Stacks 263 A)
    (hs : (S.R 121).length = s) (hcount : (S.R 246).length = N)
    (hW : (S.R 190).length = W) (hN : (S.R 116).length = B.card) (hw : (S.R 160).length = w)
    (hsource : S.R 132 = result++(bandTableWords A w B W columns 0++tail))
    (hfresh : ∀ i ∈ ([152,151,131,134,135,136,137,138,231,232,233,237] : List (Fin 240)),
      S.R (familyBoundaryReg i) = [])
    (h240 : S.R 240 = []) (h244 : S.R 244 = []) (h245 : S.R 245 = [])
    (hvolume : (sharedPageOwnedRegs.map fun i => ((embStk familyBoundaryReg S).R i).length).sum ≤
      sharedPageOwnedVolumeBound s w V B.card D H) :
    ∃ v' n, v'.user = v.user ∧ n ≤ placedFactorBatchReleaseCostBound s N B.card W w V D H ∧
      Exec body familyFactorBatchRelease (mk v S) n
        (mk v' (familyFactorBatchReleaseResult S (N*s) result tail)) := by
  obtain ⟨vi,n,hui,hn,hei⟩ := placedFactorBatchRelease_exec
    (body := fun p : Empty => nomatch p) B N W w columns hlen result tail hresult
    (embDn familyInverseLegacyReg v) (embStk familyInverseLegacyReg S)
    hs hcount hW hN hw hsource hfresh h240 h244 h245
  obtain ⟨v',hv,hu',he⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    familyInverseLegacyReg_injective (fun p => nomatch p) hei v rfl S rfl
  exact ⟨v',n,hu'.trans hui,hn.trans (placedFactorBatchReleaseCost_le
    (embStk familyInverseLegacyReg S) hvolume),he⟩

private theorem legacy_overlay_restore {A : ℕ} (original S : Stacks 263 A)
    (hL : ∀ i : Fin 263, 256 ≤ i.val → S.L i = original.L i)
    (hR : ∀ i : Fin 263, 256 ≤ i.val → S.R i = original.R i) :
    embOvr familyInverseLegacyReg (embStk familyInverseLegacyReg original).get S = original := by
  have hproject := embStk_ovr familyInverseLegacyReg_injective (embStk familyInverseLegacyReg original) S
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    by_cases hi : i.val < 256
    · let j : Fin 256 := ⟨i.val,hi⟩
      have hj : familyInverseLegacyReg j = i := Fin.ext rfl
      rw [← hj]
      exact congrArg (fun X : Stacks 256 A => X.L j) hproject
    · exact (embOvr_off (e := familyInverseLegacyReg) _ S (by
        intro j he; have hv := congrArg Fin.val he
        dsimp [familyInverseLegacyReg] at hv; omega)).1.trans (hL i (by omega))
  · funext i
    by_cases hi : i.val < 256
    · let j : Fin 256 := ⟨i.val,hi⟩
      have hj : familyInverseLegacyReg j = i := Fin.ext rfl
      rw [← hj]
      exact congrArg (fun X : Stacks 256 A => X.R j) hproject
    · exact (embOvr_off (e := familyInverseLegacyReg) _ S (by
        intro j he; have hv := congrArg Fin.val he
        dsimp [familyInverseLegacyReg] at hv; omega)).2.trans (hR i (by omega))

theorem familyFactorBatchReleaseResult_restore {A : ℕ} (original S : Stacks 263 A) (rows : ℕ)
    (result : List (Fin (A+4))) (h240 : S.R 240 = [])
    (hinp : S.inp = original.inp) (hout : S.out = original.out) (hL : S.L = original.L)
    (hframe : ∀ i, i ∉ familyFactorBatchOwnedRegs → i ≠ 132 → S.R i = original.R i)
    (howned : ∀ i ∈ familyFactorBatchOwnedRegs, original.R i = []) :
    familyFactorBatchReleaseResult S rows result (original.R 132) =
      {original with R := Function.update original.R 132 (result++original.R 132)} := by
  have hlegacy := placedFactorBatchReleaseResult_restore (embStk familyInverseLegacyReg original)
    (embStk familyInverseLegacyReg S) rows result h240 hinp hout
    (congrArg (fun L => L ∘ familyInverseLegacyReg) hL) (by
      intro i hi hi132
      apply hframe
      · intro hh
        obtain ⟨j,hj,he⟩ := List.mem_map.mp hh
        exact hi (familyInverseLegacyReg_injective he ▸ hj)
      · exact familyInverseLegacyReg_injective.ne hi132) (by
      intro i hi
      exact howned _ (List.mem_map.mpr ⟨i,hi,rfl⟩))
  change placedFactorBatchReleaseResult (embStk familyInverseLegacyReg S) rows result (original.R 132) = _ at hlegacy
  unfold familyFactorBatchReleaseResult
  rw [hlegacy,embOvr_updR familyInverseLegacyReg_injective]
  have hbase : embOvr familyInverseLegacyReg (embStk familyInverseLegacyReg original).get S = original := by
    apply legacy_overlay_restore
    · intro i _; exact congrFun hL i
    · intro i hi
      apply hframe
      · intro hh
        obtain ⟨j,hj,he⟩ := List.mem_map.mp hh
        have hv := congrArg Fin.val he
        dsimp [familyInverseLegacyReg] at hv
        omega
      · intro he; subst i; norm_num at hi
  rw [hbase]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
