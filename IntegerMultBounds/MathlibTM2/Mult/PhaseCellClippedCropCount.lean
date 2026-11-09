module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryCounterRestore
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryCounterSeedLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableRetirement
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Export only the final clipped crop count. The existing boundary arithmetic
and table restoration are reused; no unary skip word is materialized. -/
@[expose] public section
set_option autoImplicit false
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.BoundaryCropMetadata
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A : ℕ} {P U : Type}

def clippedCropCount (rg : TblR 9 → Fin T) (count : Fin T) : Pr P T Q A U :=
  .seq (.seq (tblCompile rg (code true)) (tblUnaryCopies rg [(8,count)])) (tblCompile rg restoreCode)

def clippedCropCountCost (D s width W : ℕ) :=
  16*tblC D 0+6*(coreLength s width (boundaryCropIndex s width 2)*W)+11*D+7

theorem clippedCropCount_exec (body : P → Pr P T Q A U)
    (rg : TblR 9 → Fin T) (hinj : Function.Injective rg) (count : Fin T) (hoff : ∀ i, rg i ≠ count)
    (D s width W : ℕ) (st : TblSt 9 A)
    (hs : st.val 0 = s) (hw : st.val 1 = width) (hW : st.val 2 = W)
    (hwidth : 0 < width) (hword : 0 < W) (hroom : 3*width < s)
    (hfit : s*W < 2^D) (hvalues : ∀ j, st.val j < 2^D)
    (hzero : ∀ i : Fin 9, 3 ≤ i.val → st.val i = 0)
    (wl : List (Fin (A+4))) (hwl : wl.length = D)
    (v : HS T Q A U) (S : Stacks T A)
    (hholds : tblHolds rg S (tblRho D wl [] st)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ clippedCropCountCost D s width W ∧
      Exec body (clippedCropCount rg count) (mk v S) n
        (mk v' {S with R := (Function.update S.R count
          (List.replicate (coreLength s width (boundaryCropIndex s width 2)*W) tick++S.R count))}) := by
  obtain ⟨z,⟨heq,hfitZ⟩,hrun⟩ := (tblDo_with_fits
    (code_do true D s width W A st hs hw hW hwidth hword hroom hfit) hvalues).host
      (body := body) hinj wl [] hwl rfl (Nat.zero_le D) hvalues
  have hcountValue : z.val 8 = coreLength s width (boundaryCropIndex s width 2)*W := by
    have h := (run_spec true D s width W A st hs hw hW hwidth hword hroom hfit).2.2
    rw [←heq,index_eq_boundary true s width hwidth hroom] at h
    exact h
  have hkeep := run_inputs true A st
  rw [←heq] at hkeep
  obtain ⟨v₁,F,n₁,hu₁,hn₁,he₁,hh₁,hframe⟩ := hrun v S hholds
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := tblUnaryCopies_exec (body := body) hinj wl [] z hfitZ [(8,count)]
    (by intro pair hp i; simp only [List.mem_singleton] at hp; subst pair; exact hoff i) v₁ F hh₁
  let M : Stacks T A := {F with R := unaryCopiesR z.val F.R [(8,count)]}
  have hread (i : Fin T) (hi : i ≠ count) : M.R i = F.R i := by
    simp only [M,unaryCopiesR,Function.update_of_ne hi]
  have hhM : tblHolds rg M (tblRho D wl [] z) := by
    intro i
    rw [hread _ (hoff i)]
    exact hh₁ i
  have hkept (i : Fin 9) (hi : i.val < 3) : z.val i = st.val i := by
    have he : i = Fin.castAdd 6 (⟨i.val,hi⟩ : Fin 3) := Fin.ext rfl
    rw [he]
    exact hkeep.1 _
  obtain ⟨v',G,n₃,hu₃,hn₃,he₃,hhG,hGi,hGo,hGl,hGframe⟩ := restoreCode_exec body rg hinj D z st
    hkept hzero hkeep.2 hfitZ wl hwl v₂ M hhM
  have hend : G = {S with R := (Function.update S.R count
      (List.replicate (coreLength s width (boundaryCropIndex s width 2)*W) tick++S.R count))} := by
    refine Stacks.ext (hGi.trans hframe.1) (hGo.trans hframe.2.1) (hGl.trans hframe.2.2.1) ?_
    funext i
    by_cases hc : i = count
    · subst i
      rw [hGframe count hoff]
      simp only [M,unaryCopiesR,Function.update_self,hcountValue,hframe.2.2.2 count hoff]
    · have hequal : G.R i = S.R i := by
        by_cases ht : ∃ j, rg j = i
        · obtain ⟨j,rfl⟩ := ht
          exact (hhG j).trans (hholds j).symm
        · have hbank : ∀ j, rg j ≠ i := by simpa only [not_exists] using ht
          exact ((hGframe i hbank).trans (hread i hc)).trans (hframe.2.2.2 i hbank)
      simpa only [Function.update_of_ne hc] using hequal
  have htime : n₁+n₂+n₃ ≤ clippedCropCountCost D s width W := by
    simp only [List.length_nil] at hn₁
    simp only [unaryCopiesCost,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hcountValue] at hn₂
    unfold clippedCropCountCost
    omega
  refine ⟨v',n₁+n₂+n₃,hu₃.trans (hu₂.trans hu₁),htime,?_⟩
  exact (Exec.seq (Exec.seq he₁ he₂) he₃).cast rfl (congrArg (mk v') hend)

theorem clippedCropCount_native (rg : TblR 9 → Fin T) (count : Fin T) :
    mnNativePushBound 3 (clippedCropCount (P := P) (Q := Q) (A := A) (U := U) rg count) :=
  ⟨⟨tblCompile_native _ _,tblUnaryCopies_native _ _⟩,tblCompile_native _ _⟩

def preparedClippedCropCount (rg : TblR 9 → Fin T) (globals : Fin 3 → Fin T)
    (zero ruler count : Fin T) : Pr P T Q A U :=
  .seq (.seq (chirpBankLoad rg (seedSources globals zero) ruler zero) (clippedCropCount rg count))
    (clearWords (inputTableWords rg))

def preparedClippedCropCountCost (D s width W : ℕ) :=
  (64*D+81)+clippedCropCountCost D s width W+(20*D+21)

theorem preparedClippedCropCount_exec_within (body : P → Pr P T Q A U)
    (rg : TblR 9 → Fin T) (hinj : Function.Injective rg) (globals : Fin 3 → Fin T)
    (zero ruler count : Fin T) (hcountOff : ∀ i, rg i ≠ count)
    (hrulerOff : ∀ i, rg i ≠ ruler) (hzeroOff : ∀ i, rg i ≠ zero)
    (hglobalsOff : ∀ j i, rg i ≠ globals j) (hglobalsZero : ∀ j, globals j ≠ zero)
    (D s width W : ℕ) (hwidth : 0 < width) (hword : 0 < W) (hroom : 3*width < s)
    (hfit : s*W < 2^D) (value : Fin T → ℕ)
    (hvalues : ∀ j, value (globals j) = ![s,width,W] j) (hfits : ∀ j, value (globals j) < 2^D)
    (v : HS T Q A U) (S : Stacks T A) (hruler : (S.R ruler).length = D) (hzero : S.R zero = [])
    (hwords : ∀ j, S.R (globals j) = binSyms D (value (globals j)))
    (hblank : ∀ i, S.R (rg i) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedClippedCropCountCost D s width W ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        3*preparedClippedCropCountCost D s width W) depth (preparedClippedCropCount rg globals zero ruler count)
        (mk v S) n (mk v' {S with R := (Function.update S.R count
          (List.replicate (coreLength s width (boundaryCropIndex s width 2)*W) tick++S.R count))}) := by
  obtain ⟨v₁,hu₁,he₁,hh₁⟩ := loadSeed_exec body rg hinj globals zero ruler hrulerOff hzeroOff
    hglobalsOff hglobalsZero D s width W value hvalues hfits v S hruler hzero hwords hblank depth
  let M := loadedInputTable rg (seedSources globals zero) D (seedSourceValue value zero) S
  obtain ⟨v₂,n₂,hu₂,hn₂,hex₂⟩ := clippedCropCount_exec body rg hinj count hcountOff D s width W
    (seed A s width W) (by simp [seed]) (by simp [seed]) (by simp [seed])
    hwidth hword hroom hfit
    (seed_fits A D s width W (by omega) hword (by omega) hfit) (seed_working_zero A s width W)
    (List.replicate D tick) (by simp) v₁ M hh₁
  have hreadCount : M.R count = S.R count :=
    loadedInputTable_off rg (seedSources globals zero) D (seedSourceValue value zero) S count
      (fun i => (hcountOff i).symm)
  have he₂ := mn_native_exec_within hex₂ 3 (clippedCropCount_native ..) depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hn₂) _)
  obtain ⟨v',hu₃,he₃⟩ := retireInputTable_exec_within body rg hinj (seedSources globals zero) D
    (seedSourceValue value zero) count hcountOff
    (List.replicate (coreLength s width (boundaryCropIndex s width 2)*W) tick++S.R count) v₂ S hblank depth
  have he₂' : ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v₁ M)+depth+
      3*clippedCropCountCost D s width W) depth (clippedCropCount rg count) (mk v₁ M) n₂
      (mk v₂ {M with R := (Function.update M.R count
        (List.replicate (coreLength s width (boundaryCropIndex s width 2)*W) tick++S.R count))}) := by
    simpa only [hreadCount] using he₂
  have he₃' := he₃
  simp only [Nat.reduceMul,Nat.reduceAdd] at he₃'
  have hex := mn_seq_within_add (mn_seq_within_add he₁ he₂') he₃'
  refine ⟨v',(64*D+81)+n₂+(20*D+21),hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · unfold preparedClippedCropCountCost
    omega
  · exact hex.mono (by
      intro z state hz
      simp only [preparedClippedCropCountCost,Nat.mul_add,Nat.add_zero] at hz ⊢
      omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.BoundaryCropMetadata
