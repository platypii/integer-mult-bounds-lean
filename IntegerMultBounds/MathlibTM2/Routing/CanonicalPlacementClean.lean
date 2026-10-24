module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalPlacementSerialize

/-! Restore exactly the thirty generated placement words. Original inputs,
carry-stack contents and arbitrary spectators are excluded from cleanup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def canonicalPlacementTargets : List (Fin 53) :=
  [1,2,11,14,16,17,18,19,20,21,22,23,24,26,27,28,32,33,
    34,35,36,37,38,39,40,41,42,50,51,52]

private theorem update_length_le (R : Fin T → List (Fin (A+4))) (i j : Fin T)
    (word : List (Fin (A+4))) (C : ℕ) (hR : (R i).length ≤ C) (hw : word.length ≤ C) :
    (Function.update R j word i).length ≤ C := by
  by_cases h : i = j
  · simpa [h] using hw
  · simpa [Function.update_of_ne h] using hR

private theorem resizeBank_length_le {J : Type} (R : Fin T → List (Fin (A+4)))
    (rg : J → Fin 9 → Fin T) (W x : J → ℕ) (jobs : List J) (i : Fin T) (C : ℕ)
    (hR : (R i).length ≤ C) (hW : ∀ j, W j ≤ C) :
    (binaryResizeBatchBank R rg W x jobs i).length ≤ C := by
  induction jobs with
  | nil => exact hR
  | cons j jobs ih =>
    apply update_length_le _ _ _ _ _ ih
    simpa only [length_binSyms] using hW j

theorem canonicalPlacementScalarBank_length_le (R : Fin T → List (Fin (A+4)))
    (rg : Fin 53 → Fin T) (L Lb n B : ℕ) (hn : n < 2^L) (hB : B < 2^Lb)
    (hlarge : canonicalRouterStride n ≤ n) (k : Fin 3) (i : Fin T)
    (hR : (R i).length ≤ L+Lb+1) :
    (canonicalPlacementScalarBank R rg L n B hlarge k i).length ≤ L+Lb+1 := by
  have hL : L ≤ L+Lb+1 := by omega
  have hnW : canonicalScalarWidth n ≤ L+Lb+1 :=
    (Nat.clog_le_of_le_pow (Nat.succ_le_of_lt hn)).trans hL
  have hBW : canonicalScalarWidth B ≤ L+Lb+1 :=
    (Nat.clog_le_of_le_pow (Nat.succ_le_of_lt hB)).trans (by omega)
  unfold canonicalPlacementScalarBank headerScalarBank
  apply update_length_le
  · apply update_length_le
    · apply update_length_le
      · apply resizeBank_length_le
        · simp only [canonicalPlacementWidthBank,canonicalPlacementOperandBank,
            reservoirExchangeOperandBank,reservoirExchangeOperandJobs,List.foldl_cons,List.foldl_nil,
            canonicalGeometryBank,routerReservoirGeometryBank,routerGeometryBank,Function.comp_apply]
          repeat apply update_length_le
          all_goals first | exact hR | simpa only [length_binSyms] using hL
        · intro j; exact hnW
      · simp
    · simpa only [length_binSyms] using hnW
  · simpa only [length_binSyms] using hBW

theorem canonicalPlacementCleanCost_le (R : Fin T → List (Fin (A+4)))
    (rg : Fin 53 → Fin T) (L Lb n B : ℕ) (hn : n < 2^L) (hB : B < 2^Lb)
    (hlarge : canonicalRouterStride n ≤ n) (k : Fin 3)
    (hblank : ∀ i ∈ canonicalPlacementTargets, R (rg i) = []) :
    metadataCleanCost (canonicalPlacementScalarBank R rg L n B hlarge k)
      (canonicalPlacementTargets.map rg) ≤ 60*L+60*Lb+121 := by
  have he := metadataCleanCost_le (canonicalPlacementScalarBank R rg L n B hlarge k)
    (canonicalPlacementTargets.map rg) (L+Lb+1) (by
      intro i hi
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
      apply canonicalPlacementScalarBank_length_le R rg L Lb n B hn hB hlarge k
      rw [hblank j hj]
      simp)
  simp only [List.length_map,canonicalPlacementTargets,List.length_cons,List.length_nil] at he
  dsimp only [canonicalPlacementTargets]
  omega

theorem canonicalPlacementScalarBank_keep (R : Fin T → List (Fin (A+4)))
    (rg : Fin 53 → Fin T) (L n B : ℕ) (hlarge : canonicalRouterStride n ≤ n) (k : Fin 3)
    (i : Fin T) (hi : i ∉ canonicalPlacementTargets.map rg) :
    canonicalPlacementScalarBank R rg L n B hlarge k i = R i := by
  have off (j : Fin 53) (hj : j ∈ canonicalPlacementTargets) : i ≠ rg j := by
    intro h
    exact hi (h ▸ List.mem_map.mpr ⟨j,hj,rfl⟩)
  unfold canonicalPlacementScalarBank headerScalarBank
  dsimp only [Function.comp_apply,canonicalPlacementScalarSlot]
  rw [Function.update_of_ne (off 51 (by decide +kernel))]
  change Function.update (Function.update
    (canonicalPlacementResizedBank R (rg ∘ canonicalPlacementScalarCore) L n hlarge k)
    (rg 52) [bitSymbol true]) (rg 50) (binSyms (canonicalScalarWidth n) n) i = R i
  rw [Function.update_of_ne (off 50 (by decide +kernel))]
  rw [Function.update_of_ne (off 52 (by decide +kernel))]
  rw [show canonicalPlacementResizedBank R (rg ∘ canonicalPlacementScalarCore) L n hlarge k i =
      canonicalPlacementWidthBank R (rg ∘ canonicalPlacementScalarCore ∘ canonicalPlacementResizeCore) L n i from by
    apply binaryResizeBatchBank_keep
    intro h
    obtain ⟨j,_,he⟩ := List.mem_map.mp h
    exact off ⟨34+j.val,by have := j.isLt; omega⟩
      (by fin_cases j <;> simp [canonicalPlacementTargets,Fin.ext_iff]) he.symm]
  simp only [canonicalPlacementWidthBank,canonicalPlacementOperandBank,reservoirExchangeOperandBank,
    reservoirExchangeOperandJobs,List.foldl_cons,List.foldl_nil,canonicalGeometryBank,
    routerReservoirGeometryBank,routerGeometryBank,Function.comp_apply]
  repeat rw [Function.update_of_ne (off _ (by decide +kernel))]

theorem canonicalPlacementScalarBank_restore (R : Fin T → List (Fin (A+4)))
    (rg : Fin 53 → Fin T) (L n B : ℕ) (hlarge : canonicalRouterStride n ≤ n) (k : Fin 3)
    (hblank : ∀ i ∈ canonicalPlacementTargets, R (rg i) = []) :
    metadataCleared (canonicalPlacementScalarBank R rg L n B hlarge k)
      (canonicalPlacementTargets.map rg) = R := by
  funext i
  by_cases hi : i ∈ canonicalPlacementTargets.map rg
  · rw [metadataCleared_at _ _ _ hi]
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    exact (hblank j hj).symm
  · rw [metadataCleared_keep _ _ _ hi]
    exact canonicalPlacementScalarBank_keep R rg L n B hlarge k i hi

theorem canonicalPlacementClean_exec (body : P → Pr P T Q A U)
    (rg : Fin 53 → Fin T) (hrg : Function.Injective rg) (L n B : ℕ)
    (hlarge : canonicalRouterStride n ≤ n) (k : Fin 3) (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i ∈ canonicalPlacementTargets, S.R (rg i) = [])
    (dst : Fin T) (hoff : ∀ i, rg i ≠ dst) (output : List (Fin (A+4))) :
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean (canonicalPlacementTargets.map rg))
        (mk v { S with R := Function.update (canonicalPlacementScalarBank S.R rg L n B hlarge k) dst output })
        (metadataCleanCost (canonicalPlacementScalarBank S.R rg L n B hlarge k) (canonicalPlacementTargets.map rg))
        (mk v' { S with R := Function.update S.R dst output }) := by
  apply metadataClean_framed_exec body _ _ _ _
    (canonicalPlacementScalarBank_restore S.R rg L n B hlarge k hblank) dst _ output v S
  · exact List.Nodup.map hrg (by decide +kernel)
  · intro h
    obtain ⟨i,_,he⟩ := List.mem_map.mp h
    exact hoff i he

end
end IntegerMultBounds.MathlibTM2.Routing
