module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClippedCropCount
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedHeaderList
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyWordHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderFrameRetirement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStandardBoundaryCounters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStandardBoundarySeedLoad

/-! Construct the last crop master from ordinary s/core binary words and a
borrowed unary narrow width. All temporary seed words and table data retire. -/
@[expose] public section
set_option autoImplicit false
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix BoundaryCropMetadata
variable {Q A : ℕ} {P U : Type}

def lastCropSeedPairs (masters : Fin 11 → Fin 117) : List (Fin 117 × Fin 117) :=
  [(masters 4,55),(masters 5,56),(masters 7,58)]

def boundaryLastCropMaster (masters : Fin 11 → Fin 117) : Pr P 117 Q A U :=
  .seq (.seq (.seq (copyWordHeaders 27 28 (lastCropSeedPairs masters))
    (paddedHeaderList 58 19 20 21 22 23 25 [(masters 3,57)]))
    (preparedClippedCropCount boundaryCounterRegister boundarySeedGlobals 59 58 (masters 10)))
    (clearWords [55,56,57,58])

def boundaryLastCropMasterCost (D s width w : ℕ) :=
  (18*D+19)+(21*w+12*D+29)+preparedClippedCropCountCost D s width w+(8*D+9)

theorem boundaryLastCropMaster_exec_within (body : P → Pr P 117 Q A U)
    (masters : Fin 11 → Fin 117)
    (hprivate : ∀ i, 63 ≤ (masters i).val)
    (D s width w : ℕ) (hwidth : 0 < width) (hword : 0 < w) (hroom : 3*width < s)
    (hfit : s*w < 2^D) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hs : S.R (masters 4) = binSyms D s) (hw : S.R (masters 5) = binSyms D width)
    (hruler : (S.R (masters 7)).length = D) (hnarrow : (S.R (masters 3)).length = w)
    (hcount : S.R (masters 10) = []) (hblank : ∀ i, i.val < 63 → S.R i = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ boundaryLastCropMasterCost D s width w ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        3*boundaryLastCropMasterCost D s width w) depth (boundaryLastCropMaster masters)
        (mk v S) n (mk v' {S with R := (Function.update S.R (masters 10)
          (List.replicate (coreLength s width (boundaryCropIndex s width 2)*w) tick))}) := by
  have hmasterOff (i : Fin 11) (k : Fin 117) (hk : k.val < 63) : masters i ≠ k := by
    intro he
    have hp := hprivate i
    have hv := congrArg Fin.val he
    omega
  have hpair (i : Fin 11) (k : Fin 117) (hk : k.val < 63) (h27 : k ≠ 27) (h28 : k ≠ 28) :
      [masters i,k,27,28].Nodup := by
    simp [hmasterOff i k hk,hmasterOff i 27 (by decide),hmasterOff i 28 (by decide),h27,h28]
  obtain ⟨v₁,hu₁,hex₁⟩ := copyWordHeaders_exec (body := body) 27 28 (lastCropSeedPairs masters)
    (by intro pair hp; simp only [lastCropSeedPairs,List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with rfl | rfl | rfl
        all_goals exact hpair _ _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide))
    (by intro pair hp other ho
        simp only [lastCropSeedPairs,List.mem_cons,List.not_mem_nil,or_false] at hp ho
        rcases hp with rfl | rfl | rfl
        all_goals rcases ho with rfl | rfl | rfl
        all_goals exact (hmasterOff _ _ (by dsimp only; decide)).symm)
    S.R v S (by intro pair hp; rfl) (hblank 27 (by decide)) (hblank 28 (by decide))
  let M : Stacks 117 A := {S with R := copyWordHeadersR S.R (lastCropSeedPairs masters) S.R}
  have hcopyOff (i : Fin 117) (hi : i ∉ [(55 : Fin 117),56,58]) : M.R i = S.R i := by
    apply copyWordHeadersR_off
    intro pair hp he
    apply hi
    have hmap : (lastCropSeedPairs masters).map Prod.snd = [55,56,58] := rfl
    rw [←hmap]
    exact List.mem_map.mpr ⟨pair,hp,he⟩
  have hcopyCost : ((lastCropSeedPairs masters).map (fun pair => 6*(S.R pair.1).length+6)).sum+1 = 18*D+19 := by
    simp only [lastCropSeedPairs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hs,hw,hruler,length_binSyms]
    omega
  have he₁ : ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+2*(18*D+19)) depth
      (copyWordHeaders 27 28 (lastCropSeedPairs masters)) (mk v S) (18*D+19) (mk v₁ M) := by
    rw [hcopyCost] at hex₁
    exact mn_native_exec_within hex₁ 2 (copyWordHeaders_native _ _ _) depth _ (le_refl _)
  have h55 : M.R 55 = binSyms D s := by simp [M,lastCropSeedPairs,copyWordHeadersR,hblank 55 (by decide),hs]
  have h56 : M.R 56 = binSyms D width := by simp [M,lastCropSeedPairs,copyWordHeadersR,hblank 56 (by decide),hw]
  have h58 : (M.R 58).length = D := by simp [M,lastCropSeedPairs,copyWordHeadersR,hblank 58 (by decide),hruler]
  have hsmallPrivate (i : Fin 11) : masters i ∉ [(55 : Fin 117),56,58] := by
    intro hm
    have hb : ∀ k ∈ [(55 : Fin 117),56,58], k.val < 63 := by decide +kernel
    exact hmasterOff i _ (hb _ hm) rfl
  have hconverterReg : [masters 3,58,57,19,20,21,22,23,25].Nodup := by
    refine List.nodup_cons.mpr ⟨?_,by decide⟩
    intro hm
    have hb : ∀ k ∈ [(58 : Fin 117),57,19,20,21,22,23,25], k.val < 63 := by decide +kernel
    exact hmasterOff 3 _ (hb _ hm) rfl
  have hwfit : w < 2^D := (Nat.le_mul_of_pos_left w (show 1 ≤ s by omega)).trans_lt hfit
  obtain ⟨v₂,n₂,hu₂,hn₂,hex₂⟩ := paddedHeaderList_exec (body := body) 58 19 20 21 22 23 25
    D (fun _ => w) [(masters 3,57)] (by intro pair hp; simp only [List.mem_singleton] at hp; subst pair; exact Nat.size_le.mpr hwfit)
    (by intro pair hp; simp only [List.mem_singleton] at hp; subst pair; exact hconverterReg)
    (by simp) (by intro pair hp other ho; simp only [List.mem_singleton] at hp ho; subst pair; subst other; exact (hmasterOff 3 57 (by decide)).symm)
    (by intro pair hp; simp only [List.mem_singleton] at hp; subst pair; dsimp only; decide) v₁ M h58
    (by intro pair hp; simp only [List.mem_singleton] at hp; subst pair; rw [hcopyOff _ (hsmallPrivate 3)]; exact hnarrow)
    (by intro pair hp; simp only [List.mem_singleton] at hp; subst pair; rw [hcopyOff 57 (by decide)]; exact hblank 57 (by decide))
    (by intro i hi
        have hd : List.Disjoint [(19 : Fin 117),20,21,22,23,25] [55,56,58] := by simp [List.disjoint_left]
        rw [hcopyOff i (fun hm => List.disjoint_left.mp hd hi hm)]
        have hb : ∀ k ∈ [(19 : Fin 117),20,21,22,23,25], k.val < 63 := by decide +kernel
        exact hblank i (hb i hi))
  let B : Stacks 117 A := {M with R := Function.update M.R 57 (binSyms D w)}
  have he₂ : ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v₁ M)+depth+2*(21*w+12*D+29)) depth
      (paddedHeaderList 58 19 20 21 22 23 25 [(masters 3,57)]) (mk v₁ M) n₂ (mk v₂ B) := by
    have he : Exec body (paddedHeaderList 58 19 20 21 22 23 25 [(masters 3,57)]) (mk v₁ M) n₂ (mk v₂ B) := by
      simpa only [paddedHeaderListR,B] using hex₂
    have hn : n₂ ≤ 21*w+12*D+29 := by
      have ht := hn₂
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at ht
      omega
    exact mn_native_exec_within he 2 (paddedHeaderList_native ..) depth _ (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hn) _)
  have hn₂' : n₂ ≤ 21*w+12*D+29 := by
      have ht := hn₂
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at ht
      omega
  have hseedFrame (i : Fin 117) (hi : i ∉ [(55 : Fin 117),56,57,58]) : B.R i = S.R i := by
    have hne : i ≠ 57 := by intro he; subst i; exact hi (by simp)
    rw [show B.R i = M.R i from Function.update_of_ne hne _ _]
    exact hcopyOff i (by intro hm; apply hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hm; rcases hm with rfl | rfl | rfl <;> simp)
  have hseed55 : B.R 55 = binSyms D s := by simpa only [B,Function.update_of_ne (by decide : (55 : Fin 117) ≠ 57)] using h55
  have hseed56 : B.R 56 = binSyms D width := by simpa only [B,Function.update_of_ne (by decide : (56 : Fin 117) ≠ 57)] using h56
  have hseed57 : B.R 57 = binSyms D w := by simp only [B,Function.update_self]
  have hseed58 : (B.R 58).length = D := by simpa only [B,Function.update_of_ne (by decide : (58 : Fin 117) ≠ 57)] using h58
  have hbankOff (k : Fin 117) (hk : 54 ≤ k.val) (i : TblR 9) : boundaryCounterRegister i ≠ k := by
    intro he
    have hb := (boundaryCounterRegister_bounds i).2
    have hv := congrArg Fin.val he
    omega
  let value : Fin 117 → ℕ := fun i => if i = 55 then s else if i = 56 then width else w
  have hvalues : ∀ j, value (boundarySeedGlobals j) = ![s,width,w] j := by intro j; fin_cases j <;> simp [value,boundarySeedGlobals]
  have hsfit : s < 2^D := (Nat.le_mul_of_pos_right s hword).trans_lt hfit
  have hwidthfit : width < 2^D := (show width ≤ s by omega).trans_lt hsfit
  have hprivateOff (i : Fin 11) : masters i ∉ [(55 : Fin 117),56,57,58] := by
    intro hm
    have hb : ∀ k ∈ [(55 : Fin 117),56,57,58], k.val < 63 := by decide +kernel
    exact hmasterOff i _ (hb _ hm) rfl
  have hcountB : B.R (masters 10) = [] := (hseedFrame _ (hprivateOff 10)).trans hcount
  obtain ⟨v₃,n₃,hu₃,hn₃,hex₃⟩ := preparedClippedCropCount_exec_within body boundaryCounterRegister
    boundaryCounterRegister_injective boundarySeedGlobals 59 58 (masters 10)
    (hbankOff _ (by have := hprivate 10; omega)) (hbankOff 58 (by decide)) (hbankOff 59 (by decide))
    (by intro j; apply hbankOff; fin_cases j <;> decide)
    (by intro j; fin_cases j <;> decide) D s width w hwidth hword hroom hfit value hvalues
    (by intro j; fin_cases j <;> simp [value,boundarySeedGlobals] <;> assumption)
    v₂ B hseed58 (by rw [hseedFrame 59 (by decide)]; exact hblank 59 (by decide))
    (by intro j; fin_cases j
        · simpa [value,boundarySeedGlobals] using hseed55
        · simpa [value,boundarySeedGlobals] using hseed56
        · simpa [value,boundarySeedGlobals] using hseed57)
    (by intro i
        have hb := boundaryCounterRegister_bounds i
        rw [hseedFrame _ (by intro hm; simp only [List.mem_cons,List.not_mem_nil,or_false] at hm; rcases hm with h | h | h | h <;> have hv := congrArg Fin.val h <;> simp at hv <;> omega)]
        exact hblank _ (lt_trans hb.2 (by decide))) depth
  have he₃ := hex₃
  simp only [hcountB,List.append_nil] at he₃
  let countWord := List.replicate (coreLength s width (boundaryCropIndex s width 2)*w) (tick : Fin (A+4))
  obtain ⟨v',hu₄,he₄⟩ := retireHeaderFrame_pair_exec body [55,56,57,58] (by decide) S B rfl rfl rfl hseedFrame
    (by
      intro i hi
      have hb : ∀ k ∈ [(55 : Fin 117),56,57,58], k.val < 63 := by decide +kernel
      exact hblank i (hb i hi))
    (masters 10) (masters 10) (hprivateOff 10) (hprivateOff 10) countWord countWord v₃ depth
  have hclearCost : 2*(([(55 : Fin 117),56,57,58]).map (fun i => (B.R i).length)).sum+2*([(55 : Fin 117),56,57,58]).length+1 = 8*D+9 := by
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,
      hseed55,hseed56,hseed57,hseed58,length_binSyms]
    omega
  have he₄' : ExecWithin body (fun z state => mnSize state+z ≤
      mnSize (mk v₃ {B with R := Function.update B.R (masters 10) countWord})+depth+0) depth
      (clearWords [55,56,57,58]) (mk v₃ {B with R := Function.update B.R (masters 10) countWord}) (8*D+9)
      (mk v' {S with R := Function.update S.R (masters 10) countWord}) := by
    simpa only [hclearCost,Function.update_idem,Nat.add_zero] using he₄
  have hex := mn_seq_within_add (mn_seq_within_add (mn_seq_within_add he₁ he₂) he₃) he₄'
  refine ⟨v',(18*D+19)+n₂+n₃+(8*D+9),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,?_⟩
  · unfold boundaryLastCropMasterCost
    omega
  · exact hex.mono (by
      intro z state hz
      simp only [boundaryLastCropMasterCost,Nat.mul_add,Nat.add_zero] at hz ⊢
      omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
