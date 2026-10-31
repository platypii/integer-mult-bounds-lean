module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputStage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightedInputCloseStock

/-! Normalized RHS words are computed, installed and accepted by the interior ABI
with one shared numerical reserve and linear native movement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
open ScalarPlacement
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

private theorem installInput_native :
    mnNativePushBound 3 (installInput (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [installInput,branchWords,halfCount,halfPairAct,takeFromWords,takePrefix,unaryProduct,
    transfer,transferAct,ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

def inputStageWorkspace (K q cExp e w M L : ℕ) : ℕ :=
  applyWeightsWorkspace K q (cExp+e+1) M L w+3*installInputCost M L w (cExp+e+1)

theorem inputStage_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q l w M L cExp e j : ℕ} (hw : q + (cExp + e + 1) + 4 ≤ w)
    (hq : cExp + e + 1 + j + 1 ≤ q) (X Z C : ℕ → List GaussianInt) (D : ℕ → List ℚ)
    (hlenC : ∀ n < M, (C n).length = L) (hlenD : ∀ n < M, (D n).length = L)
    (hC : ∀ n < M, ∀ x ∈ C n, ‖value q x‖ ≤ (2 : ℝ) ^ cExp)
    (hD : ∀ n < M, ∀ a ∈ D n, 1 / (2 : ℝ) ^ e ≤ (a : ℝ))
    (v : HS 117 Q A U) (tail tailX : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (K : ℕ) (hpush : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ K) (depth : ℕ) :
    let V := fun n => weightedInputNumerators q cExp e (C n) (D n)
    let factors := reciprocalWeightWords q ((List.range M).flatMap D)
    ∃ v' m, v'.user = v.user ∧ m ≤ inputStageCost q cExp e w M L ∧
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v (inputSourceBank q l w M L (cExp+e+1) X Z ((List.range M).flatMap C)
          factors tail tailX inp out))+depth+inputStageWorkspace K q cExp e w M L) depth (inputStage hQ)
        (mk v (inputSourceBank q l w M L (cExp + e + 1) X Z ((List.range M).flatMap C)
          factors tail tailX inp out)) m
        (mk v' (singleBranchInputWithXTail q l w M L X Z V tail tailX inp out)) := by
  dsimp only
  let V := fun n => weightedInputNumerators q cExp e (C n) (D n)
  let source := (List.range M).flatMap C
  let ds := (List.range M).flatMap D
  let factors := reciprocalWeightWords q ds
  let S := inputSourceBank q l w M L (cExp + e + 1) X Z source factors tail tailX inp out
  have hlength {α : Type} (F : ℕ → List α) (hF : ∀ n < M, (F n).length = L) :
      ((List.range M).flatMap F).length = M * L := by
    have h := length_flatten_const ((List.range M).map F) (by
      intro xs hx
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
      exact hF n (List.mem_range.mp hn))
    simpa only [List.flatMap_def, List.length_map, List.length_range] using h
  have hsource : source.length = M * L := hlength C hlenC
  have hds : ds.length = source.length := (hlength D hlenD).trans hsource.symm
  have hV : ∀ n < M, (V n).length = L := by
    intro n hn
    simpa only [V, weightedInputNumerators_length q cExp e (C n) (D n) ((hlenC n hn).trans (hlenD n hn).symm)] using hlenC n hn
  have hzero (k : Fin 117) (hk : k.val < 96) (hk93 : k.val ≠ 93) (hk94 : k.val ≠ 94) : S.R k = [] := by
    have hn (j : Fin 117) (hj : 96 ≤ j.val) : k ≠ j := by
      intro h; have he := congrArg (fun k : Fin 117 => k.val) h; omega
    have hnv (j : ℕ) (hj : 96 ≤ j) : k.val ≠ j := by omega
    have hn93 : k ≠ (93 : Fin 117) := fun h => hk93 (congrArg Fin.val h)
    simp [S, inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails,
      Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank,
      hn 96 (by decide), hn 111 (by decide), hn 116 (by decide), hn93,
      hk93, hk94, hnv 100 (by decide), hnv 101 (by decide), hnv 102 (by decide),
      hnv 103 (by decide), hnv 108 (by decide), hnv 110 (by decide), hnv 111 (by decide)]
  have hc : CClean mul S := by
    intro i
    refine ⟨rfl, ?_⟩
    have hi := i.isLt
    exact hzero (mul i) (by change i.val < 96; omega) (by change i.val ≠ 93; omega) (by change i.val ≠ 94; omega)
  have hfresh : ∀ r, S.R (cr r) = [] := by
    intro r
    have hr := cr_range r
    exact hzero (cr r) (by omega) hr.2.2.1 hr.2.2.2
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁, _, _⟩ := closedWeightedInput_exec_within (body := body)
    (q := q) (w := w) (cExp := cExp) (e := e) (M := M) (L := L) (j := j)
    hQ hA hw hq source ds hsource hds
    (by intro x hx; obtain ⟨n, hn, hx⟩ := List.mem_flatMap.mp hx; exact hC n (List.mem_range.mp hn) x hx)
    (by intro a ha; obtain ⟨n, hn, ha⟩ := List.mem_flatMap.mp ha; exact hD n (List.mem_range.mp hn) a ha)
    v S tail [] hc hfresh
    (by simp [S, inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, inputSourceBank])
    (by simp [S, inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, inputSourceBank]) (by simp [S, inputSourceBank, factors])
    K hpush depth
  have hflat : weightedInputNumerators q cExp e source ds = (List.range M).flatMap V := by
    exact weightedInputNumerators_flatMap q cExp e (List.range M) C D
      (by intro n hn; exact (hlenC n (List.mem_range.mp hn)).trans (hlenD n (List.mem_range.mp hn)).symm)
  have he₁' : ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+applyWeightsWorkspace K q (cExp+e+1) M L w) depth (closedWeights hQ) (mk v S) m₁
      (mk v₁ (inputInstallBank q l w M L (cExp + e + 1) X Z V factors tail tailX inp out)) := by
    rw [hflat] at he₁
    exact he₁.cast rfl (congrArg (mk v₁) (inputSourceBank_frame q l w M L (cExp + e + 1) X Z V source factors tail tailX inp out))
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := inputInstallBank_exec (body := body) q l w M L (cExp + e + 1) X Z V hV
    factors (by simp [factors, reciprocalWeightWords, ds, hlength D hlenD]) v₁ tail tailX inp out
  have ht₂ := mn_native_exec_within he₂ 3 installInput_native depth
    (mnSize (mk v₁ (inputInstallBank q l w M L (cExp+e+1) X Z V factors tail tailX inp out))+
      depth+3*installInputCost M L w (cExp+e+1))
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hm₂) _)
  have ht := mn_seq_within_add he₁' ht₂
  exact ⟨v₂,m₁+m₂,hu₂.trans hu₁,by unfold inputStageCost; omega,ht⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
