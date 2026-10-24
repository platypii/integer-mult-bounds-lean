module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorSharedFields
public import IntegerMultBounds.MathlibTM2.Routing.BinaryResizeBatchScope
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Generate one once, then install the six shared descriptor operands. The
canonical 101-register scalar scope extends by one constant and six outputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def descriptorSharedJobs : List (Fin 6) := [0,1,2,3,4,5]
def descriptorSharedWidthSlot : Fin 6 → Fin 108 := ![27,21,25,26,26,26]
def descriptorSharedValueSlot : Fin 6 → Fin 108 := ![26,2,32,101,32,101]
def descriptorSharedDestination (i : Fin 6) : Fin 108 := ⟨102 + i.val, by have := i.isLt; omega⟩
def descriptorSharedInputWidth (L W : ℕ) (i : Fin 6) : ℕ := if i.val ≤ 1 then L else W
def descriptorSharedInstallSlot (i : Fin 6) : Fin 9 → Fin 108 :=
  ![descriptorSharedWidthSlot i,descriptorSharedValueSlot i,45,descriptorSharedDestination i,
    39,40,41,42,43]

theorem descriptorSharedInstallSlot_injective (i : Fin 6) :
    Function.Injective (descriptorSharedInstallSlot i) := by
  fin_cases i <;> decide +kernel

def descriptorSharedInstallProgram (rg : Fin 108 → Fin T) : Pr P T Q A U :=
  .seq (bzero (rg 32) (rg 101) (rg 39))
    (.seq (countIter (rg 101) (rg 39) (rg 9))
      (binaryResizeBatchProgram (fun i => rg ∘ descriptorSharedInstallSlot i) descriptorSharedJobs))

def descriptorSharedGeneratedBank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 108 → Fin T) (W : ℕ) (p : Par) (w : LiveDescriptorWidths) :=
  binaryResizeBatchBank (Function.update R (rg 101) (binSyms W 1))
    (fun i => rg ∘ descriptorSharedInstallSlot i)
    (descriptorSharedWidth w) (descriptorSharedValue p w) descriptorSharedJobs

theorem descriptorSharedGeneratedBank_at (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 108 → Fin T) (hrg : Function.Injective rg) (W : ℕ)
    (p : Par) (w : LiveDescriptorWidths) (i : Fin 6) :
    descriptorSharedGeneratedBank R rg W p w (rg (descriptorSharedDestination i)) =
      binSyms (descriptorSharedWidth w i) (descriptorSharedValue p w i) := by
  have hd : (descriptorSharedJobs.map (fun i => (rg ∘ descriptorSharedInstallSlot i) 3)).Nodup := by
    simp [descriptorSharedJobs,descriptorSharedInstallSlot,descriptorSharedDestination,hrg.eq_iff]
  exact binaryResizeBatchBank_at _ _ _ _ _ hd i (by fin_cases i <;> simp [descriptorSharedJobs])

def descriptorSharedTargets (rg : Fin 108 → Fin T) : List (Fin T) :=
  rg 101 :: descriptorSharedJobs.map (fun i => rg (descriptorSharedDestination i))

theorem descriptorSharedGeneratedBank_keep (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 108 → Fin T) (W : ℕ) (p : Par) (w : LiveDescriptorWidths)
    (k : Fin T) (hk : k ∉ descriptorSharedTargets rg) :
    descriptorSharedGeneratedBank R rg W p w k = R k := by
  have hn : k ≠ rg 101 ∧ k ∉ descriptorSharedJobs.map (fun i => rg (descriptorSharedDestination i)) := by
    simpa only [descriptorSharedTargets,List.mem_cons,not_or] using hk
  unfold descriptorSharedGeneratedBank
  rw [binaryResizeBatchBank_keep]
  · exact Function.update_of_ne hn.1 _ _
  · exact hn.2

theorem descriptorSharedGeneratedBank_low (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 108 → Fin T) (hrg : Function.Injective rg) (W : ℕ)
    (p : Par) (w : LiveDescriptorWidths) (i : Fin 108) (hi : i.val < 101) :
    descriptorSharedGeneratedBank R rg W p w (rg i) = R (rg i) := by
  apply descriptorSharedGeneratedBank_keep
  intro hm
  rcases List.mem_cons.mp hm with he | hm
  · have hv := congrArg (fun x : Fin 108 => x.val) (hrg he)
    change i.val = 101 at hv
    omega
  · obtain ⟨j,_,he⟩ := List.mem_map.mp hm
    have hv := congrArg (fun x : Fin 108 => x.val) (hrg he)
    change 102 + j.val = i.val at hv
    omega

theorem descriptorSharedGeneratedBank_clean (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 108 → Fin T) (W : ℕ) (p : Par) (w : LiveDescriptorWidths)
    (hblank : ∀ k ∈ descriptorSharedTargets rg, R k = []) :
    metadataCleared (descriptorSharedGeneratedBank R rg W p w) (descriptorSharedTargets rg) = R := by
  funext k
  by_cases hk : k ∈ descriptorSharedTargets rg
  · rw [metadataCleared_at _ _ _ hk]
    exact (hblank k hk).symm
  · rw [metadataCleared_keep _ _ _ hk,descriptorSharedGeneratedBank_keep R rg W p w k hk]

theorem descriptorSharedGeneratedBank_cleanCost_le (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 108 → Fin T) (hrg : Function.Injective rg) (W : ℕ)
    (p : Par) (w : LiveDescriptorWidths) (B : ℕ) (hW : W ≤ B)
    (hwidth : ∀ i, descriptorSharedWidth w i ≤ B) :
    metadataCleanCost (descriptorSharedGeneratedBank R rg W p w) (descriptorSharedTargets rg) ≤
      7 * (2 * B + 2) + 1 := by
  have one : descriptorSharedGeneratedBank R rg W p w (rg 101) = binSyms W 1 := by
    unfold descriptorSharedGeneratedBank
    rw [binaryResizeBatchBank_keep]
    · exact Function.update_self _ _ _
    · simp [descriptorSharedJobs,descriptorSharedInstallSlot,descriptorSharedDestination,hrg.eq_iff]
  have hc := metadataCleanCost_le (descriptorSharedGeneratedBank R rg W p w)
    (descriptorSharedTargets rg) B (by
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · rw [one,length_binSyms]
        exact hW
      · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hk
        rw [descriptorSharedGeneratedBank_at R rg hrg,length_binSyms]
        exact hwidth i)
  have hl : (descriptorSharedTargets rg).length = 7 := by rfl
  simpa only [hl] using hc

theorem descriptorSharedInstallCost_le (L W B : ℕ) (w : LiveDescriptorWidths)
    (hwidth : ∀ i, descriptorSharedWidth w i ≤ B) :
    binaryResizeBatchCost (fun _ => L) (descriptorSharedInputWidth L W)
      (descriptorSharedWidth w) descriptorSharedJobs ≤
      6 * (2 * L * (4 * B + 11) + 12 * (L + W) + 26 * B + 42) + 1 := by
  have bound (jobs : List (Fin 6)) :
      binaryResizeBatchCost (fun _ => L) (descriptorSharedInputWidth L W)
        (descriptorSharedWidth w) jobs ≤
        jobs.length * (2 * L * (4 * B + 11) + 12 * (L + W) + 26 * B + 42) + 1 := by
    induction jobs with
    | nil => simp [binaryResizeBatchCost]
    | cons i jobs ih =>
        have hw := hwidth i
        have hl : descriptorSharedInputWidth L W i ≤ L + W := by
          unfold descriptorSharedInputWidth
          split <;> omega
        have hm := Nat.mul_le_mul_left (2 * L)
          (show 4 * descriptorSharedWidth w i + 11 ≤ 4 * B + 11 by omega)
        simp only [binaryResizeBatchCost,List.length_cons]
        nlinarith only [ih,hw,hl,hm]
  exact bound descriptorSharedJobs

theorem descriptorSharedInstall_exec (body : P → Pr P T Q A U)
    (rg : Fin 108 → Fin T) (hrg : Function.Injective rg) (L W : ℕ)
    (p : Par) (w : LiveDescriptorWidths)
    (hwidthFit : ∀ i, descriptorSharedWidth w i < 2 ^ L)
    (hvalueFit : ∀ i, descriptorSharedValue p w i < 2 ^ descriptorSharedInputWidth L W i)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : ∀ i, S.R (rg (descriptorSharedWidthSlot i)) = binSyms L (descriptorSharedWidth w i))
    (hvalue : ∀ i : Fin 6, i ≠ 3 → i ≠ 5 →
      S.R (rg (descriptorSharedValueSlot i)) =
        binSyms (descriptorSharedInputWidth L W i) (descriptorSharedValue p w i))
    (hzero : S.R (rg 32) = binSyms W 0)
    (hblank : ∀ i : Fin 108,
      i ∈ ([39,40,41,42,43,45,101,102,103,104,105,106,107] : List (Fin 108)) →
      S.R (rg i) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 8 * W + 9 + binaryResizeBatchCost (fun _ => L)
        (descriptorSharedInputWidth L W) (descriptorSharedWidth w) descriptorSharedJobs ∧
      Exec body (descriptorSharedInstallProgram rg) (mk v S) m
        (mk v' { S with R := descriptorSharedGeneratedBank S.R rg W p w }) := by
  obtain ⟨v₁,hu₁,he₁⟩ := bzero_exec (body := body) (wR := rg 32) (c := rg 101) (t := rg 39)
    (by simp [List.nodup_cons, hrg.eq_iff]) v S (hblank 39 (by simp))
  rw [hzero,length_binSyms,hblank 101 (by simp),List.append_nil] at he₁
  let C : Stacks T A := { S with R := Function.update S.R (rg 101) (binSyms W 0) }
  obtain ⟨v₂,hu₂,he₂⟩ := countIter_exec (body := body) (W := W) (j := 0)
    (c := rg 101) (tmp := rg 39) (hrg.ne (by decide)) (rg 9) v₁ C
    (by simp [C]) (by simp [C,hrg.eq_iff,hblank 39 (by simp)])
  let D : Stacks T A := { S with R := Function.update S.R (rg 101) (binSyms W 1) }
  have hd : ({ C with R := Function.update C.R (rg 101) (binSyms W (0+1)) } : Stacks T A) = D := by
    simp [C,D]
  rw [hd] at he₂
  have keep (i : Fin 108) (hi : i ≠ 101) : D.R (rg i) = S.R (rg i) := by simp [D,hrg.eq_iff,hi]
  have hdst : (descriptorSharedJobs.map (fun i => (rg ∘ descriptorSharedInstallSlot i) 3)).Nodup := by
    simp [descriptorSharedJobs,descriptorSharedInstallSlot,descriptorSharedDestination,hrg.eq_iff]
  have sep : ∀ i j, j ≠ 3 → ∀ k, descriptorSharedInstallSlot i j ≠ descriptorSharedInstallSlot k 3 := by
    decide +kernel
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := binaryResizeBatch_exec body
    (fun i => rg ∘ descriptorSharedInstallSlot i)
    (fun i => hrg.comp (descriptorSharedInstallSlot_injective i))
    (fun _ => L) (descriptorSharedInputWidth L W) (descriptorSharedWidth w)
    (descriptorSharedValue p w) hwidthFit hvalueFit descriptorSharedJobs hdst
    (fun i j hj k => hrg.ne (sep i j hj k)) v₂ D
    (by intro i; exact (keep _ (by fin_cases i <;> decide)).trans (hwidth i))
    (by
      intro i
      change D.R (rg (descriptorSharedValueSlot i)) = _
      by_cases h3 : i = 3
      · subst i
        simp [D,descriptorSharedValueSlot,descriptorSharedValue,descriptorSharedInputWidth]
      by_cases h5 : i = 5
      · subst i
        simp [D,descriptorSharedValueSlot,descriptorSharedValue,descriptorSharedInputWidth]
      exact (keep _ (by fin_cases i <;> simp_all [descriptorSharedValueSlot])).trans (hvalue i h3 h5))
    (by
      intro i _
      exact (keep _ (by fin_cases i <;> decide)).trans
        (hblank _ (by fin_cases i <;> decide)))
    (by
      intro i j h0 h1 h3
      exact (keep _ (by fin_cases j <;> simp_all [descriptorSharedInstallSlot])).trans
        (hblank _ (by fin_cases j <;> simp_all [descriptorSharedInstallSlot])))
  refine ⟨v₃,(4*W+4)+((4*W+5)+m₃),hu₃.trans (hu₂.trans hu₁),?_,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  omega

end
end IntegerMultBounds.MathlibTM2.Routing
