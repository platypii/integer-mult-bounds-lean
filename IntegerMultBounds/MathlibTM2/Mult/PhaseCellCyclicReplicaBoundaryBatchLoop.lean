module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaBoundaryBatchStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! The paired residual archives are consumed by one structural counted loop.
The reversed output archive retains source order after one final reversal. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 180 Q A U}

theorem cyclicReplicaBoundaryBatchLoop_exec {s t : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (pairs : List ((ZMod s → GaussianInt) × (ZMod s → GaussianInt))) (w : ℕ)
    (leftTail rightTail : List (Fin (A+4))) (v : HS 180 Q A U) (S : Stacks 180 A)
    (ready : CyclicReplicaBoundaryReady (s := s) t band a n w S)
    (hleft : S.R 169 = pairs.flatMap (fun z => cstream A w (packedInterval a (min n (s-a)) z.1))++leftTail)
    (hright : S.R 172 = pairs.flatMap (fun z => cstream A w (packedInterval 0 (n-min n (s-a)) z.2))++rightTail)
    (hclock : (S.R 176).length = pairs.length) (harchive : S.R 178 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ pairs.length*(cyclicReplicaBoundaryBatchStepCost n (cyclicPrincipalBoundary s t band a n).card w+3)+2 ∧
      Exec body (countedLoop 176 cyclicReplicaBoundaryBatchStep) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          169 leftTail) 172 rightTail) 178
            (pairs.flatMap (fun z => cstream A w (cyclicReplicaBoundaryRow t band a n z.1 z.2))).reverse) 176 [])}) := by
  let left := fun z : (ZMod s → GaussianInt) × (ZMod s → GaussianInt) =>
    cstream A w (packedInterval a (min n (s-a)) z.1)
  let right := fun z : (ZMod s → GaussianInt) × (ZMod s → GaussianInt) =>
    cstream A w (packedInterval 0 (n-min n (s-a)) z.2)
  let row := fun z : (ZMod s → GaussianInt) × (ZMod s → GaussianInt) =>
    cstream A w (cyclicReplicaBoundaryRow t band a n z.1 z.2)
  let changed : List (Fin 180) := [169,172,176,178]
  let Inv := fun j (R : Stacks 180 A) =>
    R.inp = S.inp ∧ R.out = S.out ∧ R.L = S.L ∧
    (∀ k, k ∉ changed → R.R k = S.R k) ∧
    R.R 169 = (pairs.drop j).flatMap left++leftTail ∧
    R.R 172 = (pairs.drop j).flatMap right++rightTail ∧
    R.R 178 = ((pairs.take j).flatMap row).reverse
  have hstable : ∀ j R xs, Inv j R → Inv j {R with R := Function.update R.R 176 xs} := by
    intro j R xs ⟨hi,ho,hl,hf,hs,ht,ha⟩
    refine ⟨hi,ho,hl,?_,?_,?_,?_⟩
    · intro k hk
      have h176 : k ≠ 176 := by intro h; subst k; exact hk (by simp [changed])
      simpa only [Function.update_of_ne h176] using hf k hk
    · simpa using hs
    · simpa using ht
    · simpa using ha
  have hstep : ∀ j < pairs.length, ∀ (vi : HS 180 Q A U) R, Inv j R →
      ∃ vf R' m, vf.user = vi.user ∧
        m ≤ cyclicReplicaBoundaryBatchStepCost n (cyclicPrincipalBoundary s t band a n).card w ∧
        Exec body cyclicReplicaBoundaryBatchStep (mk vi R) m (mk vf R') ∧
        R'.R 176 = R.R 176 ∧ Inv (j+1) R' := by
    intro j hj vi R ⟨hi,ho,hl,hf,hs,ht,harchive⟩
    have readyR : CyclicReplicaBoundaryReady (s := s) t band a n w R := ready.of_rightFrame hf
    have hs' : R.R 169 = left pairs[j]++((pairs.drop (j+1)).flatMap left++leftTail) := by
      rw [List.drop_eq_getElem_cons hj] at hs
      simpa only [List.flatMap_cons,List.append_assoc] using hs
    have ht' : R.R 172 = right pairs[j]++((pairs.drop (j+1)).flatMap right++rightTail) := by
      rw [List.drop_eq_getElem_cons hj] at ht
      simpa only [List.flatMap_cons,List.append_assoc] using ht
    obtain ⟨vf,m,hu,hm,he⟩ := cyclicReplicaBoundaryBatchStep_exec (body := body)
      hst hA band a n ha hn pairs[j].1 pairs[j].2 w
      ((pairs.drop (j+1)).flatMap left++leftTail) ((pairs.drop (j+1)).flatMap right++rightTail)
      vi R readyR hs' ht'
    let R' : Stacks 180 A := {R with R := (Function.update (Function.update (Function.update R.R
      169 ((pairs.drop (j+1)).flatMap left++leftTail)) 172 ((pairs.drop (j+1)).flatMap right++rightTail))
        178 ((row pairs[j]).reverse++R.R 178))}
    refine ⟨vf,R',m,hu,hm,he,by simp [R'],hi,ho,hl,?_,?_,?_,?_⟩
    · intro k hk
      have h169 : k ≠ 169 := by intro h; subst k; exact hk (by simp [changed])
      have h172 : k ≠ 172 := by intro h; subst k; exact hk (by simp [changed])
      have h178 : k ≠ 178 := by intro h; subst k; exact hk (by simp [changed])
      simpa [R',h169,h172,h178] using hf k hk
    · simp [R']
    · simp [R']
    · change (row pairs[j]).reverse++R.R 178 = ((pairs.take (j+1)).flatMap row).reverse
      rw [harchive,List.take_succ_eq_append_getElem hj]
      simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.reverse_append]
  have hInv : Inv 0 S := by
    refine ⟨rfl,rfl,rfl,fun _ _ => rfl,?_,?_,?_⟩
    · simpa only [List.drop_zero] using hleft
    · simpa only [List.drop_zero] using hright
    · simpa only [List.take_zero,List.flatMap_nil,List.reverse_nil] using harchive
  obtain ⟨vf,F,m,hu,hm,he,hclockF,hi,ho,hl,hf,hs,ht,harchiveF⟩ :=
    countedLoop_exec (body := body) 176 cyclicReplicaBoundaryBatchStep pairs.length
      (cyclicReplicaBoundaryBatchStepCost n (cyclicPrincipalBoundary s t band a n).card w)
      Inv hstable hstep v S hclock hInv
  refine ⟨vf,m,hu,hm,he.cast rfl ?_⟩
  apply congrArg (mk vf)
  refine Stacks.ext hi ho hl ?_
  funext k
  by_cases h169 : k = 169
  · subst k; simpa using hs
  by_cases h172 : k = 172
  · subst k; simpa using ht
  by_cases h176 : k = 176
  · subst k; simpa using hclockF
  by_cases h178 : k = 178
  · subst k; simpa using harchiveF
  simpa [h169,h172,h176,h178] using hf k (by simp [changed,h169,h172,h176,h178])

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
