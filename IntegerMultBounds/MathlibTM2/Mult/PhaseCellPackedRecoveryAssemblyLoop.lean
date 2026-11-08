module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedPackedPublicationMerge
public import IntegerMultBounds.MathlibTM2.Host.ConsumeScan

/-! Assemble an arbitrary list of paired interior/boundary fields with one
retained mask and one row's scratch reserve. Numerical acceptance is separate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 12 Q A U}

def replicaRecoveryAssemblyLoop : Pr P 12 Q A U :=
  scanP 10 11 (retainedPackedPublicationMerge 0 1 2 3 4 5 6 7 8 9)

theorem packedRecoveryAssemblyLoop_exec (t band a N w : ℕ) (hst : s < t) (hfit : a+N ≤ s)
    (rows : List ((ZMod s → GaussianInt) × (ZMod s → GaussianInt)))
    (hA : 4 ≤ A) (tailX tailY : List (Fin (A+4))) (v : HS 12 Q A U) (S : Stacks 12 A)
    (hmaster : S.R 0 = couplingSourceIntervalMaskSymbols true A s t band a (a+N) a N)
    (hwidth : (S.R 2).length = w)
    (hX : S.R 4 = rows.flatMap (fun row => cstream A w (packedInterval a N row.1))++tailX)
    (hY : S.R 5 = rows.flatMap (fun row => cstream A w (packedInterval a N row.2))++tailY)
    (hfresh : ∀ k ∈ ([1,3,6,8,9,11] : List (Fin 12)), S.R k = [])
    (hcount : (S.R 10).length = rows.length) (depth : ℕ) :
    let outputs := rows.map (fun row => cstream A w
      (packedInterval a N (publicationField t band a (a+N) row.1 row.2)))
    ∃ v' n, v'.user = v.user ∧
      n ≤ rows.length*(retainedPackedPublicationMergeCost N w+5)+4 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*retainedPackedPublicationMergeCost N w) depth replicaRecoveryAssemblyLoop (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 5 tailY)
          4 tailX) 7 (outputs.reverse.flatten++S.R 7))}) := by
  dsimp only
  let enc := fun D : ZMod s → GaussianInt => cstream A w (packedInterval a N D)
  let output := fun row : (ZMod s → GaussianInt) × (ZMod s → GaussianInt) =>
    enc (publicationField t band a (a+N) row.1 row.2)
  let J := fun F : Stacks 12 A => ∀ k ∈ ([0,1,2,3,6,8,9] : List (Fin 12)), F.R k = S.R k
  suffices hscan : ∃ v' n outputs, v'.user = v.user ∧
      n ≤ rows.length*(retainedPackedPublicationMergeCost N w+5)+4 ∧
      List.Forall₂ (fun row words => words = output row) rows outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*retainedPackedPublicationMergeCost N w) depth replicaRecoveryAssemblyLoop (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 5 tailY)
          4 tailX) 7 (outputs.reverse.flatten++S.R 7))}) by
    obtain ⟨v',n,outputs,hu,hn,hcert,he⟩ := hscan
    have map_eq : ∀ xs ys, List.Forall₂ (fun row words => words = output row) xs ys → ys = xs.map output := by
      intro xs ys h
      induction h with
      | nil => rfl
      | cons hrow _ ih => exact congrArg₂ List.cons hrow ih
    rw [map_eq _ _ hcert] at he
    exact ⟨v',n,hu,hn,he⟩
  apply consumeScan_exec (body := body)
    (retainedPackedPublicationMerge 0 1 2 3 4 5 6 7 8 9) 10 11 5 4 7 (by decide)
    (fun row => enc row.2) (fun row => enc row.1) rows tailY tailX
    (retainedPackedPublicationMergeCost N w) (2*retainedPackedPublicationMergeCost N w) depth
    (fun row words => words = output row) J ?_ ?_ ?_ v S (fun _ _ => rfl) hY hX hcount (hfresh 11 (by decide))
  · intro F R hR hJ k hk
    have hk10 : k ≠ 10 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hk11 : k ≠ 11 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hR k hk10 hk11).trans (hJ k hk)
  · intro F otail rest words hJ k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hJ _ (by decide)
  · intro row hr vi F otail rest hJ hboundary hinterior
    obtain ⟨vf,m,huf,hm,hem⟩ := retainedPackedPublicationMerge_exec (body := body)
      0 1 2 3 4 5 6 7 8 9 (by decide) hA hst hfit row.1 row.2 rest otail vi F
      ((hJ 0 (by decide)).trans hmaster) (by rw [hJ 2 (by decide)]; exact hwidth) hinterior hboundary
      ((hJ 1 (by decide)).trans (hfresh 1 (by decide)))
      ((hJ 3 (by decide)).trans (hfresh 3 (by decide)))
      ((hJ 6 (by decide)).trans (hfresh 6 (by decide)))
      ((hJ 8 (by decide)).trans (hfresh 8 (by decide)))
      ((hJ 9 (by decide)).trans (hfresh 9 (by decide)))
    have hew := mn_native_exec_within hem 2
      (retainedPackedPublicationMerge_native 0 1 2 3 4 5 6 7 8 9) depth _
      (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hm) _)
    refine ⟨vf,m,output row,huf,hm,?_,rfl,?_⟩
    · simp only [output,enc,length_cstream,packedInterval_length _ hfit,le_refl]
    · apply hew.cast rfl
      apply congrArg (mk vf)
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases hk : k = 4 <;> simp [Function.update_apply,hk,output,enc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
