module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReusablePackedCellBatchPublish

/-! An empty generated class owns only its copied scalar headers. Release those
copies without touching the borrowed source, output or retained caller state. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def emptyPackedHaloHeaders : List (Fin 168) := [114,101,112,109,97,98,99,100,102,103]

def emptyPackedHaloGroup : Pr P 168 Q A U := clearWords emptyPackedHaloHeaders

theorem emptyPackedHaloGroup_exec (precision stage q l s t u band L : ℕ)
    (borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hbank : embStk packedCellCoreReg S = batchInputBank precision stage q l s t u band L 0
      (fun _ => 0) [] borrowed outTail inp out) :
    ∃ v' F, v'.user = v.user ∧
      Exec body emptyPackedHaloGroup (mk v S)
        (2*(precision+stage+q+l+s+t+u+band+2*L)+21) (mk v' F) ∧
      embStk packedCellCoreReg F = releasedCellBank [] borrowed outTail inp out ∧
      ∀ k : Fin 168, 117 ≤ k.val → F.L k = S.L k ∧ F.R k = S.R k := by
  have hR (k : Fin 117) : S.R (packedCellCoreReg k) =
      (batchInputBank precision stage q l s t u band L 0 (fun _ => 0) [] borrowed outTail inp out).R k :=
    congrArg (fun B : Stacks 117 A => B.R k) hbank
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) emptyPackedHaloHeaders (by decide) v S
  let F : Stacks 168 A := {S with R := fun k => if k ∈ emptyPackedHaloHeaders then [] else S.R k}
  have hcost : (emptyPackedHaloHeaders.map (fun k => (S.R k).length)).sum =
      precision+stage+q+l+s+t+u+band+2*L := by
    simp only [emptyPackedHaloHeaders,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    have h114 : S.R 114 = List.replicate precision tick := by
      simpa [packedCellCoreReg,batchInputBank] using hR 114
    have h101 : S.R 101 = List.replicate stage tick := by
      simpa [packedCellCoreReg,batchInputBank] using hR 101
    have h112 : S.R 112 = List.replicate q tick := by
      simpa [packedCellCoreReg,batchInputBank] using hR 112
    have h109 : S.R 109 = List.replicate l tick := by
      simpa [packedCellCoreReg,batchInputBank] using hR 109
    have h97 : S.R 97 = List.replicate s tick := by
      simpa [packedCellCoreReg,batchInputBank] using hR 97
    have h98 : S.R 98 = List.replicate t tick := by
      simpa [packedCellCoreReg,batchInputBank] using hR 98
    have h99 : S.R 99 = List.replicate u tick := by
      simpa [packedCellCoreReg,batchInputBank] using hR 99
    have h100 : S.R 100 = List.replicate band tick := by
      simpa [packedCellCoreReg,batchInputBank] using hR 100
    have h102 : S.R 102 = List.replicate L tick := by
      simpa [packedCellCoreReg,batchInputBank] using hR 102
    have h103 : S.R 103 = List.replicate L tick := by
      simpa [packedCellCoreReg,batchInputBank] using hR 103
    rw [h114,h101,h112,h109,h97,h98,h99,h100,h102,h103]
    simp
    omega
  refine ⟨v',F,hu,he.cast (by rw [hcost]; simp [emptyPackedHaloHeaders]) rfl,?_,?_⟩
  · have hi := congrArg (fun B : Stacks 117 A => B.inp) hbank
    have ho := congrArg (fun B : Stacks 117 A => B.out) hbank
    have hl := congrArg (fun B : Stacks 117 A => B.L) hbank
    refine Stacks.ext hi ho hl ?_
    funext k
    by_cases hk : k.val ∈ [114,101,112,109,97,98,99,100,102,103]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with h | h | h | h | h | h | h | h | h | h
      all_goals simp [F,embStk,packedCellCoreReg,emptyPackedHaloHeaders,releasedCellBank,Fin.ext_iff,h]
    · have hn (n : ℕ) (hn : n ∈ [114,101,112,109,97,98,99,100,102,103]) : k.val ≠ n := by
        intro he; apply hk; simpa [he] using hn
      have hoff : packedCellCoreReg k ∉ emptyPackedHaloHeaders := by
        simpa [emptyPackedHaloHeaders,packedCellCoreReg,Fin.ext_iff] using hk
      change (if packedCellCoreReg k ∈ emptyPackedHaloHeaders then [] else S.R (packedCellCoreReg k)) = _
      rw [ite_eq_right hoff,hR k]
      simp [batchInputBank,releasedCellBank,hn 114 (by decide),hn 101 (by decide),hn 112 (by decide),
        hn 109 (by decide),hn 97 (by decide),hn 98 (by decide),hn 99 (by decide),hn 100 (by decide),
        hn 102 (by decide),hn 103 (by decide)]
      split_ifs <;> simp_all
  · intro k hk
    have hn : k ∉ emptyPackedHaloHeaders := by
      simp only [emptyPackedHaloHeaders,List.mem_cons,List.not_mem_nil,or_false]
      omega
    exact ⟨rfl,by simp [F,hn]⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
