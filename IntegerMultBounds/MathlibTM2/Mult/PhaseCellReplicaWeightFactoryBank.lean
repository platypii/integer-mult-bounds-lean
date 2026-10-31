module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateReplicaWeightPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaInteriorCache

/-! Ordinary headers and origin packets generate the exact replica cache input
bank. The initial RHS bank contains no precomputed numerical weight page. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {U : Type}

def replicaWeightFactoryInputBank (A Pbits stage q l s t u band N B L w : ℕ) (lo : ℕ → ℕ)
    (rhs borrowed output : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A :=
  let base := batchInputBank Pbits stage q l s t u band L (N*B) (fun n => lo (n%B)) rhs borrowed output inp out
  {base with R := (Function.update (Function.update (Function.update (Function.update
    (Function.update base.R 113 (List.replicate N tick)) 116 (List.replicate B tick))
    94 (List.replicate w tick)) 109
      ((List.range B).flatMap (fun i => binSyms (weightWorkspaceWidth Pbits q w t u) (lo i))++base.R 109))
    115 [])}

/-- Numerical page generation is shared across RHS replicas; only a unary header grows. -/
theorem generateReplicaWeightPageCost_replicas (N P s t u q L w B : ℕ) :
    generateReplicaWeightPageCost N P s t u q L w B =
      generateReplicaWeightPageCost 0 P s t u q L w B+2*N := by
  unfold generateReplicaWeightPageCost prepareReplicaFactoryDimensionsCost
  ring

private theorem factory_finish (Pbits stage q l s t u band N B L w : ℕ) (lo : ℕ → ℕ)
    (rhs borrowed output : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := replicaWeightFactoryInputBank A Pbits stage q l s t u band N B L w lo rhs borrowed output inp out
    let base := batchInputBank Pbits stage q l s t u band L (N*B) (fun n => lo (n%B)) rhs borrowed output inp out
    replicaFactoryDimensionsBank {S with R := (Function.update (Function.update S.R 109 (base.R 109))
      110 (batchWeightPage A w q Pbits s t u B L lo++S.R 110))} N B L =
      replicaInteriorCacheInputBank A Pbits stage q l s t u band N B L w lo rhs borrowed output inp out := by
  dsimp only
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases h103 : k = 103 <;> by_cases h113 : k = 113 <;> by_cases h115 : k = 115 <;>
      by_cases h116 : k = 116 <;> by_cases h109 : k = 109 <;> by_cases h110 : k = 110 <;>
      simp [replicaFactoryDimensionsBank,replicaWeightFactoryInputBank,replicaInteriorCacheInputBank,
        batchInputBank,Function.update_apply,h103,h113,h115,h116,h109,h110,Fin.ext_iff]

theorem replicaWeightFactoryBank_exec_within (Pbits stage q l s t u band N B L w : ℕ)
    (lo : ℕ → ℕ) (hP : 13 ≤ Pbits) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hlo : ∀ i < B, lo i < s) (hL : L ≤ s)
    (v : HS 117 Q A U) (rhs borrowed output : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) (depth : ℕ) :
    let S := replicaWeightFactoryInputBank A Pbits stage q l s t u band N B L w lo rhs borrowed output inp out
    ∃ v' m, v'.user = v.user ∧ m ≤ generateReplicaWeightPageCost N Pbits s t u q L w B ∧
      ExecWithin (fun p : Empty => nomatch p) (fun level z => mnSize z+level ≤ mnSize (mk v S)+depth+
        mnProgPush (generateReplicaWeightPage (P₀ := Empty) (Q := Q) (A := A) (U := U))*
          generateReplicaWeightPageCost N Pbits s t u q L w B)
        depth generateReplicaWeightPage (mk v S) m
        (mk v' (replicaInteriorCacheInputBank A Pbits stage q l s t u band N B L w lo rhs borrowed output inp out)) := by
  dsimp only
  let S := replicaWeightFactoryInputBank A Pbits stage q l s t u band N B L w lo rhs borrowed output inp out
  let base := batchInputBank Pbits stage q l s t u band L (N*B) (fun n => lo (n%B)) rhs borrowed output inp out
  have hlow (k : Fin 117) (hk : k.val < 63) : S.R k = [] := by
    have hn (n : ℕ) (h : 63 ≤ n) : k.val ≠ n := by omega
    simp [S,replicaWeightFactoryInputBank,batchInputBank,Fin.ext_iff,
      hn 93 (by decide),hn 94 (by decide),hn 97 (by decide),hn 98 (by decide),hn 99 (by decide),
      hn 100 (by decide),hn 101 (by decide),hn 102 (by decide),hn 103 (by decide),
      hn 109 (by decide),hn 110 (by decide),hn 112 (by decide),hn 113 (by decide),
      hn 114 (by decide),hn 115 (by decide),hn 116 (by decide)]
  obtain ⟨v',m,huser,hcost,he⟩ := generateReplicaWeightPage_exec_within (Q := Q)
    N Pbits s t u q L w B lo v S (base.R 109)
    (by simp [S,replicaWeightFactoryInputBank])
    (by simp [S,replicaWeightFactoryInputBank,batchInputBank])
    (by simp [S,replicaWeightFactoryInputBank,batchInputBank])
    (by simp [S,replicaWeightFactoryInputBank,batchInputBank])
    (by simp [S,replicaWeightFactoryInputBank,batchInputBank])
    (by simp [S,replicaWeightFactoryInputBank,batchInputBank])
    (by simp [S,replicaWeightFactoryInputBank,batchInputBank])
    (by simp [S,replicaWeightFactoryInputBank,batchInputBank])
    (by simp [S,replicaWeightFactoryInputBank])
    (by simp [S,replicaWeightFactoryInputBank])
    (by simp [S,base,replicaWeightFactoryInputBank])
    (fun r => hlow _ (by have hh := coefficientReg_range r; omega))
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [S,replicaWeightFactoryInputBank,batchInputBank])
    hP hs hst hu hlo hL depth
  rw [factory_finish] at he
  exact ⟨v',m,huser,hcost,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
