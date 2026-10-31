module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaWeightCache
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaSolverDimensions
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchInputBank

/-! Prepare the ordinary cached solver bank from one numerical weight key and
replica-major RHS rows. Dimension conversion is executed, not assumed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 121 Q A U}

def replicaInteriorCacheInputBank (A Pbits stage q l s t u band N B L w : ℕ) (lo : ℕ → ℕ)
    (rhs borrowed output : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A :=
  let base := batchInputBank Pbits stage q l s t u band L (N*B) (fun n => lo (n%B)) rhs borrowed output inp out
  {base with R := (Function.update (Function.update (Function.update (Function.update
    (Function.update base.R 103 (List.replicate (B*L) tick)) 116 (List.replicate N tick))
      115 (List.replicate B tick)) 94 (List.replicate w tick))
      110 (batchWeightPage A w q Pbits s t u B L lo++(rhs++borrowed)))}

def prepareReplicaInteriorCache : Pr P 121 Q A U :=
  .seq replicaWeightCache prepareReplicaSolverDimensions

def prepareReplicaInteriorCacheCost (N B L w : ℕ) : ℕ :=
  replicaWeightCacheCost N B L w+prepareReplicaSolverDimensionsCost N B L w

private theorem cacheBank_finish (A Pbits stage q l s t u band N B L w : ℕ) (lo : ℕ → ℕ)
    (rhs borrowed output : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := replicaInteriorCacheInputBank A Pbits stage q l s t u band N B L w lo rhs borrowed output inp out
    {S with R := (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update S.R 110 (rhs++borrowed)) 103 (List.replicate L tick))
        116 (List.replicate (N*B) tick)) 64 []) 115 []) 94 [])} =
    batchInputBank Pbits stage q l s t u band L (N*B) (fun n => lo (n%B)) rhs borrowed output inp out := by
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk : k ∈ ([(64 : Fin 117),94,103,110,115,116] : List (Fin 117))
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [replicaInteriorCacheInputBank,batchInputBank]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
    rcases hk with ⟨h64,h94,h103,h110,h115,h116⟩
    simp [replicaInteriorCacheInputBank,h64,h94,h103,h110,h115,h116]

theorem prepareReplicaInteriorCache_exec (Pbits stage q l s t u band N B L w : ℕ)
    (hB : 0 < B) (lo : ℕ → ℕ) (rhs borrowed output : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) (v : HS 121 Q A U) (S : Stacks 121 A)
    (hbank : embStk weightCacheCoreReg S =
      replicaInteriorCacheInputBank A Pbits stage q l s t u band N B L w lo rhs borrowed output inp out)
    (hfresh : ∀ k ∈ [(118 : Fin 121),119,120], S.R k = []) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ prepareReplicaInteriorCacheCost N B L w ∧
      Exec body prepareReplicaInteriorCache (mk v S) n (mk v' F) ∧
      embStk weightCacheCoreReg F = batchInputBank Pbits stage q l s t u band L (N*B)
        (fun n => lo (n%B)) rhs borrowed output inp out ∧
      F.R 117 = batchWeightPage A w q Pbits s t u (N*B) L (fun n => lo (n%B))++S.R 117 ∧
      F.R 118 = List.replicate (2*((N*B)*(L*w))) tick ∧ F.R 119 = [] ∧ F.R 120 = [] := by
  have hread (k : Fin 117) : S.R (weightCacheCoreReg k) =
      (replicaInteriorCacheInputBank A Pbits stage q l s t u band N B L w lo rhs borrowed output inp out).R k :=
    congrArg (fun M : Stacks 117 A => M.R k) hbank
  have hN : (S.R 116).length = N := by simpa [weightCacheCoreReg,replicaInteriorCacheInputBank] using congrArg List.length (hread 116)
  have hrows : (S.R 103).length = B*L := by simpa [weightCacheCoreReg,replicaInteriorCacheInputBank] using congrArg List.length (hread 103)
  have hw : (S.R 94).length = w := by simpa [weightCacheCoreReg,replicaInteriorCacheInputBank] using congrArg List.length (hread 94)
  have hs : S.R 110 = batchWeightPage A w q Pbits s t u B L lo++(rhs++borrowed) := by
    simpa [weightCacheCoreReg,replicaInteriorCacheInputBank] using hread 110
  have hclean (k : Fin 117) (hk : k ∈ [(64 : Fin 117),65,104,105,106,107,108]) : S.R (weightCacheCoreReg k) = [] := by
    rw [hread]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [replicaInteriorCacheInputBank,batchInputBank]
  have hlow (k : Fin 121) (hk : k ∈ [(64 : Fin 121),65,104,105,106,107,108]) : S.R k = [] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hclean 64 (by simp)
    · exact hclean 65 (by simp)
    · exact hclean 104 (by simp)
    · exact hclean 105 (by simp)
    · exact hclean 106 (by simp)
    · exact hclean 107 (by simp)
    · exact hclean 108 (by simp)
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,_⟩ := replicaWeightCache_exec (body := body)
    w q Pbits s t u N B L hB lo (rhs++borrowed) v S hN hrows hw hs (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hlow 64 (by simp)
      · exact hlow 65 (by simp)
      · exact hlow 104 (by simp)
      · exact hlow 105 (by simp)
      · exact hlow 106 (by simp)
      · exact hlow 107 (by simp)
      · exact hlow 108 (by simp)
      · exact hfresh 118 (by simp)
      · exact hfresh 119 (by simp)
      · exact hfresh 120 (by simp))
  let C : Stacks 121 A := {S with R := (Function.update (Function.update (Function.update S.R 110 (rhs++borrowed))
    117 (batchWeightPage A w q Pbits s t u (N*B) L (fun n => lo (n%B))++S.R 117))
    118 (List.replicate (2*((N*B)*(L*w))) tick))}
  have hBc : (C.R 115).length = B := by
    have hb := congrArg List.length (hread 115)
    simpa [C,weightCacheCoreReg,replicaInteriorCacheInputBank] using hb
  have hLc : (C.R 102).length = L := by
    have hl := congrArg List.length (hread 102)
    simpa [C,weightCacheCoreReg,replicaInteriorCacheInputBank,batchInputBank] using hl
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := prepareReplicaSolverDimensions_exec (body := body)
    N B L w v₁ C (by simpa [C] using hN) hBc hLc (by simpa [C] using hrows) (by simpa [C] using hw) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> simpa [C] using hlow _ (by simp))
  let F : Stacks 121 A := {C with R := (Function.update (Function.update (Function.update
    (Function.update (Function.update C.R 103 (List.replicate L tick))
      116 (List.replicate (N*B) tick)) 64 []) 115 []) 94 [])}
  refine ⟨v₂,F,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,?_,?_,?_,?_,?_⟩
  · have hp := cacheBank_finish A Pbits stage q l s t u band N B L w lo rhs borrowed output inp out
    rw [← hbank] at hp
    have hproj : embStk weightCacheCoreReg F =
        {embStk weightCacheCoreReg S with R := (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update (embStk weightCacheCoreReg S).R
            110 (rhs++borrowed)) 103 (List.replicate L tick)) 116 (List.replicate (N*B) tick))
              64 []) 115 []) 94 [])} := by
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      have h117 : k.val ≠ 117 := by omega
      have h118 : k.val ≠ 118 := by omega
      simp [F,C,embStk,weightCacheCoreReg,Function.update_apply,Fin.ext_iff,h117,h118]
    exact hproj.trans hp
  · simp [F,C]
  · simp [F,C]
  · simp [F,C,hfresh 119 (by simp)]
  · simp [F,C,hfresh 120 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
