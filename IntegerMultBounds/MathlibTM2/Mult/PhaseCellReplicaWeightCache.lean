module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaWeightPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCacheWeightPageDimensions
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedWeightCache
public import IntegerMultBounds.MathlibTM2.StackCallResources

/-! One generated multi-cell numerical page supplies the complete replica cache
and replay clock. Expansion evaluates no new numerical coefficients. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 121 Q A U}

def replicaWeightCache : Pr P 121 Q A U :=
  .seq (embProg weightCacheCoreReg Empty.elim (replicateWeightPage (P₀ := Empty)))
    cacheWeightPageFromDimensions

def replicaWeightCacheCost (N B L w : ℕ) : ℕ :=
  replicateWeightPageCost N (B*L) w+cacheWeightPageFromDimensionsCost N (B*L) w

private theorem linearCacheCost (N rows volume : ℕ) (hrows : rows ≤ volume) :
    N*(70*volume+77)+24*volume+9*rows+62+
      (26*(N*volume)+15*(N*rows)+9*N+27) ≤ 200*(N+1)*(volume+1) := by
  have hs := Nat.mul_le_mul_left N hrows
  nlinarith only [hrows,hs,Nat.zero_le (N*volume),Nat.zero_le volume,Nat.zero_le N]

/-- Both copying and replay-clock installation are linear in the expanded page. -/
theorem replicaWeightCacheCost_le (N B L w : ℕ) (hw : 1 ≤ w) :
    replicaWeightCacheCost N B L w ≤ 200*(N+1)*(B*L*w+1) := by
  have hrows : B*L ≤ B*L*w := Nat.le_mul_of_pos_right _ hw
  have hb := linearCacheCost N (B*L) (B*L*w) hrows
  simpa only [replicaWeightCacheCost,replicateWeightPageCost,cacheWeightPageFromDimensionsCost,
    Nat.mul_assoc] using hb

theorem replicaWeightCache_exec (w q Pbits s t u N B L : ℕ) (hB : 0 < B) (lo : ℕ → ℕ)
    (tail : List (Fin (A+4))) (v : HS 121 Q A U) (S : Stacks 121 A)
    (hN : (S.R 116).length = N) (hrows : (S.R 103).length = B*L) (hw : (S.R 94).length = w)
    (hsource : S.R 110 = batchWeightPage A w q Pbits s t u B L lo++tail)
    (hfresh : ∀ k ∈ [(64 : Fin 121),65,104,105,106,107,108,118,119,120], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ replicaWeightCacheCost N B L w ∧
      Exec body replicaWeightCache (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 110 tail)
          117 (batchWeightPage A w q Pbits s t u (N*B) L (fun n => lo (n%B))++S.R 117))
          118 (List.replicate (2*((N*B)*(L*w))) tick))}) ∧
      ∀ C, mnProgPush (replicaWeightCache (P := P) (U := U) (Q := Q) (A := A)) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(C+1)*replicaWeightCacheCost N B L w)
          depth replicaWeightCache (mk v S) n
          (mk v' {S with R := (Function.update (Function.update (Function.update S.R 110 tail)
            117 (batchWeightPage A w q Pbits s t u (N*B) L (fun n => lo (n%B))++S.R 117))
            118 (List.replicate (2*((N*B)*(L*w))) tick))}) := by
  let page := batchWeightPage A w q Pbits s t u (N*B) L (fun n => lo (n%B))
  obtain ⟨vi,n₁,hui,hn₁,hei⟩ := replicaWeightPage_exec
    (body := fun p : Empty => nomatch p) w q Pbits s t u N B L hB lo tail
    (embDn weightCacheCoreReg v) (embStk weightCacheCoreReg S) hN hrows hw hsource (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hfresh _ (by simp [weightCacheCoreReg]))
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    weightCacheCoreReg_injective (fun p => nomatch p) hei v rfl S rfl
  let S₁ : Stacks 121 A := {S with R := Function.update S.R 110 (page++tail)}
  have he₁' : Exec body
      (embProg weightCacheCoreReg Empty.elim (replicateWeightPage (P₀ := Empty)))
      (mk v S) n₁ (mk v₁ S₁) := by
    refine he₁.cast rfl ?_
    apply congrArg (mk v₁)
    rw [embOvr_updR weightCacheCoreReg_injective,embOvr_stk]
    rfl
  have hlen : page.length = 2*(N*(B*L)*w) := by
    simp only [page,batchWeightPage_length]
    ring
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := cacheWeightPageFromDimensions_exec (body := body)
    N (B*L) w page tail hlen v₁ S₁
    (by simpa [S₁] using hN) (by simpa [S₁] using hrows) (by simpa [S₁] using hw)
    (by simp [S₁]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simpa [S₁] using hfresh _ (by simp))
  let F : Stacks 121 A := {S with R := (Function.update (Function.update (Function.update S.R 110 tail)
    117 (page++S.R 117)) 118 (List.replicate (2*((N*B)*(L*w))) tick))}
  have he : Exec body replicaWeightCache (mk v S) (n₁+n₂) (mk v₂ F) := by
    refine (Exec.seq he₁' he₂).cast rfl ?_
    apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h118 : k = 118 <;> by_cases h117 : k = 117 <;> by_cases h110 : k = 110 <;>
      simp [S₁,F,page,h118,h117,h110,Nat.mul_assoc]
  have hn : n₁+n₂ ≤ replicaWeightCacheCost N B L w := Nat.add_le_add hn₁ hn₂
  refine ⟨v₂,n₁+n₂,hu₂.trans (hu₁.trans hui),hn,he,?_⟩
  intro C hp hb depth
  exact mn_exec_within he hp hb depth _ (by
    have hs := Nat.mul_le_mul_left (C+1) hn
    omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
