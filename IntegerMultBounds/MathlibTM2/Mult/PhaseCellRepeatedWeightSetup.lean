module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedWeightSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicateWeightPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchWeightPage

/-! Generate one exact ambient weight page and copy it across equal-origin
replicas. Numerical initialization/evaluation is paid once for the whole batch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem batchWeightPage_const (A w q P s t u B L lo : ℕ) :
    batchWeightPage A w q P s t u B L (fun _ => lo) =
      (List.replicate B (outputWeightRow A w q P s t u L lo)).flatten++
        (List.replicate B (inputWeightRow A w q P s t u L lo)).flatten := by
  simp [batchWeightPage,List.flatMap_def,List.map_const']

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def repeatedWeightSetup : Pr P₀ 117 Q A U := .seq packedWeightSetup replicateWeightPage

def repeatedWeightSetupCost (P s t u q L lo w B : ℕ) : ℕ :=
  packedWeightSetupCost P s t u q L lo w+replicateWeightPageCost B L w

theorem repeatedWeightSetup_exec (P s t u q L lo w B : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP' : (S.R 114).length = P) (hs' : (S.R 97).length = s) (ht' : (S.R 98).length = t)
    (hu' : (S.R 99).length = u) (hq : (S.R 112).length = q)
    (hL' : (S.R 102).length = L) (hcount : (S.R 103).length = L)
    (hlo' : (S.R 111).length = lo) (hw : (S.R 94).length = w) (hB : (S.R 116).length = B)
    (hblank : ∀ r, S.R (coefficientReg r) = [])
    (hfresh : ∀ k ∈ [(64 : Fin 117),65,96,104,105,106,107,108,115], S.R k = [])
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hlo : lo < s) (hL : L ≤ s) :
    ∃ v' n, v'.user = v.user ∧ n ≤ repeatedWeightSetupCost P s t u q L lo w B ∧
      Exec body repeatedWeightSetup (mk v S) n
        (mk v' { S with R := (Function.update S.R 110
          (batchWeightPage A w q P s t u B L (fun _ => lo)++S.R 110)) }) := by
  have hlow (k : Fin 117) (hk : k.val < 63) : S.R k = [] := by
    obtain ⟨r,rfl⟩ := coefficientReg_covers k hk
    exact hblank r
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := packedWeightSetup_exec (body := body)
    P s t u q L lo w v S hP' hs' ht' hu' hq hL' hcount hlo' hw hblank (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp)) hP hs hst hu hlo hL
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 110 (weightPage A w q P s t u lo L++S.R 110) }
  have he₁' : Exec body packedWeightSetup (mk v S) n₁ (mk v₁ S₁) := by
    convert he₁ using 1
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k.val < 63
    · have h110 : k ≠ 110 := by intro he; subst k; contradiction
      simp [S₁,hk,h110,hlow k hk]
    simp [S₁,hk,Function.update_apply]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := replicateWeightPage_exec (body := body) B L w
    (outputWeightRow A w q P s t u L lo) (inputWeightRow A w q P s t u L lo) (S.R 110) v₁ S₁
    (by simpa [S₁] using hB) (by simpa [S₁] using hcount) (by simpa [S₁] using hw)
    (by simp) (by simp) (by simp [S₁,weightPage,outputWeightRow,inputWeightRow,List.append_assoc]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [S₁] using hfresh _ (by simp))
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,by dsimp only [repeatedWeightSetupCost]; omega,
    (Exec.seq he₁' he₂).cast rfl ?_⟩
  simp only [S₁,batchWeightPage_const,Function.update_idem,List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
