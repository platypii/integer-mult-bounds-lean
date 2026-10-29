module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingMetadata
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompleteCouplingIntervalMetadata

/-! Generate canonical interval geometry after factor setup, using retained
masters and the descriptor's binary origin and row count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def prepareRetainedCouplingIntervalMetadata : Pr P 168 Q A U :=
  .seq prepareRetainedCouplingMetadata completeCouplingIntervalMetadata

theorem retainedCouplingIntervalMetadataR_off {A : ℕ}
    (R : Fin 168 → List (Fin (A+4))) (V s t band a b origin N : ℕ) (k : Fin 168)
    (hk : k ∉ [(145 : Fin 168),146,147,148,149,151,154,156,164]) :
    completedCouplingIntervalR (retainedCouplingMetadataR R V s t band a b) V band origin N k = R k := by
  have h148 : k ≠ 148 := by intro he; subst k; simp at hk
  have h154 : k ≠ 154 := by intro he; subst k; simp at hk
  have h156 : k ≠ 156 := by intro he; subst k; simp at hk
  have h164 : k ≠ 164 := by intro he; subst k; simp at hk
  simp only [completedCouplingIntervalR,Function.update_of_ne h148,Function.update_of_ne h154,
    Function.update_of_ne h156,Function.update_of_ne h164]
  apply retainedCouplingMetadataR_off
  intro hm
  apply hk
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> simp

theorem prepareRetainedCouplingIntervalMetadata_exec {V s t band a b origin N : ℕ}
    (hfitV : origin+(N+2*band)+s < 2^V)
    (v : HS 168 Q A U) (S : Stacks 168 A) (hV : (S.R 163).length = V)
    (hs : (S.R 121).length = s) (ht : (S.R 122).length = t)
    (hband : (S.R 124).length = band) (ha : (S.R 141).length = a) (hb : (S.R 142).length = b)
    (h155 : S.R 155 = binSyms V origin) (h165 : S.R 165 = binSyms V N)
    (hblank : ∀ k ∈ [(0 : Fin 168),1,2,3,145,146,147,148,149,151,154,156,164], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (s+t+band+a+b)*(4*V+10)+56*V+77 ∧
      Exec body prepareRetainedCouplingIntervalMetadata (mk v S) n
        (mk v' {S with R := (completedCouplingIntervalR
          (retainedCouplingMetadataR S.R V s t band a b) V band origin N)}) ∧
      CouplingIntervalMetadata V s t band a b origin N
        {S with R := (completedCouplingIntervalR
          (retainedCouplingMetadataR S.R V s t band a b) V band origin N)} := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hencoded⟩ := prepareRetainedCouplingMetadata_exec (body := body)
    v S hV hs ht hband ha hb (by
      intro k hk
      apply hblank
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  let S₁ : Stacks 168 A := {S with R := retainedCouplingMetadataR S.R V s t band a b}
  have hoff (k : Fin 168) (hk : k ∉ [(145 : Fin 168),146,147,149,151]) : S₁.R k = S.R k :=
    retainedCouplingMetadataR_off S.R V s t band a b k hk
  obtain ⟨v₂,hu₂,he₂,hmeta⟩ := completeCouplingIntervalMetadata_exec (body := body) hfitV v₁ S₁
    (by rw [hoff 163 (by decide)]; exact hV)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hencoded origin N 145 (by decide)
      · exact hencoded origin N 146 (by decide)
      · exact hencoded origin N 147 (by decide)
      · exact hencoded origin N 149 (by decide)
      · exact hencoded origin N 151 (by decide)
      · simpa [hoff 155 (by decide),couplingIntervalValue] using h155
      · simpa [hoff 165 (by decide),couplingIntervalValue] using h165)
    (by
      intro k hk
      have hnot : k ∉ [(145 : Fin 168),146,147,149,151] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hoff k hnot]
      apply hblank
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  refine ⟨v₂,n₁+(36*V+36),hu₂.trans hu₁,?_,Exec.seq he₁ he₂,hmeta⟩
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
