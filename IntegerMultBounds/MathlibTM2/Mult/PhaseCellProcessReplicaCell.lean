module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedRawRepeatedBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakeReplicaCell
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireGroupRHS
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClassFrame

/-! Execute a shared same-origin replica solve, retire its gathered RHS, and
restore the raw source and outer registers while retaining the solved output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def processReplicaCell (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq takeReplicaCell (.seq (retainedRawRepeatedBatch hR hQ) (clearWords [128,141]))

def processReplicaCellCost (p l B L s t u target rhsExp V lo : ℕ) : ℕ :=
  (6*lo+6*L+38*V+28)+retainedRawRepeatedBatchCost p l B L s t u target rhsExp lo+
    (2*(L+lo)+5)

theorem processReplicaCell_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l B L s t p u target rhsExp V : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hB : 0 < B) (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (lo : ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < B, ∀ k, ‖value (executionPrecision p l target rhsExp) (C n k)‖ ≤ (2 : ℝ)^rhsExp)
    (I : Finset (ZMod s)) (x : ℕ → ZMod s → ℝ)
    (hx : ∀ n < B, SchurDominance.Solves (realMatrix s t p u) I (x n)
      (fun k => (value (executionPrecision p l target rhsExp) (C n k)).re))
    (hfit : lo.val+L ≤ s)
    (hint : ∀ k < L, Interior s t (PhaseCellBand.width p u) (lo+(k : ZMod s)) ∧
      lo+(k : ZMod s) ∈ I)
    (hcell : ∀ k < L, cell s t (lo+(k : ZMod s)) = cell s t lo)
    (hmax : ∀ k ∈ I, cell s t k = cell s t lo → ∃ i < L, lo+(i : ZMod s) = k)
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed : List (Fin (A+4)))
    (hmasters : ∀ r ∈ groupHeaderCopies, (S.R r.1).length =
      groupHeaderValue (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 r.1)
    (hleft : ∀ k : Fin 144, k.val < 117 → S.L k = [])
    (hblank : ∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = [])
    (hsrc : S.R 110 = cstream A (executionWidth p l target rhsExp) (replicaAmbientWords B C)++borrowed)
    (h142 : (S.R 142).length = B) (h141 : S.R 141 = [])
    (hV : (S.R 125).length = V) (hloKey : lo.val < 2^V) (hLKey : L < 2^V)
    (queueTail : List (Fin (A+4)))
    (hqueue : S.R 126 = binSyms V lo.val++binSyms V L++queueTail)
    (h129 : S.R 129 = []) (h133 : S.R 133 = [])
    (h128 : S.R 128 = [])
    (h130 : (S.R 130).length = executionWidth p l target rhsExp)
    (hfresh : ∀ k ∈ [(131 : Fin 144),134,135,136,137], S.R k = []) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' S' n, v'.user = v.user ∧ n ≤ processReplicaCellCost p l B L s t u target rhsExp V lo.val ∧
      Exec (embTab groupReg body) (processReplicaCell hR hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = Function.update (Function.update S.R 126 queueTail) 93 (S'.R 93) ∧
      (∀ n : Fin B, ∀ i : Fin L, |(value q (decodeWord (((S'.R 93).drop ((n.val*L+i.val)*w)).take w))).re -
        x n (lo+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target) ∧
      (∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore lo L)
        (publishedBatchRead q w n.val L lo (S'.R 93)) (x n) (1/(2 : ℝ)^target)) ∧
      ∃ ys : List (Fin (A+4)), ys.length = B*L*w ∧ S'.R 93 = ys++S.R 93 := by
  dsimp only
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := takeReplicaCell_exec (body := embTab groupReg body)
    V lo.val L hloKey hLKey queueTail v S hV hqueue (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h128
      · exact h141
      all_goals exact hfresh _ (by simp))
  let S₁ : Stacks 144 A := {S with R := replicaCellR S.R queueTail lo.val L}
  have hmasters₁ : ∀ r ∈ groupHeaderCopies, (S₁.R r.1).length =
      groupHeaderValue (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) L r.1 := by
    intro r hr
    have hh := hmasters r hr
    simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simpa [S₁,replicaCellR,groupHeaderValue] using hh
  have hblank₁ : ∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → S₁.R k = [] := by
    intro k hk hk93 hk110
    have h126 : k ≠ 126 := by intro he; subst k; norm_num at hk
    have h128' : k ≠ 128 := by intro he; subst k; norm_num at hk
    have h141' : k ≠ 141 := by intro he; subst k; norm_num at hk
    simpa [S₁,replicaCellR,h126,h128',h141'] using hblank k hk hk93 hk110
  obtain ⟨v₂,S₂,n₂,hu₂,hn₂,he₂,hi,ho,hl,hframe,hpoint,herror,ys,hylen,hys⟩ :=
    retainedRawRepeatedBatch_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget
      hB hL hLs hpad lo C hC I x hx hfit hint hcell hmax v₁ S₁ borrowed hmasters₁ hleft hblank₁
      (by simpa [S₁,replicaCellR] using hsrc) (by simpa [S₁,replicaCellR] using h142)
      (by simp [S₁,replicaCellR]) (by simpa [S₁,replicaCellR] using h129)
      (by simpa [S₁,replicaCellR] using h133) (by simp [S₁,replicaCellR])
      (by simpa [S₁,replicaCellR] using h130) (by
        intro k hk
        have h126 : k ≠ 126 := by intro he; subst k; norm_num at hk
        have h128' : k ≠ 128 := by intro he; subst k; norm_num at hk
        have h141' : k ≠ 141 := by intro he; subst k; norm_num at hk
        simpa [S₁,replicaCellR,h126,h128',h141'] using hfresh k hk)
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := embTab groupReg body) [(128 : Fin 144),141]
    (by decide) v₂ S₂
  let S₃ : Stacks 144 A := {S₂ with R := (fun k => if k ∈ [(128 : Fin 144),141] then [] else S₂.R k)}
  have hsum : (([(128 : Fin 144),141]).map (fun k => (S₂.R k).length)).sum = L+lo.val := by
    have h128' : S₂.R 128 = List.replicate L tick := by
      simpa [S₁,replicaCellR] using congrArg (fun R => R 128) hframe
    have h141' : S₂.R 141 = List.replicate lo.val tick := by
      simpa [S₁,replicaCellR] using congrArg (fun R => R 141) hframe
    simp [h128',h141']
  have he₃' : Exec (embTab groupReg body) (clearWords [128,141]) (mk v₂ S₂)
      (2*(L+lo.val)+5) (mk v₃ S₃) := by
    simpa only [hsum,List.length_cons,List.length_nil] using he₃
  have h93 : S₃.R 93 = S₂.R 93 := by simp [S₃]
  refine ⟨v₃,S₃,n₁+(n₂+(2*(L+lo.val)+5)),hu₃.trans (hu₂.trans hu₁),?_,
    Exec.seq he₁ (Exec.seq he₂ he₃'),hi,ho,hl,?_,?_,?_,ys,hylen,?_⟩
  · dsimp only [processReplicaCellCost]; omega
  · funext k
    by_cases hk128 : k = 128
    · subst k; simp [S₃,h128]
    by_cases hk141 : k = 141
    · subst k; simp [S₃,h141]
    by_cases hk93 : k = 93
    · subst k; simp
    by_cases hk126 : k = 126
    · subst k
      simpa [S₃,S₁,replicaCellR] using congrArg (fun R => R 126) hframe
    have hh := congrArg (fun R => R k) hframe
    simpa [S₃,S₁,replicaCellR,hk128,hk141,hk93,hk126] using hh
  · simpa only [h93] using hpoint
  · simpa only [h93] using herror
  · simpa only [h93,show S₁.R 93 = S.R 93 by simp [S₁,replicaCellR]] using hys

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
