module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredRawRepeatedBatch
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

noncomputable def retainedRawRepeatedBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq installGroupHeaders (.seq installReplicaHeaders (restoredRawRepeatedBatch hR hQ))

def retainedRawRepeatedBatchCost (p l B L s t u target rhsExp lo : ℕ) : ℕ :=
  installGroupHeadersCost (2^15*p) (executionStagePrecision p l target rhsExp+1)
    (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) L+
      (4*B+4*lo+9)+restoredRawRepeatedBatchCost p l B L s t u target rhsExp lo

theorem retainedRawRepeatedBatch_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l B L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
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
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) L r.1)
    (hleft : ∀ k : Fin 144, k.val < 117 → S.L k = [])
    (hblank : ∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = [])
    (hsrc : S.R 110 = cstream A (executionWidth p l target rhsExp) (replicaAmbientWords B C)++borrowed)
    (h142 : (S.R 142).length = B) (h141 : (S.R 141).length = lo.val)
    (h129 : S.R 129 = []) (h133 : S.R 133 = [])
    (h128 : (S.R 128).length = L)
    (h130 : (S.R 130).length = executionWidth p l target rhsExp)
    (hfresh : ∀ k ∈ [(131 : Fin 144),134,135,136,137], S.R k = []) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' S' n, v'.user = v.user ∧ n ≤ retainedRawRepeatedBatchCost p l B L s t u target rhsExp lo.val ∧
      Exec (embTab groupReg body) (retainedRawRepeatedBatch hR hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = Function.update S.R 93 (S'.R 93) ∧
      (∀ n : Fin B, ∀ i : Fin L, |(value q (decodeWord (((S'.R 93).drop ((n.val*L+i.val)*w)).take w))).re -
        x n (lo+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target) ∧
      (∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore lo L)
        (publishedBatchRead q w n.val L lo (S'.R 93)) (x n) (1/(2 : ℝ)^target)) ∧
      ∃ ys : List (Fin (A+4)), ys.length = B*L*w ∧ S'.R 93 = ys++S.R 93 := by
  dsimp only
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let band := PhaseCellBand.width p u
  obtain ⟨v₁,hu₁,he₁⟩ := installGroupHeaders_exec (body := embTab groupReg body)
    P N q l s t u band L v S hmasters h133
  let S₁ : Stacks 144 A := {S with R := copiedGroupR P N q l s t u band L S.R}
  have hoff₁ (k : Fin 144) (hk : 117 ≤ k.val) : S₁.R k = S.R k :=
    copiedGroupR_off P N q l s t u band L S.R k hk
  obtain ⟨v₂,hu₂,he₂⟩ := installReplicaHeaders_exec (body := embTab groupReg body) B lo.val v₁ S₁
    (by rw [hoff₁ 142 (by decide)]; exact h142)
    (by rw [hoff₁ 141 (by decide)]; exact h141)
    (by rw [hoff₁ 133 (by decide)]; exact h133)
  let S₂ : Stacks 144 A := {S₁ with R := copiedReplicaR B lo.val S₁.R}
  have hoff₂ (k : Fin 144) (hk : 117 ≤ k.val) : S₂.R k = S.R k := by
    rw [show S₂.R k = S₁.R k from copiedReplicaR_off B lo.val S₁.R k
      (by intro he; subst k; norm_num at hk) (by intro he; subst k; norm_num at hk)]
    exact hoff₁ k hk
  have h93 : S₂.R 93 = S.R 93 := by
    rw [show S₂.R 93 = S₁.R 93 from copiedReplicaR_off B lo.val S₁.R 93 (by decide) (by decide)]
    apply unaryCopiesR_off
    intro r hr he
    simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases he
  have hbank := copiedReplica_project P N q l s t u band L lo.val B S
    (cstream A (executionWidth p l target rhsExp) (replicaAmbientWords B C)) borrowed hleft hblank hsrc
  obtain ⟨v₃,S₃,n₃,hu₃,hn₃,he₃,hi,ho,hl,hframe,hpoint,herror,ys,hylen,hys⟩ :=
    restoredRawRepeatedBatch_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget
      hB hL hLs hpad lo C hC I x hx hfit hint hcell hmax v₂ S₂ borrowed (S.R 93)
      hbank (by rw [hoff₂ 129 (by decide)]; exact h129)
      (by rw [hoff₂ 133 (by decide)]; exact h133)
      (by rw [hoff₂ 128 (by decide)]; exact h128)
      (by rw [hoff₂ 130 (by decide)]; exact h130)
      (by intro k hk
          have hkval : 117 ≤ k.val := by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
          rw [hoff₂ k hkval]; exact hfresh k hk)
  have hrestore : restoredGroupR S₂.R = S.R := by
    apply restoredGroupR_frame S₂.R S.R h93
    · have hh := congrArg (fun T : Stacks 117 A => T.R 110) hbank
      simpa [embStk,groupReg,repeatedBatchInputBank,batchInputBank,hsrc] using hh
    · exact hoff₂
    · exact hblank
  refine ⟨v₃,S₃,installGroupHeadersCost P N q l s t u band L+((4*B+4*lo.val+9)+n₃),
    hu₃.trans (hu₂.trans hu₁),?_,Exec.seq he₁ (Exec.seq he₂ he₃),hi,ho,hl,?_,hpoint,herror,ys,hylen,hys⟩
  · dsimp only [retainedRawRepeatedBatchCost,P,N,q,band]
    omega
  · rw [hframe,hrestore]; simp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
