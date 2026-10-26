module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedRawRepeatedBatch
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

noncomputable def restoredRawRepeatedBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq (protectedRawRepeatedBatch hR hQ) (.seq retireGroupRHS (uclear 129))

def restoredRawRepeatedBatchCost (p l B L s t u target rhsExp lo : ℕ) : ℕ :=
  rawRepeatedBatchCost p l B L s t u target rhsExp lo +
    12*B*L*executionWidth p l target rhsExp + 6*L*executionWidth p l target rhsExp +
    9*L+15*B+25

theorem restoredRawRepeatedBatch_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed outTail : List (Fin (A+4)))
    (hbank : embStk groupReg S = repeatedBatchInputBank (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) L lo.val B
      (cstream A (executionWidth p l target rhsExp) (replicaAmbientWords B C)) borrowed outTail S.inp S.out)
    (h129 : S.R 129 = []) (h133 : S.R 133 = [])
    (h128 : (S.R 128).length = L)
    (h130 : (S.R 130).length = executionWidth p l target rhsExp)
    (hfresh : ∀ k ∈ [(131 : Fin 144),134,135,136,137], S.R k = []) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' S' n, v'.user = v.user ∧ n ≤ restoredRawRepeatedBatchCost p l B L s t u target rhsExp lo.val ∧
      Exec (embTab groupReg body) (restoredRawRepeatedBatch hR hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = Function.update (restoredGroupR S.R) 93 (S'.R 93) ∧
      (∀ n : Fin B, ∀ i : Fin L, |(value q (decodeWord (((S'.R 93).drop ((n.val*L+i.val)*w)).take w))).re -
        x n (lo+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target) ∧
      (∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore lo L)
        (publishedBatchRead q w n.val L lo (S'.R 93)) (x n) (1/(2 : ℝ)^target)) ∧
      ∃ ys : List (Fin (A+4)), ys.length = B*L*w ∧ S'.R 93 = ys++outTail := by
  dsimp only
  let w := executionWidth p l target rhsExp
  let raw := cstream A w (replicaAmbientWords B C)
  let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L (fun _ => lo) C))
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hi₁,ho₁,hl₁,hrhs,hclean,hcount,hoff,hpoint,herror,ys,hylen,hys⟩ :=
    protectedRawRepeatedBatch_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget
      hB hL hLs hpad lo C hC I x hx hfit hint hcell hmax v S borrowed outTail hbank h129 h133
  have hsrc : S.R 110 = raw++borrowed := by
    have hh := congrArg (fun T : Stacks 117 A => T.R 110) hbank
    simpa [embStk,groupReg,repeatedBatchInputBank,batchInputBank,raw,w] using hh
  have hfresh₁ : ∀ k ∈ [(131 : Fin 144),134,135,136,137], S₁.R k = [] := by
    intro k hk
    have hkval : 117 ≤ k.val := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
    have hk129 : k ≠ 129 := by
      intro he; subst k; norm_num at hk
    rw [hoff k hkval hk129]
    exact hfresh k hk
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := retireGroupRHS_exec (body := embTab groupReg body)
    B L w rhs (raw++borrowed) v₁ S₁
    (by rw [hoff 128 (by decide) (by decide)]; exact h128)
    (by simp [hcount])
    (by rw [hoff 130 (by decide) (by decide)]; exact h130)
    hrhs (by simp [rhs,cellSourceRows,Nat.mul_assoc]) hfresh₁
  let S₂ : Stacks 144 A := { S₁ with R := Function.update S₁.R 110 (raw++borrowed) }
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (embTab groupReg body) 129 v₂ S₂
  let S₃ : Stacks 144 A := { S₂ with R := Function.update S₂.R 129 [] }
  have he₃' : Exec (embTab groupReg body) (uclear 129) (mk v₂ S₂) (2*B+2) (mk v₃ S₃) := by
    simpa [S₂,S₃,hcount] using he₃
  have h93 : S₃.R 93 = S₁.R 93 := by simp [S₃,S₂]
  refine ⟨v₃,S₃,n₁+(n₂+(2*B+2)),hu₃.trans (hu₂.trans hu₁),?_,
    Exec.seq he₁ (Exec.seq he₂ he₃'),hi₁,ho₁,hl₁,?_,?_,?_,ys,hylen,h93.trans hys⟩
  · dsimp only [restoredRawRepeatedBatchCost]
    dsimp only [w] at hn₂
    omega
  · funext k
    by_cases hk93 : k = 93
    · subst k; simp
    by_cases hk110 : k = 110
    · subst k; simpa [S₃,S₂,restoredGroupR] using hsrc.symm
    by_cases hk129 : k = 129
    · subst k; simp [S₃,restoredGroupR,h129]
    simp only [Function.update_of_ne hk93]
    by_cases hlo : k.val < 117
    · simp [S₃,S₂,restoredGroupR,hlo,hk93,hk110,hk129,hclean k hlo hk93 hk110]
    · simp [S₃,S₂,restoredGroupR,hlo,hk110,hk129,hoff k (by omega) hk129]
  · simpa only [h93] using hpoint
  · simpa only [h93] using herror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
