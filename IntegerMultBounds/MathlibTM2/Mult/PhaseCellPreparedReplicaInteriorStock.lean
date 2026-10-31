module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaInteriorCache
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaInteriorBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedOriginsStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPreparationStock

/-! Prepared replica execution retains its numerical guarantees and simultaneous stock bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 121 Q A U}

theorem preparedReplicaInteriorBatch_exec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l N B L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hB : 0 < B) (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ r < N, ∀ k, ‖value (executionPrecision p l target rhsExp) (C r k)‖ ≤ (2 : ℝ)^rhsExp)
    (I : Finset (ZMod s)) (x : ℕ → ZMod s → ℝ)
    (hx : ∀ r < N, SchurDominance.Solves (realMatrix s t p u) I (x r)
      (fun k => (value (executionPrecision p l target rhsExp) (C r k)).re))
    (hfit : ∀ j < B, (lo j).val+L ≤ s)
    (hint : ∀ j < B, ∀ k < L, Interior s t (PhaseCellBand.width p u) (lo j+(k : ZMod s)) ∧
      lo j+(k : ZMod s) ∈ I)
    (hcell : ∀ j < B, ∀ k < L, cell s t (lo j+(k : ZMod s)) = cell s t (lo j))
    (hmax : ∀ j < B, ∀ k ∈ I, cell s t k = cell s t (lo j) → ∃ i < L, lo j+(i : ZMod s) = k)
    (v : HS 121 Q A U) (S : Stacks 121 A) (tail borrowed : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock ScalarPlacement.cr
      (rmulOne (P := Empty) (Q := Q) (A := A) (U := U) ScalarPlacement.mul
        ScalarPlacement.mul_injective (by decide) hQ ScalarPlacement.cr)) ≤ K) (depth : ℕ) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let stage := executionStagePrecision p l target rhsExp
    let rhs := cstream A w ((List.range N).flatMap (fun r =>
      (List.range B).flatMap (cellSourceRows L lo (fun _ => C r))))
    embStk weightCacheCoreReg S = replicaInteriorCacheInputBank A (2^15*p) (stage+1) q l s t u
      (PhaseCellBand.width p u) N B L w (fun j => (lo j).val) rhs borrowed tail inp out →
    S.R 118 = [] → S.R 119 = [] → S.R 120 = [] →
    ∃ v' F n, v'.user = v.user ∧
      n ≤ prepareReplicaInteriorCacheCost N B L w+cachedBatchFromOriginsCost p l (N*B) L s t u target rhsExp ∧
      ExecWithin body (fun level z => mnSize z + level ≤ mnSize (mk v S) + depth +
        (3 * prepareReplicaInteriorCacheCost N B L w +
          cachedOriginsWorkspace (P₀ := P) (A := A) (U := U) hQ R K p l (N*B) L s t u target rhsExp))
        depth (preparedReplicaInteriorBatch hR hQ) (mk v S) n (mk v' F) ∧
      (embStk weightCacheCoreReg F).inp = inp ∧ (embStk weightCacheCoreReg F).out = out ∧
      (∀ k, (embStk weightCacheCoreReg F).L k = []) ∧
      (embStk weightCacheCoreReg F).R 110 = rhs++borrowed ∧
      (∀ k : Fin 117, k ≠ 93 → k ≠ 110 → (embStk weightCacheCoreReg F).R k = []) ∧
      F.R 117 = batchWeightPage A w q (2^15*p) s t u (N*B) L (fun n => (lo (n%B)).val)++S.R 117 ∧
      F.R 118 = List.replicate (2*((N*B)*(L*w))) tick ∧ F.R 119 = [] ∧ F.R 120 = [] ∧
      (∀ r : Fin N, ∀ j : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore (lo j) L)
        (publishedBatchRead q w (r.val*B+j.val) L (lo j) ((embStk weightCacheCoreReg F).R 93))
        (x r) (1/(2 : ℝ)^target)) ∧
      ∃ ys : BoundedEncodedStream A w q (interiorOutputExponent p l target rhsExp),
        ys.val.length = (N*B)*L*w ∧ (embStk weightCacheCoreReg F).R 93 = ys++tail := by
  dsimp only
  intro hbank h118 h119 h120
  obtain ⟨vf,Ff,nf,huf,hnf,hef,hrest⟩ := preparedReplicaInteriorBatch_exec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hB hL hLs hpad lo C hC
    I x hx hfit hint hcell hmax v S tail borrowed inp out hbank h118 h119 h120
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let stage := executionStagePrecision p l target rhsExp
  let rhs := cstream A w ((List.range N).flatMap (fun r =>
    (List.range B).flatMap (cellSourceRows L lo (fun _ => C r))))
  obtain ⟨v₁,M,n₁,hu₁,hn₁,he₁,hbankM,hcache,hclock,h119M,h120M⟩ :=
    prepareReplicaInteriorCache_exec (body := body) (2^15*p) (stage+1) q l s t u
      (PhaseCellBand.width p u) N B L w hB (fun j => (lo j).val) rhs borrowed tail inp out v S hbank (by
        intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl
        · exact h118
        · exact h119
        · exact h120)
  have ht₁ := mn_native_exec_within he₁ 3 prepareReplicaInteriorCache_native depth
    (mnSize (mk v S) + depth + 3 * prepareReplicaInteriorCacheCost N B L w)
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hn₁) _)
  obtain ⟨v₂,F₂,n₂,hu₂,hn₂,he₂,hproj₂,hoff₂⟩ := cachedBatchFromOrigins_exec_within (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hL hpad
    (fun n => lo (n%B)) (fun n => C (n/B))
    (fun n hn => hC _ ((Nat.div_lt_iff_lt_mul hB).mpr hn))
    v₁ M tail borrowed (S.R 117) inp out R K hpushR hpushK depth
    (by simpa only [replicaInteriorRows_eq N B L hB lo C] using hbankM)
    hcache (by rw [hclock,List.length_replicate]) h119M h120M
  have ht := mn_seq_within_add ht₁ he₂
  obtain ⟨heqn,heqF⟩ := ht.toExec.unique hef
  rw [heqn,heqF] at ht
  exact ⟨vf,Ff,nf,huf,hnf,ht,hrest⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
