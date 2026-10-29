module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellInputBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedBatchFromOrigins

/-! The local input path reuses a retained origin-dependent weight page. The
cache survives the actual numerical call and its error describes the same output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def packedCellCacheReg (i : Fin 121) : Fin 168 := ⟨i.val,by omega⟩

theorem packedCellCacheReg_injective : Function.Injective packedCellCacheReg := by
  intro i j he
  exact Fin.ext (congrArg (fun k : Fin 168 => k.val) he)

theorem packedCellCacheCore_view (S : Stacks 168 A) :
    embStk weightCacheCoreReg (embStk packedCellCacheReg S) = embStk packedCellCoreReg S := rfl

noncomputable def cachedPackedCellBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 168 Q A U :=
  .seq rawPackedCellInputs
    (embProg packedCellCacheReg Empty.elim (cachedBatchFromOrigins (P₀ := Empty) hR hQ))

theorem cachedPackedCellBatch_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp origin N V : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (offsets : List ℕ) (hne : offsets ≠ []) (hordered : offsets.Pairwise (· ≤ ·))
    (hhalo : origin+N ≤ s) (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (I : Finset (ZMod s)) (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) I x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (hint : ∀ r < offsets.length, ∀ k < L,
      Interior s t (PhaseCellBand.width p u) (packedCellOrigin origin offsets r+(k : ZMod s)) ∧
      packedCellOrigin origin offsets r+(k : ZMod s) ∈ I)
    (hcell : ∀ r < offsets.length, ∀ k < L,
      cell s t (packedCellOrigin origin offsets r+(k : ZMod s)) = cell s t (packedCellOrigin origin offsets r))
    (hmax : ∀ r < offsets.length, ∀ k ∈ I,
      cell s t k = cell s t (packedCellOrigin origin offsets r) →
      ∃ i < L, packedCellOrigin origin offsets r+(i : ZMod s) = k)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (2*executionPrecision p l target rhsExp+8) t u)
    (hwV : executionWidth p l target rhsExp < 2^V)
    (hcoords : origin+N < 2^V) (hunits : (origin+N)*executionWidth p l target rhsExp < 2^V)
    (tail outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hbank : embStk packedCellCoreReg S = batchInputBank (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) L offsets.length
      (fun i => (packedCellOrigin (s := s) origin offsets i).val) []
      (cstream A (executionWidth p l target rhsExp) (packedInterval origin N C)++tail) outTail inp out)
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = []) (hV : (S.R 163).length = V)
    (h153 : S.R 153 = []) (h155 : S.R 155 = binSyms V origin) (h154 : S.R 154 = binSyms V 0)
    (cacheTail : List (Fin (A+4)))
    (hcache : S.R 117 = batchWeightPage A (executionWidth p l target rhsExp)
      (executionPrecision p l target rhsExp) (2^15*p) s t u offsets.length L
      (fun i => (packedCellOrigin (s := s) origin offsets i).val)++cacheTail)
    (hcacheCount : (S.R 118).length = 2*(offsets.length*(L*executionWidth p l target rhsExp)))
    (h119 : S.R 119 = []) (h120 : S.R 120 = []) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let lo := packedCellOrigin (s := s) origin offsets
    let rhs := cstream A w ((List.range offsets.length).flatMap (cellSourceRows L lo (fun _ => C)))
    ∃ v' F m, v'.user = v.user ∧
      m ≤ packedCellGroupInputCost V N L w offsets.length q+
        cachedBatchFromOriginsCost p l offsets.length L s t u target rhsExp ∧
      Exec body (cachedPackedCellBatch hR hQ) (mk v S) m (mk v' F) ∧
      (∀ k : Fin 168, 117 ≤ k.val → F.L k = S.L k ∧ F.R k = S.R k) ∧
      (embStk packedCellCoreReg F).inp = inp ∧ (embStk packedCellCoreReg F).out = out ∧
      (∀ k, (embStk packedCellCoreReg F).L k = []) ∧
      (embStk packedCellCoreReg F).R 110 = rhs++(cstream A w (packedInterval origin N C)++tail) ∧
      (∀ k : Fin 117, k ≠ 93 → k ≠ 110 → (embStk packedCellCoreReg F).R k = []) ∧
      (∀ r : Fin offsets.length, ∀ i : Fin L,
        |(value q (decodeWord ((((embStk packedCellCoreReg F).R 93).drop ((r.val*L+i.val)*w)).take w))).re-
          x (lo r+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target) ∧
      (∀ r : Fin offsets.length, PhaseCellInterface.ErrorOn (publishedCellCore (lo r) L)
        (publishedBatchRead q w r.val L (lo r) ((embStk packedCellCoreReg F).R 93)) x (1/(2 : ℝ)^target)) ∧
      ∃ ys : BoundedEncodedStream A w q (interiorOutputExponent p l target rhsExp),
        ys.val.length = offsets.length*L*w ∧ (embStk packedCellCoreReg F).R 93 = ys++outTail := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let lo := packedCellOrigin (s := s) origin offsets
  let rhs := cstream A w ((List.range offsets.length).flatMap (cellSourceRows L lo (fun _ => C)))
  have hw : executionWidth p l target rhsExp = 2*executionPrecision p l target rhsExp+8 := by
    dsimp [executionWidth,executionPrecision]; omega
  have hbank' : embStk packedCellCoreReg S = batchInputBank (2^15*p) (executionStagePrecision p l target rhsExp+1)
      q l s t u (PhaseCellBand.width p u) L offsets.length (fun i => (lo i).val) []
      (cstream A (2*q+8) (packedInterval origin N C)++tail) outTail inp out := by
    simpa only [hw] using hbank
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,hinput⟩ := packedCellInputBank_exec (body := body)
    C hhalo hL offsets hne hordered hfit hVeq (by simpa only [hw] using hwV) hcoords
    (by simpa only [hw] using hunits) tail outTail inp out v S hbank'
    h165 h166 hV h153 h155 h154
  let G : Stacks 168 A := {S with R := Function.update S.R 110 (rhs++S.R 110)}
  have he₁' : Exec body rawPackedCellInputs (mk v S) m₁ (mk v₁ G) := by
    simpa only [G,rhs,lo,w,q,hw] using he₁
  have hfit' : ∀ r < offsets.length, (lo r).val+L ≤ s := by
    intro r hr
    rw [packedCellOrigin_val offsets hhalo hL hfit r hr]
    have hm : offsets[r]?.getD 0 ∈ offsets := by
      simpa only [List.getElem?_eq_getElem hr,Option.getD_some] using List.getElem_mem hr
    have hf := hfit _ hm
    omega
  obtain ⟨vi,M,m₂,hui,hm₂,hei,hcacheFrame,hrest⟩ := cachedBatchFromOrigins_spec
    (body := fun p : Empty => nomatch p) hR hQ hA hp hst hu hαu hθ hgap hbudget hL hLs hpad
    lo (fun _ => C) (fun _ _ k => hC k) I (fun _ => x) (fun _ _ => hx) hfit' hint hcell hmax
    (embDn packedCellCacheReg v₁) (embStk packedCellCacheReg G) outTail
    (cstream A w (packedInterval origin N C)++tail) cacheTail inp out
    (by rw [packedCellCacheCore_view]; simpa only [G,rhs,lo,w,q,hw] using hinput)
    (by simpa [G,embStk,packedCellCacheReg] using hcache)
    (by simpa [G,embStk,packedCellCacheReg] using hcacheCount)
    (by simpa [G,embStk,packedCellCacheReg] using h119)
    (by simpa [G,embStk,packedCellCacheReg] using h120)
  obtain ⟨v₂,F,he₂,hv₂,hu₂,hproj,hframe⟩ := exec_emb (body' := body) (ι := Empty.elim)
    packedCellCacheReg_injective (fun p => nomatch p) hei v₁ rfl G rfl
  have hnative : embStk packedCellCoreReg F = embStk weightCacheCoreReg M := by
    rw [← packedCellCacheCore_view,hproj]
  refine ⟨v₂,F,m₁+m₂,hu₂.trans (hui.trans hu₁),Nat.add_le_add (by simpa only [w,q,hw] using hm₁) hm₂,
    Exec.seq he₁' he₂,?_,?_⟩
  · intro k hk
    by_cases hsmall : k.val < 121
    · let i : Fin 121 := ⟨k.val,hsmall⟩
      have heq : packedCellCacheReg i = k := Fin.ext rfl
      have hl := congrArg (fun B : Stacks 121 A => B.L i) hproj
      have hr := congrArg (fun B : Stacks 121 A => B.R i) hproj
      have hf := hcacheFrame i hk
      have hn : k ≠ 110 := by
        intro he
        have hv := congrArg (fun j : Fin 168 => j.val) he
        norm_num at hv
        omega
      constructor
      · simpa only [embStk_L,heq,G] using hl.trans hf.1
      · simpa [embStk,heq,G,hn] using hr.trans hf.2
    · have hoff : ∀ i, packedCellCacheReg i ≠ k := by
        intro i he
        have hv := congrArg (fun r : Fin 168 => r.val) he
        have hi := i.isLt
        change i.val = k.val at hv
        omega
      have hn : k ≠ 110 := by
        intro he
        have hv := congrArg (fun j : Fin 168 => j.val) he
        norm_num at hv
        omega
      simpa [G,hn] using hframe k hoff
  · simpa only [← hnative] using hrest

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
