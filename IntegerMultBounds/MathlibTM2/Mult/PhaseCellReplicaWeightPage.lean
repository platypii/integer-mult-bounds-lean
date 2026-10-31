module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBatchOrder
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicateWeightPage

/-! Expand one generated multi-cell weight key for a combined replica batch.
Only linear copying is repeated; coefficient evaluation is shared. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

/-- Expand the base numerical page into the exact replica-major cached page,
preserving its following suffix. Scratch and all other tapes restore. -/
theorem replicaWeightPage_exec (w q Pbits s t u N B L : ℕ) (hB : 0 < B) (lo : ℕ → ℕ)
    (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hN : (S.R 116).length = N) (hrows : (S.R 103).length = B*L) (hw : (S.R 94).length = w)
    (hsource : S.R 110 = batchWeightPage A w q Pbits s t u B L lo++tail)
    (hfresh : ∀ k ∈ [(64 : Fin 117),65,104,105,106,107,108], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ replicateWeightPageCost N (B*L) w ∧
      Exec body replicateWeightPage (mk v S) n
        (mk v' {S with R := (Function.update S.R 110
          (batchWeightPage A w q Pbits s t u (N*B) L (fun n => lo (n%B))++tail))}) := by
  let xs := (List.range B).flatMap (fun j => outputWeightRow A w q Pbits s t u L (lo j))
  let ys := (List.range B).flatMap (fun j => inputWeightRow A w q Pbits s t u L (lo j))
  have hxs : xs.length = (B*L)*w := by simp [xs,List.length_flatMap]; ring
  have hys : ys.length = (B*L)*w := by simp [ys,List.length_flatMap]; ring
  have hsrc : S.R 110 = xs++(ys++tail) := by
    simpa only [batchWeightPage,List.append_assoc,xs,ys] using hsource
  obtain ⟨v',n,huser,hcost,he⟩ := replicateWeightPage_exec (body := body)
    N (B*L) w xs ys tail v S hN hrows hw hxs hys hsrc hfresh
  refine ⟨v',n,huser,hcost,?_⟩
  simpa only [batchWeightPage_replicas A w q Pbits s t u N B L hB lo,
    List.append_assoc,xs,ys] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
