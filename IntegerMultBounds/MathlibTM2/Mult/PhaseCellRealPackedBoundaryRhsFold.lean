module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRhsFold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealReplicaRows

/-! Real projection and the existing linear fold share the retained row headers.
The numerical operation is independent of cyclic geometry and replica count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def realPackedBoundaryRhsFold : Pr P 168 Q A U :=
  .seq (realReplicaRows 116 130 143 77 78 79) packedBoundaryRhsFold

def realPackedBoundaryRhsFoldCost (N w : ℕ) :=
  realReplicaRowsCost N w+(60*(N+1)*w+60*N+60)

theorem realPackedBoundaryRhsFold_exec (s : ℕ) [NeZero s] (B : Finset (ZMod s))
    (C : ZMod s → GaussianInt) (w : ℕ) (hA : 4 ≤ A) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hsource : S.R 143 = cstream A w ((bOrder s B).map C))
    (hwidth : (S.R 130).length = w) (hcount : (S.R 116).length = B.card)
    (hfloor : (S.R 0).length = B.card/2)
    (hparity : (S.R 2).length = (B.card+1)/2-B.card/2)
    (hbytes : (S.R 3).length = ((B.card+1)/2)*w)
    (hblank : ∀ r : Fin 168, 6 ≤ r.val → r.val < 80 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ realPackedBoundaryRhsFoldCost B.card w ∧
      Exec body realPackedBoundaryRhsFold (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 143 []) 6
          (cstream A w ((bFoldOrder s B).map (fun i => realPartWord (C i)))))}) := by
  let xs := cstream A w ((bOrder s B).map C)
  have hxs : xs.length = B.card*w := by
    rw [length_cstream,List.length_map]
    rw [← List.toFinset_card_of_nodup (bOrder_nodup s B),bOrder_toFinset]
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := realReplicaRows_exec_within (body := body)
    116 130 143 77 78 79 (by decide) B.card w v S xs [] hcount hwidth
    (by simpa only [List.append_nil] using hsource) hxs
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact hblank _ (by decide) (by decide)) 0
  let J : Stacks 168 A := {S with R := (Function.update S.R 143
    (cstream A w ((bOrder s B).map (fun i => realPartWord (C i)))))}
  have he₁' : Exec body (realReplicaRows 116 130 143 77 78 79) (mk v S) m₁ (mk v₁ J) := by
    simpa only [J,realPartSymbol_cstream hA,List.map_map,Function.comp_def,List.append_nil,xs] using he₁.toExec
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := packedBoundaryRhsFold_exec (body := body)
    s B (fun i => realPartWord (C i)) w v₁ J
    (by simp [J]) (by simpa [J] using hwidth) (by simpa [J] using hcount)
    (by simpa [J] using hfloor) (by simpa [J] using hparity) (by simpa [J] using hbytes)
    (by intro r hr6 hr77
        have hr : r ≠ 143 := by intro h; subst r; norm_num at hr77
        simpa [J,hr] using hblank r hr6 (by omega))
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,
    (Exec.seq he₁' he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk : k = 143 <;> simp [J,hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
