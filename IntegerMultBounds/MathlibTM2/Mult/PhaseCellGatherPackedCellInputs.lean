module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyCountedLine
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOrderedGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval
public import IntegerMultBounds.MathlibTM2.Host.BinArith
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceSchedule

/-! Interior cell RHS gathering from a local packed halo. A single bounded
source copy serves all ordered cell windows; the ambient-period header survives. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- The existing advance controller can start at the halo origin. Its
absolute-coordinate packets then produce local sweep controls directly. -/
theorem originAdvances_translate (w base previous : ℕ) (offsets : List ℕ) :
    originAdvances w (base+previous) (offsets.map (base+·)) = originAdvances w previous offsets := by
  induction offsets generalizing previous with
  | nil => rfl
  | cons j js ih => simp [originAdvances,ih,Nat.add_sub_add_left]

theorem packedGatherControls_eq (w base : ℕ) (offsets : List ℕ) (hne : offsets ≠ []) :
    gatherControls A (originAdvances w base (offsets.map (base+·))++[0]) =
      (match offsets.map (·*w) with
      | [] => [] | j::js => gatherControls A (j::windowAdvances j js)) := by
  change gatherControls A (originAdvances w (base+0) (offsets.map (base+·))++[0]) = _
  rw [originAdvances_translate,originAdvances_symbols]
  cases hm : offsets.map (·*w) with
  | nil => simp at hm; exact False.elim (hne hm)
  | cons j js => simp [originAdvances,originAdvances_window]

/-- Local storage presents exactly the existing arithmetic row, without
changing its ambient origin or period. -/
theorem packedInterval_eq_cellSourceRows {s origin L : ℕ}
    (C : ZMod s → GaussianInt) (hfit : origin+L ≤ s) :
    packedInterval origin L C = cellSourceRows L (fun _ => (origin : ZMod s)) (fun _ => C) 0 := by
  apply List.ext_getElem (by simp [packedInterval_length C hfit])
  intro j hj hk
  have hjL : j < L := by simpa only [packedInterval_length C hfit] using hj
  rw [packedInterval_get C hfit hjL]
  simp [cellSourceRows,Nat.cast_add]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def gatherPackedCellInputs : Pr P 168 Q A U :=
  .seq (toUnary 165 166 0 1 2)
    (.seq (copyCountedLine 166 94 110 92 108 104 105)
      (.seq (naturalGather 110 91 1 2 0 92 3 4 5 6 7 8 9 102 94)
        (clearWords [92,166,91])))

theorem gatherPackedCellInputs_exec {V N L w s origin : ℕ}
    (C : ZMod s → GaussianInt) (hhalo : origin+N ≤ s) (hNV : N < 2^V)
    (offsets : List ℕ) (hne : offsets ≠ []) (hordered : offsets.Pairwise (· ≤ ·))
    (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (tail : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = [])
    (hwidth : (S.R 94).length = w) (hrows : (S.R 102).length = L)
    (hsource : S.R 110 = cstream A w (packedInterval origin N C)++tail)
    (hcontrol : S.R 91 = (match offsets.map (·*w) with
      | [] => [] | j::js => gatherControls A (j::windowAdvances j js)))
    (hclean : ∀ k ∈ [(0 : Fin 168),1,2,3,4,5,6,7,8,9,92,104,105,108], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ offsets.length*(14*L*w+27)+32*N*w+17*N+11*V+6*L*w+9*L+60 ∧
      Exec body gatherPackedCellInputs (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 110
          (offsets.flatMap (fun j => cstream A w (packedInterval (origin+j) L C))++S.R 110)) 91 [])}) := by
  let E := cstream A w (packedInterval origin N C)
  have hlen : E.length = N*w := by simp [E,packedInterval_length C hhalo]
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := toUnary_exec_linear (body := body)
    (a := 165) (z := 166) (w := 0) (t := 1) (t₂ := 2) (by decide) hNV v S h165
    (hclean 0 (by simp)) (hclean 1 (by simp)) (hclean 2 (by simp))
  let B : Stacks 168 A := {S with R := Function.update S.R 166 (List.replicate N tick)}
  have he₁' : Exec body (toUnary 165 166 0 1 2) (mk v S) m₁ (mk v₁ B) := by
    simpa only [h166,List.append_nil] using he₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := copyCountedLine_exec (body := body)
    166 94 110 92 108 104 105 (by decide) N w E tail hlen v₁ B
    (by simp [B]) (by simpa [B] using hwidth) (by simpa [B,E] using hsource)
    (by simpa [B] using hclean 108 (by simp)) (by simpa [B] using hclean 104 (by simp))
    (by simpa [B] using hclean 105 (by simp))
  let G : Stacks 168 A := {B with R := Function.update B.R 92 E}
  have he₂' : Exec body (copyCountedLine 166 94 110 92 108 104 105) (mk v₁ B) m₂ (mk v₂ G) := by
    simpa only [hclean 92 (by simp),List.append_nil,B,Function.update_of_ne (by decide : (92 : Fin 168) ≠ 166)] using he₂
  have ho : (offsets.map (·*w)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact hordered.imp (fun h => Nat.mul_le_mul_right w h)
  have hf : ∀ j ∈ offsets.map (·*w), j+L*w ≤ E.length := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hj
    simpa only [hlen,← Nat.add_mul] using Nat.mul_le_mul_right w (hfit k hk)
  have hcleang : ∀ k ∈ [(1 : Fin 168),2,0,3,4,5,6,7,8,9], G.R k = [] := by
    intro k hk
    have hlo : k.val < 10 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hn92 : k ≠ 92 := by intro he; subst k; norm_num at hlo
    have hn166 : k ≠ 166 := by intro he; subst k; norm_num at hlo
    have hsub : [(1 : Fin 168),2,0,3,4,5,6,7,8,9] ⊆
        [(0 : Fin 168),1,2,3,4,5,6,7,8,9,92,104,105,108] := by
      intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    have hi : S.R k = [] := hclean k (hsub hk)
    simpa [G,B,hn92,hn166] using hi
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := orderedGather_exec (body := body)
    (dst := 110) (control := 91) (savedControl := 1) (advance := 2) (window := 0) (src := 92)
    (acc := 3) (current := 4) (savedSource := 5) (buf := 6) (tmp := 7)
    (initialControl := 8) (initialSource := 9) (rowCount := 102) (wordR := 94)
    (by decide) L w (offsets.map (·*w)) E (by simpa using hne) ho hf v₂ G
    (by cases hm : offsets.map (·*w) <;> simpa [G,B,hm] using hcontrol) (by simp [G]) (by simpa [G,B] using hrows)
    (by simpa [G,B] using hwidth) hcleang
  let rows := offsets.flatMap (fun j => cstream A w (packedInterval (origin+j) L C))
  have hdata : (offsets.map (·*w)).flatMap (fun j => (E.drop j).take (L*w)) = rows := by
    simp only [List.flatMap_map,E,cstream_drop,cstream_take]
    apply List.flatMap_congr
    intro j hj
    rw [packedInterval_crop C (hfit j hj)]
  let F : Stacks 168 A := {G with R := Function.update G.R 110 (rows++G.R 110)}
  have he₃' : Exec body (naturalGather 110 91 1 2 0 92 3 4 5 6 7 8 9 102 94)
      (mk v₂ G) m₃ (mk v₃ F) := by simpa only [hdata] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) [(92 : Fin 168),166,91] (by decide) v₃ F
  have hsum : ([(92 : Fin 168),166,91].map (fun k => (F.R k).length)).sum = N*w+N+(S.R 91).length := by
    simp [F,G,B,hlen,Nat.add_assoc]
  refine ⟨v₄,m₁+(m₂+(m₃+(2*(N*w+N+(S.R 91).length)+7))),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄))).cast (by rw [hsum]; simp) ?_⟩
  · simp only [List.length_map,hlen] at hm₃
    dsimp only [copyCountedLineCost] at hm₂
    have hvol := originAdvances_sum_le w 0 N offsets
      (List.pairwise_cons.mpr ⟨by simp,hordered⟩) (by omega)
      (fun j hj => (Nat.le_add_right j L).trans (hfit j hj))
    have hcontrols : S.R 91 = gatherControls A (originAdvances w 0 offsets++[0]) := by
      rw [hcontrol]
      simpa using (packedGatherControls_eq (A := A) w 0 offsets hne).symm
    have hclen : (S.R 91).length ≤ N*w+offsets.length+1 := by
      rw [hcontrols]
      simp only [length_gatherControls,List.sum_append,List.sum_singleton,Nat.add_zero,
        List.length_append,originAdvances_length,List.length_singleton]
      omega
    nlinarith only [hm₁,hm₂,hm₃,hclen]
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h92 : k = 92 <;> by_cases h166' : k = 166 <;> by_cases h91 : k = 91 <;>
      by_cases h110 : k = 110 <;> simp [F,G,B,rows,h92,h166',h91,h110,h166,hclean 92 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
