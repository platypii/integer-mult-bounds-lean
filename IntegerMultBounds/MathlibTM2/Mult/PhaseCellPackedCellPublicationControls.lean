module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellScatter

/-! Derive local publication gaps from the existing gather advances. The source
controls and batch count are restored by the original conversion machine. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem packedCellPublicationControls_exec {count savedCount control savedControl counter window zero acc dst trash tmp : Fin T}
    (hreg : [count,savedCount,control,savedControl,counter,window,zero,acc,dst,trash,tmp].Nodup)
    (N L w : ℕ) (offsets : List ℕ) (hne : offsets ≠ [])
    (hdis : offsets.Pairwise (fun i j => i+L ≤ j)) (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R count = List.replicate offsets.length tick)
    (hs : S.R control = gatherControls A (originAdvances w 0 offsets++[0])++borrowed)
    (hw : (S.R window).length = L*w)
    (hz : ∀ k ∈ [savedCount,savedControl,counter,zero,acc,trash,tmp], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 12*N*w+21*offsets.length+21 ∧
      Exec body (publicationControls count savedCount control savedControl counter window zero acc dst trash tmp)
        (mk v S) m (mk v' {S with R := (Function.update S.R dst
          (gatherControls A (packedCellGaps L w offsets)++S.R dst))}) := by
  cases ho : offsets with
  | nil => exact False.elim (hne ho)
  | cons p ps =>
    let ds := originAdvances w p ps
    have hsorted : (0::offsets).Pairwise (· ≤ ·) := List.pairwise_cons.mpr
      ⟨by simp,hdis.imp (fun h => by omega)⟩
    have hv := originAdvances_sum_le w 0 N offsets hsorted (Nat.zero_le _)
      (fun j hj => (Nat.le_add_right j L).trans (hfit j hj))
    have hadv : originAdvances w 0 offsets = p*w::ds := by simp [ho,originAdvances,ds]
    have hds : ds.length = ps.length := originAdvances_length w p ps
    have hLd : ∀ d ∈ ds, L*w ≤ d := originAdvances_lower L w p ps (by simpa only [ho] using hdis)
    have hsrc : S.R control = gatherControls A (p*w::ds)++([blank]++borrowed) := by
      rw [hs,hadv,gatherControls_append]
      simp [gatherControls,List.append_assoc]
    obtain ⟨v',m,hu,hm,he⟩ := publicationControls_exec (body := body) hreg (L*w) (p*w) ds hLd
      tick (List.replicate ps.length tick) ([blank]++borrowed) (by simp [hds]) v S
      (by simpa [ho,List.replicate_succ] using hc) hsrc hw hz
    have hgaps : p*w::ds.map (·-L*w) = packedCellGaps L w offsets := by
      have ha := originAdvances_symbols w 0 offsets
      simp only [Nat.zero_mul] at ha
      rw [packedCellGaps,windowGaps_publicationGaps,← ha,hadv]
      rfl
    refine ⟨v',m,hu,?_,by simpa only [hgaps,ho] using he⟩
    rw [hadv,List.sum_cons] at hv
    simp only [Nat.zero_mul,Nat.zero_add] at hv
    simp only [List.length_cons,hds] at hm ⊢
    nlinarith only [hm,hv]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
