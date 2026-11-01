module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryCursor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryProblem

/-! A single list of indexed boundary fields describes both archives. The
modified RHS is determined by the same entry, so correspondence is structural. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s A : ℕ} [NeZero s]

structure ReplicaRecoveryPreparationCursor (H : ReplicaHaloProblem s) (target : ℕ) (X : ℕ → ZMod s → ℝ)
    (residualTail rhsTail boundaryTail recoveryTail : List (Fin (A+4))) (r : ℕ) (S : Stacks 257 A) : Prop where
  index : r ≤ H.Fs.length
  residual : ∃ Ds : List (ZMod s → GaussianInt), Ds.length = H.Fs.length-r ∧
    S.R 238 = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++residualTail ∧
    ∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-(r+j.val)) Ds[j.val]
  rhs : S.R 93 = (H.Fs.drop r).flatMap (fun C => cstream A H.wordWidth (packedInterval H.origin H.span C))++rhsTail
  archive : ∃ rows : List (ℕ × (ZMod s → GaussianInt)), rows.length = r ∧
    S.R 125 = rows.flatMap (fun z => cstream A H.wordWidth (packedInterval H.origin H.span z.2))++boundaryTail ∧
    S.R 256 = rows.flatMap (fun z => cstream A H.wordWidth
      (packedInterval H.origin H.span (replicaRecoveryRhs H z.1 z.2)))++recoveryTail ∧
    ∀ j : Fin rows.length, rows[j.val].1 = H.Fs.length-r+j.val ∧
      Nonempty (ReplicaRecoveryRow H target rows[j.val].1 rows[j.val].2 (X rows[j.val].1))

namespace ReplicaRecoveryPreparationCursor
variable {H : ReplicaHaloProblem s} {target : ℕ} {X : ℕ → ZMod s → ℝ}
  {residualTail rhsTail boundaryTail recoveryTail : List (Fin (A+4))} {r : ℕ} {S : Stacks 257 A}

theorem initial (H : ReplicaHaloProblem s) (target : ℕ) (X : ℕ → ZMod s → ℝ)
    (S : Stacks 257 A) (Ds : List (ZMod s → GaussianInt)) (hlen : Ds.length = H.Fs.length)
    (hres : S.R 238 = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++residualTail)
    (hgood : ∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) Ds[j.val])
    (hrhs : S.R 93 = H.Fs.flatMap (fun C => cstream A H.wordWidth (packedInterval H.origin H.span C))++rhsTail) :
    ReplicaRecoveryPreparationCursor H target X residualTail rhsTail (S.R 125) (S.R 256) 0 S := by
  refine ⟨Nat.zero_le _,⟨Ds,by simpa using hlen,hres,by simpa using hgood⟩,by simpa using hrhs,
    [],rfl,by simp,by simp,?_⟩
  intro j
  exact Fin.elim0 j

theorem head (h : ReplicaRecoveryPreparationCursor H target X residualTail rhsTail boundaryTail recoveryTail r S)
    (hr : r < H.Fs.length) :
    ∃ D, ∃ Ds : List (ZMod s → GaussianInt), Ds.length = H.Fs.length-(r+1) ∧
      ReplicaCouplingResidualSpec H (H.Fs.length-1-r) D ∧
      S.R 238 = cstream A H.wordWidth (packedInterval H.origin H.span D)++
        (Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++residualTail) ∧
      (∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-(r+1+j.val)) Ds[j.val]) ∧
      S.R 93 = cstream A H.wordWidth (packedInterval H.origin H.span
        (H.Fs.reverse.getD (H.Fs.length-1-r) (fun _ => 0)))++
        ((H.Fs.drop (r+1)).flatMap (fun C => cstream A H.wordWidth (packedInterval H.origin H.span C))++rhsTail) := by
  obtain ⟨rows,hlen,h125,_,_⟩ := h.archive
  have hc : ReplicaRecoveryCursor H (fun _ _ => True) residualTail rhsTail boundaryTail r
      (embStk (Fin.castLE (by decide : 255 ≤ 257)) S) := by
    refine ⟨h.index,h.residual,h.rhs,rows.map Prod.snd,by simp [hlen],?_,fun _ => trivial⟩
    change S.R 125 = _
    simpa only [List.flatMap_map] using h125
  exact hc.head H _ _ _ _ _ _ hr

theorem advance (h : ReplicaRecoveryPreparationCursor H target X residualTail rhsTail boundaryTail recoveryTail r S)
    (hr : r < H.Fs.length) (Ds : List (ZMod s → GaussianInt)) (hlen : Ds.length = H.Fs.length-(r+1))
    (hgood : ∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-(r+1+j.val)) Ds[j.val])
    (Y : ZMod s → GaussianInt)
    (hY : Nonempty (ReplicaRecoveryRow H target (H.Fs.length-1-r) Y (X (H.Fs.length-1-r))))
    (F : Stacks 257 A)
    (hres : F.R 238 = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++residualTail)
    (hrhs : F.R 93 = (H.Fs.drop (r+1)).flatMap (fun C => cstream A H.wordWidth (packedInterval H.origin H.span C))++rhsTail)
    (h125 : F.R 125 = cstream A H.wordWidth (packedInterval H.origin H.span Y)++S.R 125)
    (h256 : F.R 256 = cstream A H.wordWidth
      (packedInterval H.origin H.span (replicaRecoveryRhs H (H.Fs.length-1-r) Y))++S.R 256) :
    ReplicaRecoveryPreparationCursor H target X residualTail rhsTail boundaryTail recoveryTail (r+1) F := by
  obtain ⟨rows,hlenRows,hboundary,hrecovery,hrows⟩ := h.archive
  refine ⟨by omega,⟨Ds,hlen,hres,hgood⟩,hrhs,(H.Fs.length-1-r,Y)::rows,by simp [hlenRows],?_,?_,?_⟩
  · simpa only [List.flatMap_cons,List.append_assoc] using
      h125.trans (congrArg (fun tail => cstream A H.wordWidth (packedInterval H.origin H.span Y)++tail) hboundary)
  · simpa only [List.flatMap_cons,List.append_assoc] using
      h256.trans (congrArg (fun tail => cstream A H.wordWidth
        (packedInterval H.origin H.span (replicaRecoveryRhs H (H.Fs.length-1-r) Y))++tail) hrecovery)
  · intro ⟨j,hj⟩
    cases j with
    | zero => exact ⟨by simp; omega,hY⟩
    | succ j =>
      have hh := hrows ⟨j,by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hj⟩
      simp only at hh
      refine ⟨?_,hh.2⟩
      simp only [List.getElem_cons_succ]
      rw [hh.1]
      omega

theorem finished {S : Stacks 257 A}
    (h : ReplicaRecoveryPreparationCursor H target X residualTail rhsTail boundaryTail recoveryTail H.Fs.length S) :
    S.R 238 = residualTail ∧ S.R 93 = rhsTail ∧
    ∃ B : ReplicaRecoveryBatch H target X,
      S.R 125 = (List.ofFn B.boundary).flatMap
        (fun Y => cstream A H.wordWidth (packedInterval H.origin H.span Y))++boundaryTail ∧
      S.R 256 = B.inputs.reverse.flatMap
        (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))++recoveryTail := by
  obtain ⟨Ds,hlenDs,hres,_⟩ := h.residual
  have hz : Ds = [] := List.length_eq_zero_iff.mp (by simpa using hlenDs)
  refine ⟨by simpa [hz] using hres,by simpa using h.rhs,?_⟩
  obtain ⟨rows,hlen,h125,h256,hrows⟩ := h.archive
  have htag (i : ℕ) (hi : i < rows.length) : rows[i].1 = i := by
    simpa using (hrows ⟨i,hi⟩).1
  let B : ReplicaRecoveryBatch H target X := {
    boundary := fun r => rows[r.val]'(by rw [hlen]; exact r.isLt) |>.2
    row := fun r => by
      have hh := (hrows ⟨r.val,by rw [hlen]; exact r.isLt⟩).2
      rw [htag r.val (by rw [hlen]; exact r.isLt)] at hh
      exact Classical.choice hh }
  have hboundary : rows.map Prod.snd = List.ofFn B.boundary := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_ofFn]
      rfl
  have hrhs : rows.map (fun z => replicaRecoveryRhs H z.1 z.2) =
      List.ofFn (fun r : Fin H.Fs.length => replicaRecoveryRhs H r.val (B.boundary r)) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_ofFn]
      have hi' : i < rows.length := by simpa only [List.length_map] using hi
      change replicaRecoveryRhs H rows[i].1 rows[i].2 = replicaRecoveryRhs H i rows[i].2
      rw [htag i hi']
  refine ⟨B,?_,?_⟩
  · have hh := congrArg (fun ys => ys.flatMap
        (fun Y => cstream A H.wordWidth (packedInterval H.origin H.span Y))++boundaryTail) hboundary
    simp only [List.flatMap_map] at hh
    exact h125.trans hh
  · simp only [ReplicaRecoveryBatch.inputs,List.reverse_reverse]
    have hh := congrArg (fun rs => rs.flatMap
        (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))++recoveryTail) hrhs
    simp only [List.flatMap_map] at hh
    exact h256.trans hh

end ReplicaRecoveryPreparationCursor
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
