module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingLoop

/-! Paired residual/original-RHS queues and the reversed recovered archive.
The cursor is independent of numerical accuracy: its output predicate is supplied
by the complete row theorem, and is checked once when that row is prepended. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s A : ℕ} [NeZero s]

structure ReplicaRecoveryCursor (H : ReplicaHaloProblem s)
    (Good : ℕ → (ZMod s → GaussianInt) → Prop)
    (residualTail rhsTail outputTail : List (Fin (A+4))) (r : ℕ) (S : Stacks 255 A) : Prop where
  index : r ≤ H.Fs.length
  residual : ∃ Ds : List (ZMod s → GaussianInt), Ds.length = H.Fs.length-r ∧
    S.R 238 = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++residualTail ∧
    ∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-(r+j.val)) Ds[j.val]
  rhs : S.R 93 = (H.Fs.drop r).flatMap (fun F => cstream A H.wordWidth (packedInterval H.origin H.span F))++rhsTail
  output : ∃ Es : List (ZMod s → GaussianInt), Es.length = r ∧
    S.R 125 = Es.flatMap (fun E => cstream A H.wordWidth (packedInterval H.origin H.span E))++outputTail ∧
    ∀ j : Fin Es.length, Good (r-1-j.val) Es[j.val]

theorem ReplicaRecoveryCursor.initial (H : ReplicaHaloProblem s) Good residualTail rhsTail
    (S : Stacks 255 A) (Ds : List (ZMod s → GaussianInt)) (hlen : Ds.length = H.Fs.length)
    (hres : S.R 238 = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++residualTail)
    (hgood : ∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) Ds[j.val])
    (hrhs : S.R 93 = H.Fs.flatMap (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))++rhsTail) :
    ReplicaRecoveryCursor H Good residualTail rhsTail (S.R 125) 0 S := by
  refine ⟨Nat.zero_le _,⟨Ds,by simpa using hlen,hres,by simpa using hgood⟩,
    by simpa using hrhs,[],rfl,by simp,?_⟩
  intro j
  exact Fin.elim0 j

theorem ReplicaRecoveryCursor.of_frame (H : ReplicaHaloProblem s) Good residualTail rhsTail outputTail r (S F : Stacks 255 A)
    (h : ReplicaRecoveryCursor H Good residualTail rhsTail outputTail r S)
    (h238 : F.R 238 = S.R 238) (h93 : F.R 93 = S.R 93) (h125 : F.R 125 = S.R 125) :
    ReplicaRecoveryCursor H Good residualTail rhsTail outputTail r F := by
  obtain ⟨Ds,hlen,hres,hgood⟩ := h.residual
  obtain ⟨Es,hlenE,hout,hEs⟩ := h.output
  exact ⟨h.index,⟨Ds,hlen,h238.trans hres,hgood⟩,h93.trans h.rhs,
    ⟨Es,hlenE,h125.trans hout,hEs⟩⟩

theorem ReplicaRecoveryCursor.head (H : ReplicaHaloProblem s) Good residualTail rhsTail outputTail r S
    (h : ReplicaRecoveryCursor H Good residualTail rhsTail outputTail r S) (hr : r < H.Fs.length) :
    ∃ D, ∃ Ds : List (ZMod s → GaussianInt), Ds.length = H.Fs.length-(r+1) ∧
      ReplicaCouplingResidualSpec H (H.Fs.length-1-r) D ∧
      S.R 238 = cstream A H.wordWidth (packedInterval H.origin H.span D)++
        (Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++residualTail) ∧
      (∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-(r+1+j.val)) Ds[j.val]) ∧
      S.R 93 = cstream A H.wordWidth (packedInterval H.origin H.span
        (H.Fs.reverse.getD (H.Fs.length-1-r) (fun _ => 0)))++
        ((H.Fs.drop (r+1)).flatMap (fun F => cstream A H.wordWidth (packedInterval H.origin H.span F))++rhsTail) := by
  obtain ⟨Ds,hlen,hres,hgood⟩ := h.residual
  have hne : Ds ≠ [] := by intro hz; simp [hz] at hlen; omega
  obtain ⟨D,Ds,rfl⟩ := List.exists_cons_of_ne_nil hne
  have hreverse : H.Fs.reverse.getD (H.Fs.length-1-r) (fun _ => 0) = H.Fs[r] := by
    rw [List.getD_eq_getElem _ _ (by simp; omega),List.getElem_reverse]
    congr 1
    omega
  refine ⟨D,Ds,by simp only [List.length_cons] at hlen; omega,
    by simpa using hgood ⟨0,by simp⟩,?_,?_,?_⟩
  · simpa only [List.flatMap_cons,List.append_assoc] using hres
  · intro j
    have hh := hgood ⟨j.val+1,by simpa using Nat.succ_lt_succ j.isLt⟩
    simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1] using hh
  · rw [h.rhs,List.drop_eq_getElem_cons hr,List.flatMap_cons,List.append_assoc,hreverse]

theorem ReplicaRecoveryCursor.advance (H : ReplicaHaloProblem s) Good residualTail rhsTail outputTail r S
    (h : ReplicaRecoveryCursor H Good residualTail rhsTail outputTail r S) (hr : r < H.Fs.length)
    (Ds : List (ZMod s → GaussianInt)) (hlen : Ds.length = H.Fs.length-(r+1))
    (hgood : ∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-(r+1+j.val)) Ds[j.val])
    (E : ZMod s → GaussianInt) (hE : Good r E) (F : Stacks 255 A)
    (hres : F.R 238 = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++residualTail)
    (hrhs : F.R 93 = (H.Fs.drop (r+1)).flatMap (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))++rhsTail)
    (hout : F.R 125 = cstream A H.wordWidth (packedInterval H.origin H.span E)++S.R 125) :
    ReplicaRecoveryCursor H Good residualTail rhsTail outputTail (r+1) F := by
  obtain ⟨Es,hlenE,harchive,hEs⟩ := h.output
  refine ⟨by omega,⟨Ds,hlen,hres,hgood⟩,hrhs,E::Es,by simp [hlenE],?_,?_⟩
  · simpa only [List.flatMap_cons,List.append_assoc] using hout.trans
      (congrArg (fun xs => cstream A H.wordWidth (packedInterval H.origin H.span E)++xs) harchive)
  · intro ⟨j,hj⟩
    cases j with
    | zero => simpa using hE
    | succ j =>
      have hh := hEs ⟨j,by simp only [List.length_cons,Nat.succ_lt_succ_iff] at hj; exact hj⟩
      simpa only [List.getElem_cons_succ,show r+1-1-(j+1) = r-1-j by omega] using hh

theorem ReplicaRecoveryCursor.finished (H : ReplicaHaloProblem s) Good residualTail rhsTail outputTail S
    (h : ReplicaRecoveryCursor H Good residualTail rhsTail outputTail H.Fs.length S) :
    S.R 238 = residualTail ∧ S.R 93 = rhsTail ∧
    ∃ Es : List (ZMod s → GaussianInt), Es.length = H.Fs.length ∧
      S.R 125 = Es.flatMap (fun E => cstream A H.wordWidth (packedInterval H.origin H.span E))++outputTail ∧
      ∀ j : Fin Es.length, Good (H.Fs.length-1-j.val) Es[j.val] := by
  obtain ⟨Ds,hlen,hres,_⟩ := h.residual
  have hz : Ds = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
  exact ⟨by simpa [hz] using hres,by simpa using h.rhs,h.output⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
