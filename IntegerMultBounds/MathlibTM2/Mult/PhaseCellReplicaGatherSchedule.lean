module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaGatherData

/-! Same-origin windows in consecutive RHS lines form one forward sweep.
Each line contributes one complete in-bounds window, in replica order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

def replicaSymbolOrigins (B s p w : ℕ) : List ℕ :=
  (List.range B).map (fun n => (n*s+p)*w)

theorem replicaSymbolOrigins_ordered (B s p w : ℕ) :
    (replicaSymbolOrigins B s p w).Pairwise (· ≤ ·) := by
  apply List.pairwise_map.mpr
  exact List.pairwise_le_range.imp (fun h =>
    Nat.mul_le_mul_right w (Nat.add_le_add_right (Nat.mul_le_mul_right s h) p))

theorem replicaSymbolOrigins_fit (B s p L w : ℕ) (hfit : p+L ≤ s) :
    ∀ q ∈ replicaSymbolOrigins B s p w, q+L*w ≤ B*s*w := by
  intro q hq
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hq
  have hnB : n+1 ≤ B := List.mem_range.mp hn
  have hi : n*s+(p+L) ≤ B*s :=
    (Nat.add_le_add_left hfit (n*s)).trans (by
      simpa [Nat.add_mul] using Nat.mul_le_mul_right s hnB)
  simpa only [Nat.add_mul,Nat.mul_assoc,Nat.add_assoc] using Nat.mul_le_mul_right w hi

theorem replicaGatherRows_eq_rhs {A s : ℕ} (B p L w : ℕ) (C : ℕ → ZMod s → GaussianInt)
    (hfit : p+L ≤ s) (q : ℕ) (qs : List ℕ) (horigins : replicaSymbolOrigins B s p w = q::qs) :
    gatherRows (L*w) ((cstream A w (replicaAmbientWords B C)).drop q) (windowAdvances q qs) =
      cstream A w ((List.range B).flatMap (cellSourceRows L (fun _ => (p : ZMod s)) C)) := by
  have ho := replicaSymbolOrigins_ordered B s p w
  rw [horigins] at ho
  rw [gatherRows_windowAdvances (L*w) q qs _ ho,← horigins]
  simp only [replicaSymbolOrigins,List.flatMap_map]
  simp only [cstream,List.flatMap_assoc]
  apply List.flatMap_congr
  intro n hn
  exact replicaAmbientStream_window w B C p L n (List.mem_range.mp hn) hfit

def replicaGatherControls (A B s p w : ℕ) : List (Fin (A+4)) :=
  match replicaSymbolOrigins B s p w with
  | [] => []
  | q::qs => gatherControls A (q::windowAdvances q qs)

theorem replicaSymbolOrigins_succ (B s p w : ℕ) :
    replicaSymbolOrigins (B+1) s p w = p*w::replicaSymbolOrigins B s (s+p) w := by
  simp only [replicaSymbolOrigins,List.range_succ_eq_map,List.map_cons,List.map_map,
    Nat.zero_mul,Nat.zero_add]
  congr 1
  apply List.map_congr_left
  intro n _
  dsimp only [Function.comp_apply]
  simp only [Nat.succ_eq_add_one]
  ring

theorem replicaWindowAdvances (B s p w : ℕ) :
    windowAdvances (p*w) (replicaSymbolOrigins B s (s+p) w) =
      List.replicate B (s*w)++[0] := by
  induction B generalizing p with
  | zero => simp [replicaSymbolOrigins,windowAdvances]
  | succ B ih =>
    rw [replicaSymbolOrigins_succ]
    simp only [windowAdvances,Nat.add_mul,Nat.add_sub_cancel_right]
    rw [← Nat.add_mul,ih]
    rfl

theorem replicaGatherControls_succ (A B s p w : ℕ) :
    replicaGatherControls A (B+1) s p w =
      gatherControls A (p*w::(List.replicate B (s*w)++[0])) := by
  simp only [replicaGatherControls,replicaSymbolOrigins_succ,replicaWindowAdvances]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
