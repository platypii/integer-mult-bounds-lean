module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDoubleWeightedEntry

/-! Write the entire weighted residual from the conjugated projector and its weight tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal Node
variable {T Q A m n M : ℕ} [NeZero M] {P U : Type}

def upperEntryPorts : Fin 14 ↪ Fin 17 := ⟨![14,1,2,16,4,5,6,7,8,9,10,11,12,13],by decide⟩
def lowerEntryPorts : Fin 14 ↪ Fin 17 := ⟨![15,1,2,16,4,5,6,7,8,9,10,11,12,13],by decide⟩
def complementEntryPorts : Fin 14 ↪ Fin 17 := ⟨![0,1,2,3,4,5,6,7,16,9,10,11,12,13],by decide⟩

def blockEntry (ports : Fin m → Fin m → Fin 17 ↪ Fin T) : Fin m ⊕ Fin m → Fin m ⊕ Fin m → Pr P T Q A U
  | .inl i, .inl j => doubleWeightedEntry (i.val*m+j.val) (ports i j)
  | .inl i, .inr j => weightedEntry (i.val*m+j.rev.val) (upperEntryPorts.trans (ports i j.rev))
  | .inr i, .inl j => weightedEntry (i.rev.val*m+j.val) (lowerEntryPorts.trans (ports i.rev j))
  | .inr i, .inr j => complementEntry (i.rev.val*m+j.rev.val) (complementEntryPorts.trans (ports i.rev j.rev))

def projectorBank (ports : Fin m → Fin m → Fin 17 ↪ Fin T) (B : Matrix (Fin m) (Fin m) (ZMod M))
    (α α' : Fin m → ZMod M) (H : ℕ) (tail : List (Fin (A+4))) (R : Regs T A) :=
  ∀ i j, let r := ports i j
    R (r 13) = matrixWords A H B ++ tail ∧
    R (r 0) = binSyms H ((1 : Matrix (Fin m) (Fin m) (ZMod M)) i j).val ∧
    R (r 2) = binSyms H M ∧ R (r 14) = binSyms H (α i).val ∧ R (r 15) = binSyms H (α' j).val ∧
    ∀ k : Fin 17, k = 1 ∨ 3 ≤ k ∧ k ≤ 12 → R (r k) = []

theorem projectorWriter_exec (body : P → Pr P T Q A U) (ports : Fin m → Fin m → Fin 17 ↪ Fin T)
    (out : Fin T) (shared : ∀ i j, ports i j 16 = out) (e : (Fin m ⊕ Fin m) ≃ Fin n)
    (proj g : Matrix (Fin m) (Fin m) (ZMod M)) (α α' : Fin m → ZMod M) (H : ℕ) (hm : M < 2^H)
    (tail : List (Fin (A+4))) :
    let c := 8*(m*m*H)+96*H*H+344*H+182
    Writes body (projectorBank ports (g*proj*g⁻¹) α α' H tail) out
      (sequence (fun i => sequence (fun j => blockEntry ports (e.symm i) (e.symm j)) (List.finRange n)) (List.finRange n))
      (matrixWords A H (projectorResidual e proj α α' g)) (n*(n*c+1)+1) := by
  intro c
  let B := g*proj*g⁻¹
  apply projectorWords_writes
  · intro R xs ok i j
    have keep (k : Fin 17) (hk : k ≠ 16) : Function.update R out xs (ports i j k) = R (ports i j k) := by
      rw [← shared i j]; exact Function.update_of_ne ((ports i j).injective.ne hk) _ _
    obtain ⟨a,b,f,h,l,s⟩ := ok i j
    exact ⟨(keep 13 (by decide)).trans a,(keep 0 (by decide)).trans b,(keep 2 (by decide)).trans f,
      (keep 14 (by decide)).trans h,(keep 15 (by decide)).trans l,fun k hk => (keep k (by omega)).trans (s k hk)⟩
  · have offset (i j : Fin m) : (i.val*m+j.val)*H ≤ m*m*H := by
      apply Nat.mul_le_mul_right
      have hi := i.isLt
      have hj := j.isLt
      nlinarith only [Nat.mul_le_mul_right m (show i.val+1 ≤ m by omega),hj]
    intro x y v S ok
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        obtain ⟨z,l,hz,hl,run⟩ := doubleWeightedEntry_writes body (ports i j) B i j (α i) (α' j) H hm tail v S (ok i j)
        rw [shared] at run
        exact ⟨z,l,hz,by dsimp [c]; linarith [offset i j],run⟩
      | inr j =>
        obtain ⟨a,_,f,h,_,s⟩ := ok i j.rev
        have work : ∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 → upperEntryPorts k = 1 ∨ 3 ≤ upperEntryPorts k ∧ upperEntryPorts k ≤ 12 := by decide
        obtain ⟨z,l,hz,hl,run⟩ := weightedEntry_writes body (upperEntryPorts.trans (ports i j.rev)) B i j.rev (α i) H hm tail v S
          ⟨a,h,f,fun k hk => s _ (work k hk)⟩
        rw [show (upperEntryPorts.trans (ports i j.rev)) 3 = out from shared ..] at run
        exact ⟨z,l,hz,by dsimp [c]; nlinarith only [hl,offset i j.rev],run⟩
    | inr i =>
      cases y with
      | inl j =>
        obtain ⟨a,_,f,_,h,s⟩ := ok i.rev j
        have work : ∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 → lowerEntryPorts k = 1 ∨ 3 ≤ lowerEntryPorts k ∧ lowerEntryPorts k ≤ 12 := by decide
        obtain ⟨z,l,hz,hl,run⟩ := weightedEntry_writes body (lowerEntryPorts.trans (ports i.rev j)) B i.rev j (α' j) H hm tail v S
          ⟨a,h,f,fun k hk => s _ (work k hk)⟩
        rw [show (lowerEntryPorts.trans (ports i.rev j)) 3 = out from shared ..,mul_comm (α' j)] at run
        exact ⟨z,l,hz,by dsimp [c]; nlinarith only [hl,offset i.rev j],run⟩
      | inr j =>
        obtain ⟨a,b,f,_,_,s⟩ := ok i.rev j.rev
        have work : ∀ k : Fin 14, k = 1 ∨ 3 ≤ k ∧ k ≤ 7 → complementEntryPorts k = 1 ∨ 3 ≤ complementEntryPorts k ∧ complementEntryPorts k ≤ 12 := by decide
        obtain ⟨z,l,hz,hl,run⟩ := complementEntry_writes body (complementEntryPorts.trans (ports i.rev j.rev)) B i.rev j.rev H hm tail v S
          ⟨a,b,f,fun k hk => s _ (work k hk)⟩
        rw [show (complementEntryPorts.trans (ports i.rev j.rev)) 8 = out from shared ..] at run
        exact ⟨z,l,hz,by dsimp [c]; nlinarith only [hl,offset i.rev j.rev],run⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
