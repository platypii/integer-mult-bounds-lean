module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackComplementEntry

/-! Emit the upper-left block from the complementary projector and both tape weights. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal
variable {T Q A d M : ℕ} [NeZero M] {P U : Type}

def leftWeightPorts : Fin 13 ↪ Fin 17 := ⟨![14,8,2,1,4,5,6,7,9,10,11,12,3],by decide⟩
def rightWeightPorts : Fin 13 ↪ Fin 17 := ⟨![15,1,2,16,4,5,6,7,9,10,11,12,3],by decide⟩

def doubleWeightedEntry (offset : ℕ) (r : Fin 17 ↪ Fin T) : Pr P T Q A U :=
  scaleEntry (scaleEntry (complementEntry offset ((Fin.castLEEmb (by decide)).trans r))
    (leftWeightPorts.trans r)) (rightWeightPorts.trans r)

theorem doubleWeightedEntry_writes (body : P → Pr P T Q A U) (r : Fin 17 ↪ Fin T)
    (B : Matrix (Fin d) (Fin d) (ZMod M)) (i j : Fin d) (left right : ZMod M) (H : ℕ) (hm : M < 2^H)
    (tail : List (Fin (A+4))) :
    Writes body (fun R => R (r 13) = matrixWords A H B ++ tail ∧
      R (r 0) = binSyms H ((1 : Matrix (Fin d) (Fin d) (ZMod M)) i j).val ∧ R (r 2) = binSyms H M ∧
      R (r 14) = binSyms H left.val ∧ R (r 15) = binSyms H right.val ∧
      ∀ k : Fin 17, k = 1 ∨ 3 ≤ k ∧ k ≤ 12 → R (r k) = [])
      (r 16) (doubleWeightedEntry (i.val*d+j.val) r) (binSyms H (left*((1-B) i j)*right).val)
      (8*((i.val*d+j.val)*H)+96*H*H+344*H+182) := by
  intro v S ⟨matrix,delta,modulus,hl,hr,free⟩
  let bank : Fin 14 ↪ Fin T := (Fin.castLEEmb (by decide)).trans r
  have base := complementEntry_writes body bank B i j H hm tail
  have first := scaleEntry_writes body (leftWeightPorts.trans r) _ _ ((1-B) i j) left H _ hm base
  have second := scaleEntry_writes body (rightWeightPorts.trans r) _ _ (left*((1-B) i j)) right H _ hm first
  have scratch (f : Fin 13 ↪ Fin 17) (valid : ∀ k, k = 1 ∨ 4 ≤ k ∧ k < 12 →
      f k = 1 ∨ 3 ≤ f k ∧ f k ≤ 12) (k h) := free (f k) (valid k h)
  have small : ∀ k : Fin 14, k = 1 ∨ 3 ≤ k ∧ k ≤ 7 →
      (k.castLE (by decide) : Fin 17) = 1 ∨ 3 ≤ (k.castLE (by decide) : Fin 17) ∧ (k.castLE (by decide) : Fin 17) ≤ 12 := by decide
  obtain ⟨z,n,hz,hn,run⟩ := second v S
    ⟨⟨⟨matrix,delta,modulus,fun k h => free _ (small k h)⟩,hl,modulus,scratch leftWeightPorts (by decide)⟩,
      hr,modulus,scratch rightWeightPorts (by decide)⟩
  rw [mul_comm right] at run
  exact ⟨z,n,hz,by nlinarith only [hn],run⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
