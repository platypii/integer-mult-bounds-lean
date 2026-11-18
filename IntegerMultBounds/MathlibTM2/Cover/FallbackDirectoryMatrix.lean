module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDirectoryOffset
public import IntegerMultBounds.MathlibTM2.Cover.FallbackProjectorEntries
public import IntegerMultBounds.MathlibTM2.Host.OrderedMove

/-! Pack a directory label in the row-major binary format used by conjugation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Node LabelTraversal FlatCoordinateLayout
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable {T Q : ℕ} {P U : Type}
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def directoryMatrix (m : ℕ) (a : Fin 7 ↪ Fin T) (b : Fin 6 ↪ Fin T)
    (prefixWidth zeros out : Fin T) : Pr P T Q prime U :=
  sequence (fun r => sequence (fun c => .seq (bcopy zeros (b 2) (b 3) (b 5))
    (.seq (directoryCoefficient a b prefixWidth r c) (moveRightOrdered (b 2) (b 3) out)))
    (List.finRange m)) (List.finRange m)

theorem directoryMatrix_writes (body : P → Pr P T Q prime U) (a : Fin 7 ↪ Fin T) (b : Fin 6 ↪ Fin T)
    (shared : a 3 = b 0) (sep : ∀ i j, a i ≠ b j ∨ i = 3 ∧ j = 0)
    (prefixWidth zeros out : Fin T) (ports : [prefixWidth,a 0,a 6].Nodup)
    (external : [prefixWidth,zeros,out].Nodup) (prefixAcc : prefixWidth ≠ b 2)
    (aOut : ∀ i, a i ≠ out) (bOut : ∀ i, b i ≠ out) (zeroPort : ∀ i, zeros ≠ b i)
    (m w j H : ℕ) (pos : 0 < H) (ancestor tail : List (Fin (prime+4))) :
    Writes body (fun R => R (a 2) = ancestor ++ (LabelDirectory.digits m w j).map RadixDigits.digitSymbol ++ tail ∧
      (R prefixWidth).length = ancestor.length ∧ (R (a 1)).length = w ∧
      (∀ i : Fin 7, i = 0 ∨ 3 ≤ i → R (a i) = []) ∧ (R (b 4)).length = H ∧
      (∀ i : Fin 6, i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 → R (b i) = []) ∧ R zeros = binSyms H 0)
      out (directoryMatrix m a b prefixWidth zeros out) (matrixWords prime H (physicalLabel m w j))
      (m*(m*(12*ancestor.length+8*(w*(m*m))+w*(7*H+prime+31)+10*H+42)+1)+1) := by
  regs_ne external
  apply matrixWords_writes
  · intro R xs h
    simpa only [Function.update_of_ne (aOut _),Function.update_of_ne (bOut _),
      Function.update_of_ne ‹prefixWidth ≠ out›,Function.update_of_ne ‹zeros ≠ out›] using h
  · intro r c v S ⟨directory,prefixLen,width,scratch,bits,free,zero⟩
    have acc (i) : a i ≠ b 2 := (sep i 2).resolve_right (by decide +revert)
    have apart (i) : b i ≠ a 0 := ((sep 0 i).resolve_right (by decide +revert)).symm
    obtain ⟨u,hu,copy⟩ := bcopy_exec body (a := zeros) (c := b 2) (t₁ := b 3) (t₂ := b 5)
      (by simp [zeroPort,b.injective.eq_iff]) v S (free 3 (by decide)) (free 5 (by decide))
    have empty := free 2 (by decide)
    rw [zero,length_binSyms,empty,List.append_nil] at copy
    let B := {S with R := Function.update S.R (b 2) (binSyms H 0)}
    have keep (k) (hk : k ≠ b 2) : B.R k = S.R k := Function.update_of_ne hk _ _
    obtain ⟨y,n,hy,hn,read⟩ := directoryCoefficient_exec body a b shared apart prefixWidth ports m w j H pos r c
      ancestor tail u B ((keep _ (acc 2)).trans directory) (by rwa [keep _ prefixAcc]) (by rwa [keep _ (acc 1)])
      (fun i hi => (keep _ (acc i)).trans (scratch i hi)) (by rwa [keep _ (by simp)]) (Function.update_self ..)
      (fun i hi => (keep _ (b.injective.ne (by omega))).trans (free i (by omega)))
    let word := binSyms (A := prime) H (physicalLabel m w j r c).val
    let F := {B with R := Function.update B.R (b 2) word}
    obtain ⟨z,hz,move⟩ := moveRightOrdered_exec (body := body) (b 2) (b 3) out (by simp) (bOut 2) (bOut 3) y F
      (by simpa [F,B] using free 3 (by decide))
    simp only [F,B,Function.update_self,Function.update_idem,Function.update_of_ne (bOut 2).symm,← empty,Function.update_eq_self] at move
    simp only [B,Function.update_idem] at read
    refine ⟨z,_,hz.trans (hy.trans hu),?_,Exec.seq copy (Exec.seq read move)⟩
    · simp only [word,length_binSyms]
      have bound : suffixFields (finProdFinEquiv (c,r)) ≤ m*m := Nat.sub_le .. |>.trans (Nat.sub_le ..)
      linarith [Nat.mul_le_mul_left w bound]
end IntegerMultBounds.MathlibTM2.Cover.Fallback
