module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepCounterField
public import IntegerMultBounds.MathlibTM2.Cover.FallbackDirectoryMatrix

/-! Write the two destination rows in the coordinate order used by a sweep. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks.Shared50ModularControl
open Cover.Fallback Stack Host Node FlatCoordinateLayout RadixDigits
open Cover.LabelTraversal
variable {T Q d : ℕ} {P U : Type}
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def sweepCounterRows (a : Fin 7 ↪ Fin T) (b : Fin 6 ↪ Fin T)
    (zeros out : Fin T) (axis : Fin 2 → Fin 64 → Fin d) : Pr P T Q prime U :=
  sequence (fun r => sequence (fun c => .seq (bcopy zeros (b 2) (b 3) (b 5))
    (.seq (sweepCoordinate a b (axis r c)) (moveRightOrdered (b 2) (b 3) out)))
    (List.finRange 64)) (List.finRange 2)

theorem sweepCounterRows_writes (body : P → Pr P T Q prime U) (a : Fin 7 ↪ Fin T) (b : Fin 6 ↪ Fin T)
    (shared : a 3 = b 0) (sep : ∀ i j, a i ≠ b j ∨ i = 3 ∧ j = 0)
    (zeros out : Fin T) (external : zeros ≠ out) (aOut : ∀ i, a i ≠ out) (bOut : ∀ i, b i ≠ out)
    (zeroPort : ∀ i, zeros ≠ b i) (axis : Fin 2 → Fin 64 → Fin d)
    (w H : ℕ) (pos : 0 < H) (dest : Fin ((prime^w)^d)) (ds : List (Fin prime))
    (len : ds.length = w*d) (number : value ds = dest.val) (tail : List (Fin (prime+4))) :
    let ok := fun (R : Regs T prime) => R (a 2) = ds.map digitSymbol ++ tail ∧ (R (a 1)).length = w ∧
      (∀ i : Fin 7, i = 0 ∨ 3 ≤ i → R (a i) = []) ∧ (R (b 4)).length = H ∧
      (∀ i : Fin 6, i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 → R (b i) = []) ∧ R zeros = binSyms H 0
    let cost := 8*(w*d)+w*(7*H+prime+31)+10*H+38
    Writes body ok out (sweepCounterRows a b zeros out axis)
      (matrixWords prime H (fun r c => coordinates dest (axis r c))) (2*(64*cost+1)+1) := by
  intro ok cost
  have stable (R) (xs) (h : ok R) : ok (Function.update R out xs) := by
    simpa only [ok,Function.update_of_ne (aOut _),Function.update_of_ne (bOut _),
      Function.update_of_ne external] using h
  have entry (r c) : Writes body ok out (.seq (bcopy zeros (b 2) (b 3) (b 5))
      (.seq (sweepCoordinate a b (axis r c)) (moveRightOrdered (b 2) (b 3) out)))
      (binSyms H (coordinates dest (axis r c)).val) cost := by
    intro v S ⟨source,width,scratch,bits,free,zero⟩
    have acc (i) : a i ≠ b 2 := (sep i 2).resolve_right (by decide +revert)
    have apart (i) : b i ≠ a 0 := ((sep 0 i).resolve_right (by decide +revert)).symm
    obtain ⟨u,hu,copy⟩ := bcopy_exec body (a := zeros) (c := b 2) (t₁ := b 3) (t₂ := b 5)
      (by simp [zeroPort,b.injective.eq_iff]) v S (free 3 (by decide)) (free 5 (by decide))
    have empty := free 2 (by decide)
    rw [zero,length_binSyms,empty,List.append_nil] at copy
    let B := {S with R := Function.update S.R (b 2) (binSyms H 0)}
    have keep (k) (hk : k ≠ b 2) : B.R k = S.R k := Function.update_of_ne hk _ _
    obtain ⟨y,n,hy,hn,read⟩ := sweepCoordinate_exec body a b shared apart dest (axis r c) ds len number tail H pos u B
      ((keep _ (acc 2)).trans source) (by rwa [keep _ (acc 1)])
      (fun i hi => (keep _ (acc i)).trans (scratch i hi)) (by rwa [keep _ (by simp)]) (Function.update_self ..)
      (fun i hi => (keep _ (b.injective.ne (by omega))).trans (free i (by omega)))
    let word := binSyms (A := prime) H (coordinates dest (axis r c)).val
    let F := {B with R := Function.update B.R (b 2) word}
    obtain ⟨z,hz,move⟩ := moveRightOrdered_exec (body := body) (b 2) (b 3) out (by simp) (bOut 2) (bOut 3) y F
      (by simpa [F,B] using free 3 (by decide))
    simp only [F,B,Function.update_self,Function.update_idem,Function.update_of_ne (bOut 2).symm,← empty,Function.update_eq_self] at move
    simp only [B,Function.update_idem] at read
    refine ⟨z,_,hz.trans (hy.trans hu),?_,Exec.seq copy (Exec.seq read move)⟩
    · simp only [word,length_binSyms]
      have bound : suffixFields (axis r c) ≤ d := Nat.sub_le .. |>.trans (Nat.sub_le ..)
      dsimp [cost]
      linarith [Nat.mul_le_mul_left w bound]
  exact matrixWords_writes body out ok stable _ _ H cost entry

end IntegerMultBounds.MathlibTM2.M6.BitNode
