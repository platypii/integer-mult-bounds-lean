module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDirectoryBinary
public import IntegerMultBounds.Machine.PrefixAddressData
public import IntegerMultBounds.MathlibTM2.Node.Params

/-! Read a destination coordinate from the live little-endian radix counter. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks.Shared50ModularControl
open Cover.Fallback Stack Host RadixDigits FlatCoordinateLayout Mult.PhaseCellToeplitz
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem sweepCounterField_read {T Q d w : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 7 ↪ Fin T) (dest : Fin ((prime^w)^d)) (k : Fin d) (ds : List (Fin prime))
    (len : ds.length = w*d) (number : value ds = dest.val) (tail : List (Fin (prime+4)))
    (v : HS T Q prime U) (S : Stacks T prime) (source : S.R (r 2) = ds.map digitSymbol ++ tail)
    (skip : (S.R (r 0)).length = w*suffixFields k) (width : (S.R (r 1)).length = w)
    (free : ∀ i : Fin 7, 4 ≤ i → S.R (r i) = []) :
    ∃ z xs, z.user = v.user ∧ xs.length = w ∧ value xs = (coordinates dest k).val ∧
      Exec body (copyAfterPrefix (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6))
        (mk v S) (6*(w*suffixFields k)+10*w+16)
        (mk z {S with R := Function.update S.R (r 3) (xs.map digitSymbol ++ S.R (r 3))}) := by
  let offset := w*suffixFields k
  let lo := ds.take offset
  let xs := (ds.drop offset).take w
  let hi := (ds.drop offset).drop w
  have limit : offset+w ≤ ds.length := by
    rw [len,← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ (by unfold suffixFields; omega)
  have low : lo.length = offset := by simp [lo]; omega
  have field : xs.length = w := by simp [xs]; omega
  have parts : lo ++ xs ++ hi = ds := by simp [lo,xs,hi,List.append_assoc]
  have val := PrefixAddressData.extract_word prime_prime.two_le lo xs hi
  rw [parts,number,low,field] at val
  have coord := coordinate_value (coordinates dest) k
  rw [rank_coordinates] at coord
  rw [show prime^offset = (prime^w)^suffixFields k from pow_mul _ _ _] at val
  obtain ⟨z,user,copy⟩ := copyAfterPrefix_exec (body := body)
    (by simp [List.nodup_cons,r.injective.eq_iff] : [r 0,r 1,r 2,r 3,r 4,r 5,r 6].Nodup)
    v S (lo.map digitSymbol) (xs.map digitSymbol) (hi.map digitSymbol ++ tail)
    (by rw [source,← parts]; simp [List.append_assoc])
    (by simpa [low] using skip) (by simpa [field] using width)
    (free 4 (by decide)) (free 5 (by decide)) (free 6 (by decide))
  exact ⟨z,xs,user,field,val.symm.trans coord,by simpa [low,field,offset] using copy⟩

theorem sweepCounterBinary_exec {T Q d w : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (a : Fin 7 ↪ Fin T) (b : Fin 6 ↪ Fin T) (shared : a 3 = b 0)
    (dest : Fin ((prime^w)^d)) (k : Fin d) (ds : List (Fin prime))
    (len : ds.length = w*d) (number : value ds = dest.val) (tail : List (Fin (prime+4)))
    (H : ℕ) (pos : 0 < H) (v : HS T Q prime U) (S : Stacks T prime)
    (source : S.R (a 2) = ds.map digitSymbol ++ tail)
    (skip : (S.R (a 0)).length = w*suffixFields k) (width : (S.R (a 1)).length = w)
    (scratch : ∀ i : Fin 7, 3 ≤ i → S.R (a i) = []) (bits : (S.R (b 4)).length = H)
    (zero : S.R (b 2) = binSyms H 0) (free : ∀ i : Fin 6, i = 1 ∨ i = 3 ∨ i = 5 → S.R (b i) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ 6*(w*suffixFields k)+w*(7*H+prime+27)+22 ∧
      Exec body (.seq (copyAfterPrefix (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6))
        (.seq (radixWord b) (bclear (b 0)))) (mk v S) n
        (mk z {S with R := Function.update S.R (b 2) (binSyms H (coordinates dest k).val)}) := by
  obtain ⟨u,xs,hu,size,val,read⟩ := sweepCounterField_read body a dest k ds len number tail v S
    source skip width (fun i hi => scratch i (by omega))
  have empty := scratch 3 (by decide)
  rw [empty,List.append_nil,shared] at read
  rw [shared] at empty
  obtain ⟨z,n,hz,hn,convert⟩ := radixFieldBinary_exec body b xs H pos u S empty bits zero free
  rw [val] at convert
  rw [shared]
  refine ⟨z,_,hz.trans hu,?_,Exec.seq read convert⟩
  rw [size] at hn
  nlinarith only [hn]

open Node

noncomputable def sweepCoordinate {T Q d : ℕ} {P U : Type}
    (a : Fin 7 ↪ Fin T) (b : Fin 6 ↪ Fin T) (k : Fin d) : Pr P T Q prime U :=
  .seq (umul (suffixFields k) (a 1) (a 0) (a 6))
    (.seq (.seq (copyAfterPrefix (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6))
      (.seq (radixWord b) (bclear (b 0)))) (uclear (a 0)))

theorem sweepCoordinate_exec {T Q d w : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (a : Fin 7 ↪ Fin T) (b : Fin 6 ↪ Fin T) (shared : a 3 = b 0) (apart : ∀ i, b i ≠ a 0)
    (dest : Fin ((prime^w)^d)) (k : Fin d) (ds : List (Fin prime))
    (len : ds.length = w*d) (number : value ds = dest.val) (tail : List (Fin (prime+4)))
    (H : ℕ) (pos : 0 < H) (v : HS T Q prime U) (S : Stacks T prime)
    (source : S.R (a 2) = ds.map digitSymbol ++ tail) (width : (S.R (a 1)).length = w)
    (scratch : ∀ i : Fin 7, i = 0 ∨ 3 ≤ i → S.R (a i) = []) (bits : (S.R (b 4)).length = H)
    (zero : S.R (b 2) = binSyms H 0) (free : ∀ i : Fin 6, i = 1 ∨ i = 3 ∨ i = 5 → S.R (b i) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ 8*(w*suffixFields k)+w*(7*H+prime+31)+28 ∧
      Exec body (sweepCoordinate a b k) (mk v S) n
        (mk z {S with R := Function.update S.R (b 2) (binSyms H (coordinates dest k).val)}) := by
  have empty := scratch 0 (by decide)
  obtain ⟨u,hu,mul⟩ := umul_exec body (suffixFields k) (a := a 1) (b := a 0) (t := a 6)
    (by simp) (by simp) (by simp) v S (scratch 6 (by decide))
  rw [width,empty,List.append_nil] at mul
  let B := {S with R := Function.update S.R (a 0) (List.replicate (suffixFields k*w) tick)}
  have keep (i) (hi : i ≠ a 0) : B.R i = S.R i := Function.update_of_ne hi _ _
  have offset : (B.R (a 0)).length = w*suffixFields k := by simp [B,Nat.mul_comm]
  obtain ⟨y,n,hy,hn,read⟩ := sweepCounterBinary_exec body a b shared dest k ds len number tail H pos u B
    ((keep _ (by simp)).trans source) offset (by rwa [keep _ (by simp)])
    (fun i hi => (keep _ (a.injective.ne (by omega))).trans (scratch i (Or.inr hi)))
    (by rwa [keep _ (apart 4)]) ((keep _ (apart 2)).trans zero) (fun i hi => (keep _ (apart i)).trans (free i hi))
  let F := {B with R := Function.update B.R (b 2) (binSyms H (coordinates dest k).val)}
  obtain ⟨z,hz,clear⟩ := uclear_exec body (a 0) y F
  have size : (F.R (a 0)).length = w*suffixFields k := by simpa [F,Function.update_of_ne (apart 2).symm] using offset
  refine ⟨z,4*w+4+(n+(2*(F.R (a 0)).length+2)),hz.trans (hy.trans hu),?_,Exec.seq mul (Exec.seq read ?_)⟩
  · show 4*w+4+(n+(2*(F.R (a 0)).length+2)) ≤ _
    rw [size]; nlinarith only [hn]
  · simpa only [F,B,Function.update_comm (apart 2),Function.update_idem,← empty,Function.update_eq_self] using clear

end IntegerMultBounds.MathlibTM2.M6.BitNode
