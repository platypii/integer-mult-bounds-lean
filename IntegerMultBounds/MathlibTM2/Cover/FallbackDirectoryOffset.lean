module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDirectoryBinary
public import IntegerMultBounds.MathlibTM2.Node.Params

/-! Address a physical directory coefficient from the live ancestor and digit widths. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Node FlatCoordinateLayout
open Mult.PhaseCellToeplitz
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q : ℕ} {P U : Type}

noncomputable def directoryCoefficient {m : ℕ} (a : Fin 7 ↪ Fin T) (b : Fin 6 ↪ Fin T) (prefixWidth : Fin T)
    (r c : Fin m) : Pr P T Q prime U :=
  .seq (ucopy prefixWidth (a 0) (a 6)) (.seq (umul (suffixFields (finProdFinEquiv (c,r))) (a 1) (a 0) (a 6))
    (.seq (.seq (copyAfterPrefix (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6))
      (.seq (radixWord b) (bclear (b 0)))) (uclear (a 0))))

theorem directoryCoefficient_exec (body : P → Pr P T Q prime U) (a : Fin 7 ↪ Fin T) (b : Fin 6 ↪ Fin T)
    (shared : a 3 = b 0) (apart : ∀ i, b i ≠ a 0) (prefixWidth : Fin T)
    (ports : [prefixWidth,a 0,a 6].Nodup) (m w j H : ℕ) (pos : 0 < H) (r c : Fin m)
    (ancestor tail : List (Fin (prime+4))) (v : HS T Q prime U) (S : Stacks T prime)
    (directory : S.R (a 2) = ancestor ++ (LabelDirectory.digits m w j).map RadixDigits.digitSymbol ++ tail)
    (prefixLen : (S.R prefixWidth).length = ancestor.length) (width : (S.R (a 1)).length = w)
    (scratch : ∀ i : Fin 7, i = 0 ∨ 3 ≤ i → S.R (a i) = []) (bits : (S.R (b 4)).length = H)
    (zero : S.R (b 2) = binSyms H 0) (free : ∀ i : Fin 6, i = 1 ∨ i = 3 ∨ i = 5 → S.R (b i) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ 12*ancestor.length+8*(w*suffixFields (finProdFinEquiv (c,r)))+
      w*(7*H+prime+31)+32 ∧ Exec body (directoryCoefficient a b prefixWidth r c) (mk v S) n
        (mk z {S with R := Function.update S.R (b 2) (binSyms H (physicalLabel m w j r c).val)}) := by
  regs_ne ports
  let s := suffixFields (finProdFinEquiv (c,r))
  obtain ⟨u,hu,copy⟩ := ucopy_exec body ‹prefixWidth ≠ a 0› ‹prefixWidth ≠ a 6› (by simp) v S (scratch 6 (by decide))
  have empty := scratch 0 (by decide)
  rw [prefixLen,empty,List.append_nil] at copy
  let B := {S with R := Function.update S.R (a 0) (List.replicate ancestor.length tick)}
  obtain ⟨y,hy,mul⟩ := umul_exec body s (a := a 1) (b := a 0) (t := a 6) (by simp) (by simp) (by simp) u B
    (by simpa [B] using scratch 6 (by decide))
  have bw : (B.R (a 1)).length = w := by simpa [B] using width
  rw [bw] at mul
  let C := {B with R := Function.update B.R (a 0) (List.replicate (s*w) tick ++ B.R (a 0))}
  have keep (i) (hi : i ≠ a 0) : C.R i = S.R i := by simp [C,B,Function.update_of_ne hi]
  have len : (C.R (a 0)).length = ancestor.length+w*s := by simp [C,B,Nat.mul_comm,Nat.add_comm]
  obtain ⟨z,n,hz,hn,read⟩ := directoryBinary_exec body a b shared m w j H pos r c ancestor tail y C
    ((keep _ (by simp)).trans directory) len (by rwa [keep _ (by simp)])
    (fun i hi => (keep _ (a.injective.ne (by omega))).trans (scratch i (Or.inr hi)))
    (by rwa [keep _ (apart 4)]) ((keep _ (apart 2)).trans zero) (fun i hi => (keep _ (apart i)).trans (free i hi))
  let F := {C with R := Function.update C.R (b 2) (binSyms H (physicalLabel m w j r c).val)}
  obtain ⟨t,ht,clear⟩ := uclear_exec body (a 0) z F
  have fl : (F.R (a 0)).length = ancestor.length+w*s := by simpa [F,Function.update_of_ne (apart 2).symm] using len
  refine ⟨t,(4*ancestor.length+4)+((4*w+4)+(n+(2*(F.R (a 0)).length+2))),ht.trans (hz.trans (hy.trans hu)),?_,Exec.seq copy (Exec.seq mul (Exec.seq read ?_))⟩
  · rw [fl]; dsimp [s] at *; nlinarith only [hn]
  · simpa only [F,C,B,Function.update_comm (apart 2),Function.update_idem,← empty,Function.update_eq_self] using clear

end IntegerMultBounds.MathlibTM2.Cover.Fallback
