module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDirectoryRead
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRadixWord

/-! Read a fixed-width binary coefficient directly from a physical directory. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host RadixDigits FlatCoordinateLayout
open Mult.PhaseCellToeplitz
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q : ℕ} {P U : Type}

theorem directoryBinary_exec (body : P → Pr P T Q prime U) (a : Fin 7 ↪ Fin T) (b : Fin 6 ↪ Fin T)
    (shared : a 3 = b 0) (m w j H : ℕ) (pos : 0 < H) (r c : Fin m)
    (ancestor tail : List (Fin (prime+4))) (v : HS T Q prime U) (S : Stacks T prime) :
    let offset := w * suffixFields (finProdFinEquiv (c,r))
    S.R (a 2) = ancestor ++ (LabelDirectory.digits m w j).map digitSymbol ++ tail →
    (S.R (a 0)).length = ancestor.length+offset → (S.R (a 1)).length = w →
    (∀ i : Fin 7, 3 ≤ i → S.R (a i) = []) → (S.R (b 4)).length = H →
    S.R (b 2) = binSyms H 0 → (∀ i : Fin 6, i = 1 ∨ i = 3 ∨ i = 5 → S.R (b i) = []) →
    ∃ z n, z.user = v.user ∧ n ≤ 6*(ancestor.length+offset)+w*(7*H+prime+27)+22 ∧
      Exec body (.seq (copyAfterPrefix (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6))
        (.seq (radixWord b) (bclear (b 0)))) (mk v S) n
        (mk z {S with R := Function.update S.R (b 2) (binSyms H (physicalLabel m w j r c).val)}) := by
  intro offset directory skip width scratch bits zero free
  obtain ⟨u,xs,hu,len,val,read⟩ := directoryRead_exec body a m w j r c ancestor tail v S directory skip width
    (fun i hi => scratch i (by omega))
  have empty := scratch 3 (by decide)
  rw [empty,List.append_nil,shared] at read
  rw [shared] at empty
  let B := {S with R := Function.update S.R (b 0) (xs.map digitSymbol)}
  have keep (i : Fin 6) (hi : i ≠ 0) : B.R (b i) = S.R (b i) := Function.update_of_ne (b.injective.ne hi) _ _
  obtain ⟨y,n,hy,hn,convert⟩ := radixWord_exec body b xs H pos u B (Function.update_self ..)
    (by rwa [keep 4 (by decide)]) ((keep 2 (by decide)).trans zero)
    (fun i hi => (keep i (by omega)).trans (free i hi))
  rw [val] at convert
  let F := {B with R := Function.update B.R (b 2) (binSyms H (physicalLabel m w j r c).val)}
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body (b 0) y F
  have size : (F.R (b 0)).length = w := by simp [F,B,len]
  rw [shared]
  refine ⟨z,(6*(ancestor.length+offset)+10*w+16)+(n+(2*(F.R (b 0)).length+2)),hz.trans (hy.trans hu),?_,Exec.seq read (Exec.seq convert ?_)⟩
  · rw [size]; rw [len] at hn; nlinarith only [hn]
  · simpa only [F,B,Function.update_comm (b.injective.ne (by decide : (2 : Fin 6) ≠ 0)),
      Function.update_idem,← empty,Function.update_eq_self] using clear

end IntegerMultBounds.MathlibTM2.Cover.Fallback
