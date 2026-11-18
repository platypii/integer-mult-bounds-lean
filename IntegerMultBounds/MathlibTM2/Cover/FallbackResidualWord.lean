module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackProjectorWriter
import IntegerMultBounds.MathlibTM2.Cover.FallbackRewind

/-! Generate the conjugated projector, write its weighted residual, and release the intermediate tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal Node
variable {T Q A m n M : ℕ} [NeZero M] {P U : Type}

theorem residualWord_writes (body : P → Pr P T Q A U) (ports : Fin m → Fin m → Fin 17 ↪ Fin T)
    (src out : Fin T) (distinct : src ≠ out) (input : ∀ i j, ports i j 13 = src)
    (output : ∀ i j, ports i j 16 = out) (e : (Fin m ⊕ Fin m) ≃ Fin n)
    (proj g : Matrix (Fin m) (Fin m) (ZMod M)) (α α' : Fin m → ZMod M) (H : ℕ) (hm : M < 2^H)
    (ok : Regs T A → Prop) (generate : Pr P T Q A U) (cost : ℕ)
    (writer : Writes body ok src generate (matrixWords A H (g*proj*g⁻¹)) cost) :
    Writes body (fun R => ok R ∧ R src = [] ∧ ∀ i j, let r := ports i j
      R (r 0) = binSyms H ((1 : Matrix (Fin m) (Fin m) (ZMod M)) i j).val ∧
      R (r 2) = binSyms H M ∧ R (r 14) = binSyms H (α i).val ∧ R (r 15) = binSyms H (α' j).val ∧
      ∀ k : Fin 17, k = 1 ∨ 3 ≤ k ∧ k ≤ 12 → R (r k) = []) out
      (.seq generate (.seq (sequence (fun i => sequence (fun j => blockEntry ports (e.symm i) (e.symm j))
        (List.finRange n)) (List.finRange n)) (bclear src)))
      (matrixWords A H (projectorResidual e proj α α' g))
      (cost+(n*(n*(8*(m*m*H)+96*H*H+344*H+182)+1)+1)+(2*(m*m*H)+2)) := by
  intro v S ⟨ready,empty,weights⟩
  obtain ⟨u,l,hu,hl,load⟩ := writer v S ready
  rw [empty,List.append_nil] at load
  let B := {S with R := Function.update S.R src (matrixWords A H (g*proj*g⁻¹))}
  have keep (i j) (k : Fin 17) (hk : k ≠ 13) : B.R (ports i j k) = S.R (ports i j k) := by
    apply Function.update_of_ne
    rw [← input i j]; exact (ports i j).injective.ne hk
  obtain ⟨y,t,hy,ht,emit⟩ := projectorWriter_exec body ports out output e proj g α α' H hm [] u B (by
    intro i j
    obtain ⟨oneWord,modulus,row,col,free⟩ := weights i j
    exact ⟨by simp [B,input],(keep i j 0 (by decide)).trans oneWord,(keep i j 2 (by decide)).trans modulus,
      (keep i j 14 (by decide)).trans row,(keep i j 15 (by decide)).trans col,
      fun k hk => (keep i j k (by omega)).trans (free k hk)⟩)
  let F := {B with R := Function.update B.R out (matrixWords A H (projectorResidual e proj α α' g) ++ B.R out)}
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body src y F
  have len : (F.R src).length = m*m*H := by simp only [F,B,Function.update_of_ne distinct,Function.update_self,length_matrixWords]
  refine ⟨z,l+(t+(2*(F.R src).length+2)),hz.trans (hy.trans hu),?_,Exec.seq load (Exec.seq emit ?_)⟩
  · rw [len,Nat.add_assoc]; exact Nat.add_le_add hl (Nat.add_le_add_right ht _)
  · simpa only [F,B,Function.update_of_ne distinct.symm,Function.update_comm distinct.symm,
      Function.update_idem,← empty,Function.update_eq_self] using clear

end IntegerMultBounds.MathlibTM2.Cover.Fallback
