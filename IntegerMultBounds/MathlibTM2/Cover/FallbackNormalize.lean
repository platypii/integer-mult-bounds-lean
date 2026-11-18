module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackConjugate
import IntegerMultBounds.MathlibTM2.Cover.FallbackRewind

/-! Normalize a generated numerator tape and release its register for the next label. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal Node
variable {T Q A m M : ℕ} [NeZero M] {P U : Type}

theorem normalizedNumerators_writes (body : P → Pr P T Q A U) (r : Fin 14 ↪ Fin T)
    (g proj : Matrix (Fin m) (Fin m) (ZMod M)) (H : ℕ) (hm : M < 2^H)
    (ok : Regs T A → Prop) (numerators : Pr P T Q A U) (cost : ℕ)
    (generate : Writes body ok (r 13) numerators (matrixWords A H (conjugateNumerator g proj)) cost) :
    Writes body (fun R => ok R ∧ R (r 13) = [] ∧ R (r 0) = binSyms H (Ring.inverse g.det).val ∧
      R (r 2) = binSyms H M ∧ ∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 → R (r k) = []) (r 3)
      (.seq numerators (.seq (sequence (fun i : Fin m => sequence (fun j : Fin m =>
        weightedEntry (i.val*m+j.val) r) (List.finRange m)) (List.finRange m)) (bclear (r 13))))
      (matrixWords A H (g*proj*g⁻¹))
      (cost + (m*(m*(8*(m*m*H)+48*H*H+166*H+88)+1)+1) + (2*(m*m*H)+2)) := by
  intro v S ⟨ready,empty,inv,modulus,free⟩
  obtain ⟨u,n,hu,hn,build⟩ := generate v S ready
  let word := matrixWords A H (conjugateNumerator g proj)
  let B := {S with R := Function.update S.R (r 13) word}
  rw [empty,List.append_nil] at build
  have keep (k : Fin 14) (hk : k ≠ 13) : B.R (r k) = S.R (r k) :=
    Function.update_of_ne (r.injective.ne hk) _ _
  obtain ⟨y,t,hy,ht,normalize⟩ := conjugateMatrix_writes body r g proj H hm [] u B
    ⟨by simp [B,word],(keep 0 (by decide)).trans inv,(keep 2 (by decide)).trans modulus,
      fun k hk => (keep k (by omega)).trans (free k hk)⟩
  let E := {B with R := Function.update B.R (r 3) (matrixWords A H (g*proj*g⁻¹) ++ B.R (r 3))}
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body (r 13) y E
  have ne := r.injective.ne (by decide : (13 : Fin 14) ≠ 3)
  have len : (E.R (r 13)).length = m*m*H := by simp [E,B,word,length_matrixWords]
  refine ⟨z,n+(t+(2*(E.R (r 13)).length+2)),hz.trans (hy.trans hu),?_,Exec.seq build (Exec.seq normalize ?_)⟩
  · rw [len]; omega
  · simpa only [E,B,Function.update_of_ne ne.symm,Function.update_comm ne.symm,
      Function.update_idem,← empty,Function.update_eq_self] using clear

end IntegerMultBounds.MathlibTM2.Cover.Fallback
