module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackRadixStep

/-! Convert a little-endian radix word and restore it in reading order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Node RadixDigits
variable {T Q q : ℕ} {P U : Type}

def radixWord (r : Fin 6 ↪ Fin T) : Pr P T Q q U :=
  .seq (moveR (r 0) (r 1) id) (eachSym (r 1) (r 0)
    (onDigit (hornerStep (fun _ => r 2) (fun _ => r 3) (r 4) (r 4) (r 5)) (List.finRange q)))

theorem radixWord_exec (body : P → Pr P T Q q U) (r : Fin 6 ↪ Fin T) (xs : List (Fin q))
    (H : ℕ) (pos : 0 < H) (v : HS T Q q U) (S : Stacks T q) (digits : S.R (r 0) = xs.map digitSymbol)
    (hw : (S.R (r 4)).length = H) (zero : S.R (r 2) = binSyms H 0)
    (free : ∀ i : Fin 6, i = 1 ∨ i = 3 ∨ i = 5 → S.R (r i) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ xs.length*(7*H+q+15)+4 ∧
      Exec body (radixWord r) (mk v S) n
        (mk z {S with R := Function.update S.R (r 2) (binSyms H (value xs))}) := by
  let B := {S with R := movedR S.R (r 0) (r 1) id (S.R (r 0))}
  obtain ⟨u,hu,reverse⟩ := moveR_exec body (r 0) (r 1) (by simp) id v S
  have keep (k) (h₀ : k ≠ r 0) (h₁ : k ≠ r 1) : B.R k = S.R k := by simp [B,movedR,h₀,h₁]
  have layout : AutoLayout (fun _ : Fin 1 => r 2) (fun _ : Fin 1 => r 3) (r 4) (r 4) (r 5) := by
    constructor <;> first | exact fun _ _ _ => Subsingleton.elim _ _ | intros; simp
  obtain ⟨z,R,n,hz,hn,run,empty,rest,frame⟩ := radixDigits_exec body (src := r 1) (saved := r 0) layout
    (by simp [List.nodup_cons,r.injective.eq_iff]) xs H pos u B
    (by simp [B,movedR,digits,free 1 (by decide),List.map_reverse])
    (by rwa [keep _ (by simp) (by simp)]) ((keep _ (by simp) (by simp)).trans (free 3 (by decide)))
    ((keep _ (by simp) (by simp)).trans (free 5 (by decide))) ((keep _ (by simp) (by simp)).trans zero)
  refine ⟨z,_,hz.trans hu,?_,(Exec.seq reverse run).cast rfl ?_⟩
  · rw [digits,List.length_map]; nlinarith only [hn]
  · apply congrArg (mk z)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h₀ : k = r 0
    · subst k; simpa [B,movedR,digits] using rest
    by_cases h₁ : k = r 1
    · subst k; simpa [free 1 (by decide)] using empty
    change R k = Function.update S.R (r 2) _ k
    rw [frame k h₁ h₀]
    by_cases h₂ : k = r 2
    · subst k; simp
    simpa [Function.update_of_ne h₂] using keep k h₀ h₁

end IntegerMultBounds.MathlibTM2.Cover.Fallback
