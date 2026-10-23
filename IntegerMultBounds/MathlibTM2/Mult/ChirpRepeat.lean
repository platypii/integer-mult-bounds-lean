module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! # Repeat a source stream with a preserved unary count

Whole-period copies avoid rescanning a source for individual cyclic entries. The source,
count and workspace are restored; a later prefix copy removes the final overshoot.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def repeatStream {α : Type} (n : ℕ) (xs : List α) : List α := (List.replicate n xs).flatten

@[simp] theorem repeatStream_zero {α : Type} (xs : List α) : repeatStream 0 xs = [] := rfl

theorem repeatStream_succ {α : Type} (n : ℕ) (xs : List α) :
    repeatStream (n + 1) xs = repeatStream n xs ++ xs := by
  simp [repeatStream, List.replicate_succ', List.flatten_append]

@[simp] theorem length_repeatStream {α : Type} (n : ℕ) (xs : List α) :
    (repeatStream n xs).length = n * xs.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [repeatStream_succ, List.length_append, ih]; ring

def repeatCopy (count saved src dst tmp : Fin T) : Pr P T Q A U :=
  scanP count saved (copyR src dst tmp id)

/-- Copy whole periods into a reversed accumulator, preserving the source and count. -/
theorem repeatCopy_exec {count saved src dst tmp : Fin T}
    (hreg : [count, saved, src, dst, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (S.R count).length * (4 * (S.R src).length + 9) + 4 ∧
      Exec body (repeatCopy count saved src dst tmp) (mk v S) n
        (mk v' { S with R := (Function.update S.R dst
          ((repeatStream (S.R count).length (S.R src)).reverse ++ S.R dst)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  let Ψ : ℕ → Regs T A := fun j => Function.update S.R dst
    ((repeatStream j (S.R src)).reverse ++ S.R dst)
  have hp : IterSpec body (copyR src dst tmp id) count saved Ψ
      (fun _ => 4 * (S.R src).length + 4) (S.R count).length := by
    intro j _ v₀ S₀ hS
    have hx : S₀.R src = S.R src := by
      rw [hS src ‹count ≠ src›.symm ‹saved ≠ src›.symm]
      simp [Ψ, ‹src ≠ dst›]
    have hd : S₀.R dst = (repeatStream j (S.R src)).reverse ++ S.R dst := by
      simpa [Ψ] using hS dst ‹count ≠ dst›.symm ‹saved ≠ dst›.symm
    have ht : S₀.R tmp = [] := by
      rw [hS tmp ‹count ≠ tmp›.symm ‹saved ≠ tmp›.symm]
      simp [Ψ, ‹dst ≠ tmp›.symm, htmp]
    obtain ⟨v₁, hu₁, he₁⟩ := copyR_exec body src dst tmp ‹src ≠ dst› ‹src ≠ tmp› ‹dst ≠ tmp› id v₀ S₀ ht
    refine ⟨v₁, Function.update S₀.R dst (((S₀.R src).map id).reverse ++ S₀.R dst),
      4 * (S₀.R src).length + 4, hu₁, by rw [hx], he₁,
      by simp [‹count ≠ dst›], by simp [‹saved ≠ dst›], ?_⟩
    intro k hkc hks
    by_cases hk : k = dst
    · subst k
      simp only [Function.update_self, List.map_id, hx, hd, Ψ, repeatStream_succ,
        List.reverse_append, List.append_assoc]
    · rw [Function.update_of_ne hk, hS k hkc hks]
      simp [Ψ, hk]
  obtain ⟨v', R', n, hu, hn, he, hc, hs, hf⟩ := scanP_exec body ‹count ≠ saved› hp 0 v S (by simp)
    (fun k _ _ => by simp [Ψ])
  refine ⟨v', n, hu, ?_, he.cast rfl ?_⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, hsaved,
      List.length_nil, Nat.mul_zero, Nat.add_zero] at hn
    nlinarith
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    change R' k = Function.update S.R dst ((repeatStream (S.R count).length (S.R src)).reverse ++ S.R dst) k
    by_cases hkc : k = count
    · subst k; simp [hc, hsaved, ‹count ≠ dst›]
    by_cases hks : k = saved
    · subst k; simp [hs, hsaved, ‹saved ≠ dst›]
    · rw [hf k hkc hks]
      simp [Ψ]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
