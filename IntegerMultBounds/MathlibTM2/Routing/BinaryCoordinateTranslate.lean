module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Translate a live binary coordinate from one interval base to another.
Subtraction, addition and temporary erasure are executed and fully charged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

/-- Install a computed word without reversing its bit order, then erase the
temporary output. Shared by scalar arithmetic and table lookup. -/
def coordinateReplaceProgram (src dst t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (bclear dst) (.seq (bcopy src dst t₁ t₂) (bclear src))

theorem coordinateReplace_exec (body : P → Pr P T Q A U)
    (src dst t₁ t₂ : Fin T) (hdist : [src, dst, t₁, t₂].Nodup)
    (L : ℕ) (word : List (Fin (A + 4))) (hword : word.length = L)
    (v : HS T Q A U) (S : Stacks T A)
    (hdst : (S.R dst).length = L) (hsrc : S.R src = [])
    (ht₁ : S.R t₁ = []) (ht₂ : S.R t₂ = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (coordinateReplaceProgram src dst t₁ t₂)
        (mk v { S with R := Function.update S.R src word }) (10 * L + 10)
        (mk v' { S with R := Function.update S.R dst word }) := by
  have hne : src ≠ dst ∧ src ≠ t₁ ∧ src ≠ t₂ ∧ dst ≠ t₁ ∧ dst ≠ t₂ := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, not_false_eq_true] at hdist
    exact ⟨hdist.1.1, hdist.1.2.1, hdist.1.2.2, hdist.2.1.1, hdist.2.1.2⟩
  let G : Stacks T A := { S with R := Function.update S.R src word }
  obtain ⟨v₁, hu₁, _, he₁⟩ := bclear_exec body dst v G
  let H : Stacks T A := { G with R := Function.update G.R dst [] }
  obtain ⟨v₂, hu₂, he₂⟩ := bcopy_exec body
    (a := src) (c := dst) (t₁ := t₁) (t₂ := t₂) hdist v₁ H
    (by simp [H, G, Ne.symm hne.2.1, Ne.symm hne.2.2.2.1, ht₁])
    (by simp [H, G, Ne.symm hne.2.2.1, Ne.symm hne.2.2.2.2, ht₂])
  have hs : H.R src = word := by simp [H, G, hne.1]
  rw [hs, show H.R dst = [] by simp [H], List.append_nil, hword] at he₂
  let J : Stacks T A := { H with R := Function.update H.R dst word }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body src v₂ J
  have hl : (G.R dst).length = L := by simp [G, Ne.symm hne.1, hdst]
  have hj : (J.R src).length = L := by simp [J, H, G, hne.1, hword]
  have hf : Function.update J.R src [] = Function.update S.R dst word := by
    funext j
    by_cases hs : j = src
    · subst j; simp [hne.1, hsrc]
    by_cases hd : j = dst
    · subst j; simp [J, hs]
    · simp [J, H, G, hs, hd]
  rw [hl] at he₁
  rw [hj, hf] at he₃
  exact ⟨v₃, hu₃.trans (hu₂.trans hu₁),
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) (by omega) rfl⟩

def binaryCoordinateTranslateProgram (rg : Fin 9 → Fin T) : Pr P T Q A U :=
  .seq (bsub (rg 0) (rg 1) (rg 3) (rg 5) (rg 6) (rg 7) (rg 8))
    (.seq (badd (rg 3) (rg 2) (rg 4) (rg 5) (rg 6) (rg 7) (rg 8)) (bclear (rg 3)))

theorem binaryCoordinateTranslate_exec (body : P → Pr P T Q A U)
    (rg : Fin 9 → Fin T) (hrg : Function.Injective rg) (L q base target : ℕ)
    (hq : q < 2 ^ L) (hbase : base ≤ q) (hresult : q - base + target < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hqInput : S.R (rg 0) = binSyms L q) (hbaseInput : S.R (rg 1) = binSyms L base)
    (htargetInput : S.R (rg 2) = binSyms L target)
    (hblank : ∀ j : Fin 9, j = 3 ∨ j = 5 ∨ j = 6 ∨ j = 7 → S.R (rg j) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (binaryCoordinateTranslateProgram rg) (mk v S) (18 * L + 18)
        (mk v' { S with R := Function.update S.R (rg 4) (binSyms L (q - base + target) ++ S.R (rg 4)) }) := by
  obtain ⟨v₁, hu₁, _, _, he₁⟩ := bsub_exec body
    (a := rg 0) (b := rg 1) (c := rg 3) (tx := rg 5) (ty := rg 6) (tz := rg 7) (cy := rg 8)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    hq (by omega : base < 2 ^ L) v S hqInput hbaseInput
    (hblank 5 (by simp)) (hblank 6 (by simp)) (hblank 7 (by simp))
  have hsub : (q + 2 ^ L - base) % 2 ^ L = q - base := by
    rw [show q + 2 ^ L - base = (q - base) + 2 ^ L by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hsub, hblank 3 (by simp), List.append_nil] at he₁
  let G : Stacks T A := { S with R := Function.update S.R (rg 3) (binSyms L (q - base)) }
  obtain ⟨v₂, hu₂, _, _, he₂⟩ := badd_exec body
    (a := rg 3) (b := rg 2) (c := rg 4) (tx := rg 5) (ty := rg 6) (tz := rg 7) (cy := rg 8)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    (by omega : q - base < 2 ^ L) (by omega : target < 2 ^ L) v₁ G (by simp [G])
    (by simpa [G, hrg.eq_iff] using htargetInput)
    (by simpa [G, hrg.eq_iff] using hblank 5 (by simp))
    (by simpa [G, hrg.eq_iff] using hblank 6 (by simp))
    (by simpa [G, hrg.eq_iff] using hblank 7 (by simp))
  rw [Nat.mod_eq_of_lt hresult] at he₂
  have hout : G.R (rg 4) = S.R (rg 4) := by simp [G, hrg.eq_iff]
  rw [hout] at he₂
  let H : Stacks T A := { G with R := Function.update G.R (rg 4) (binSyms L (q - base + target) ++ S.R (rg 4)) }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (rg 3) v₂ H
  have hlen : (H.R (rg 3)).length = L := by simp [H, G, hrg.eq_iff]
  have hf : Function.update H.R (rg 3) [] =
      Function.update S.R (rg 4) (binSyms L (q - base + target) ++ S.R (rg 4)) := by
    funext j
    by_cases h3 : j = rg 3
    · subst j; simp [hrg.eq_iff, hblank 3 (by simp)]
    by_cases h4 : j = rg 4
    · subst j; simp [H, G, h3]
    · simp [H, G, h3, h4]
  rw [hlen, hf] at he₃
  exact ⟨v₃, hu₃.trans (hu₂.trans hu₁), Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) (by omega) rfl⟩

def binaryCoordinateTranslateInPlaceProgram (rg : Fin 9 → Fin T) : Pr P T Q A U :=
  .seq (binaryCoordinateTranslateProgram rg)
    (coordinateReplaceProgram (rg 4) (rg 0) (rg 5) (rg 6))

theorem binaryCoordinateTranslateInPlace_exec (body : P → Pr P T Q A U)
    (rg : Fin 9 → Fin T) (hrg : Function.Injective rg) (L q base target : ℕ)
    (hq : q < 2 ^ L) (hbase : base ≤ q) (hresult : q - base + target < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hqInput : S.R (rg 0) = binSyms L q) (hbaseInput : S.R (rg 1) = binSyms L base)
    (htargetInput : S.R (rg 2) = binSyms L target)
    (hblank : ∀ j : Fin 9, j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 → S.R (rg j) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (binaryCoordinateTranslateInPlaceProgram rg) (mk v S) (28 * L + 28)
        (mk v' { S with R := Function.update S.R (rg 0) (binSyms L (q - base + target)) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := binaryCoordinateTranslate_exec body rg hrg L q base target
    hq hbase hresult v S hqInput hbaseInput htargetInput
    (by intro j hj; rcases hj with rfl | rfl | rfl | rfl <;> exact hblank _ (by simp))
  rw [hblank 4 (by simp), List.append_nil] at he₁
  obtain ⟨v₂, hu₂, he₂⟩ := coordinateReplace_exec body (rg 4) (rg 0) (rg 5) (rg 6)
    (by simp [List.nodup_cons, hrg.eq_iff]) L (binSyms L (q - base + target))
    (length_binSyms L _) v₁ S (by rw [hqInput]; exact length_binSyms L _)
    (hblank 4 (by simp)) (hblank 5 (by simp)) (hblank 6 (by simp))
  exact ⟨v₂, hu₂.trans hu₁, Exec.cast (Exec.seq he₁ he₂) (by omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
