module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalWord
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Copy, append one high zero, increment and normalize. The extra bit makes
successor generation valid even when every original input bit is one. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binaryCanonicalSuccessorProgram (rg : Fin 6 → Fin T) : Pr P T Q A U :=
  .seq (bcopy (rg 0) (rg 2) (rg 3) (rg 4))
    (.seq (bpad (rg 2) (rg 1) (rg 3) (rg 4))
      (.seq (countIter (rg 2) (rg 3) (rg 5)) (binaryCanonicalProgram (rg 2) (rg 3))))

theorem binaryCanonicalSuccessor_exec (body : P → Pr P T Q A U)
    (rg : Fin 6 → Fin T) (hrg : Function.Injective rg) (L n : ℕ) (hn : n < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R (rg 0) = binSyms L n)
    (hpad : (S.R (rg 1)).length = 1)
    (hblank : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → i ≠ 5 → S.R (rg i) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (binaryCanonicalSuccessorProgram rg) (mk v S) (18*L+39)
        (mk v' { S with R := Function.update S.R (rg 2) (binSyms (Nat.clog 2 (n+1+1)) (n+1)) }) := by
  obtain ⟨v₁,hu₁,he₁⟩ := bcopy_exec body
    (a := rg 0) (c := rg 2) (t₁ := rg 3) (t₂ := rg 4)
    (by simp [List.nodup_cons,hrg.eq_iff]) v S
    (hblank 3 (by decide) (by decide) (by decide)) (hblank 4 (by decide) (by decide) (by decide))
  rw [hsrc,hblank 2 (by decide) (by decide) (by decide),List.append_nil,length_binSyms] at he₁
  let C : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms L n) }
  obtain ⟨v₂,hu₂,he₂⟩ := bpad_exec (body := body) (a := rg 2) (eR := rg 1) (t₁ := rg 3) (t₂ := rg 4)
    (by simp [List.nodup_cons,hrg.eq_iff]) hn v₁ C (by simp [C])
    (by simp [C,hrg.eq_iff,hblank 3 (by decide) (by decide) (by decide)])
    (by simp [C,hrg.eq_iff,hblank 4 (by decide) (by decide) (by decide)])
  have hp : (C.R (rg 1)).length = 1 := by simpa [C,hrg.eq_iff] using hpad
  rw [hp] at he₂
  let D : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms (L+1) n) }
  have hd : ({ C with R := Function.update C.R (rg 2) (binSyms (L+1) n) } : Stacks T A) = D := by simp [C,D]
  rw [hd] at he₂
  obtain ⟨v₃,hu₃,he₃⟩ := countIter_exec (body := body) (W := L+1) (j := n)
    (c := rg 2) (tmp := rg 3) (hrg.ne (by decide)) (rg 5) v₂ D (by simp [D])
    (by simp [D,hrg.eq_iff,hblank 3 (by decide) (by decide) (by decide)])
  let E : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms (L+1) (n+1)) }
  have he : ({ D with R := Function.update D.R (rg 2) (binSyms (L+1) (n+1)) } : Stacks T A) = E := by simp [D,E]
  rw [he] at he₃
  have hfit : n+1 < 2 ^ (L+1) := by
    rw [pow_succ]
    have := Nat.two_pow_pos L
    omega
  obtain ⟨v₄,hu₄,he₄⟩ := binaryCanonicalWord_exec body (rg 2) (rg 3) (hrg.ne (by decide))
    (L+1) (n+1) hfit v₃ E (by simp [E])
    (by simp [E,hrg.eq_iff,hblank 3 (by decide) (by decide) (by decide)])
  have hf : ({ E with R := Function.update E.R (rg 2) (binSyms (Nat.clog 2 (n+1+1)) (n+1)) } : Stacks T A) =
      { S with R := Function.update S.R (rg 2) (binSyms (Nat.clog 2 (n+1+1)) (n+1)) } := by simp [E]
  rw [hf] at he₄
  have hx := Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))
  exact ⟨v₄,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),Exec.cast hx (by omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
