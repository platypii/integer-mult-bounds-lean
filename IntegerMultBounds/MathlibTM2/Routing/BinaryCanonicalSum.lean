module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryCrossPad
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalSuccessor

/-! Preserved, independently padded operands for the canonical word `x+y+1`.
The common width includes its own carry bit; no sum-fit hypothesis is needed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

theorem binarySumSuccessor_fit (L M x y : ℕ) (hx : x < 2^L) (hy : y < 2^M) :
    x+y+1 < 2^(L+M+1) := by
  have hL : 2^L ≤ 2^(L+M) := Nat.pow_le_pow_right (by decide) (by omega)
  have hM : 2^M ≤ 2^(L+M) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_succ]
  omega

variable {T Q A : ℕ} {P U : Type}

def binaryCanonicalSumSlot : Fin 7 → Fin 10 := ![0,1,2,3,4,6,7]

theorem binaryCanonicalSumSlot_injective : Function.Injective binaryCanonicalSumSlot := by
  decide +kernel

def binaryCanonicalSumProgram (rg : Fin 10 → Fin T) : Pr P T Q A U :=
  .seq (binaryCrossPadProgram (rg ∘ binaryCanonicalSumSlot))
    (.seq (badd (rg 3) (rg 4) (rg 5) (rg 6) (rg 7) (rg 8) (rg 9))
      (.seq (countIter (rg 5) (rg 6) (rg 9))
        (.seq (binaryCanonicalProgram (rg 5) (rg 6))
          (.seq (bclear (rg 3)) (bclear (rg 4))))))

theorem binaryCanonicalSum_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (L M x y : ℕ)
    (hx : x < 2^L) (hy : y < 2^M) (v : HS T Q A U) (S : Stacks T A)
    (hsrcX : S.R (rg 0) = binSyms L x) (hsrcY : S.R (rg 1) = binSyms M y)
    (hone : (S.R (rg 2)).length = 1)
    (hblank : ∀ i : Fin 10, i ≠ 0 → i ≠ 1 → i ≠ 2 → S.R (rg i) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (binaryCanonicalSumProgram rg) (mk v S) (44*(L+M)+99)
        (mk v' { S with R := (Function.update S.R (rg 5)
          (binSyms (Nat.clog 2 (x+y+1+1)) (x+y+1))) }) := by
  have off : ∀ i : Fin 7, i ≠ 0 → i ≠ 1 → i ≠ 2 →
      binaryCanonicalSumSlot i ≠ 0 ∧ binaryCanonicalSumSlot i ≠ 1 ∧
        binaryCanonicalSumSlot i ≠ 2 := by decide +kernel
  obtain ⟨v₁,hu₁,he₁⟩ := binaryCrossPad_exec body (rg ∘ binaryCanonicalSumSlot)
    (hrg.comp binaryCanonicalSumSlot_injective) L M x y hx hy v S hsrcX hsrcY hone
    (by intro i h0 h1 h2; have h := off i h0 h1 h2; exact hblank _ h.1 h.2.1 h.2.2)
  let W := L+M+1
  let C : Stacks T A := { S with R := (Function.update (Function.update S.R
    (rg 3) (binSyms W x)) (rg 4) (binSyms W y)) }
  have hfit := binarySumSuccessor_fit L M x y hx hy
  have hxW : x < 2^W := by dsimp [W]; omega
  have hyW : y < 2^W := by dsimp [W]; omega
  obtain ⟨v₂,hu₂,_,_,he₂⟩ := badd_exec (body := body)
    (a := rg 3) (b := rg 4) (c := rg 5) (tx := rg 6) (ty := rg 7) (tz := rg 8) (cy := rg 9)
    (by simp [List.nodup_cons,hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    hxW hyW v₁ C (by simp [C,hrg.eq_iff]) (by simp [C])
    (by simp [C,hrg.eq_iff,hblank 6 (by decide) (by decide) (by decide)])
    (by simp [C,hrg.eq_iff,hblank 7 (by decide) (by decide) (by decide)])
    (by simp [C,hrg.eq_iff,hblank 8 (by decide) (by decide) (by decide)])
  have hsum : (x+y) % 2^W = x+y := Nat.mod_eq_of_lt (by dsimp [W]; omega)
  rw [hsum] at he₂
  simp only [C,Function.update_apply,hrg.eq_iff] at he₂
  simp only [show (5 : Fin 10) ≠ 4 from by decide,show (5 : Fin 10) ≠ 3 from by decide,
    ↓reduceIte,hblank 5 (by decide) (by decide) (by decide),List.append_nil] at he₂
  let D : Stacks T A := { C with R := Function.update C.R (rg 5) (binSyms W (x+y)) }
  obtain ⟨v₃,hu₃,he₃⟩ := countIter_exec (body := body) (W := W) (j := x+y)
    (c := rg 5) (tmp := rg 6) (hrg.ne (by decide)) (rg 9) v₂ D (by simp [D])
    (by simp [D,C,hrg.eq_iff,hblank 6 (by decide) (by decide) (by decide)])
  let E : Stacks T A := { C with R := Function.update C.R (rg 5) (binSyms W (x+y+1)) }
  have hE : ({ D with R := Function.update D.R (rg 5) (binSyms W (x+y+1)) } : Stacks T A) = E := by
    simp [D,E]
  rw [hE] at he₃
  obtain ⟨v₄,hu₄,he₄⟩ := binaryCanonicalWord_exec body (rg 5) (rg 6) (hrg.ne (by decide))
    W (x+y+1) hfit v₃ E (by simp [E])
    (by simp [E,C,hrg.eq_iff,hblank 6 (by decide) (by decide) (by decide)])
  let F : Stacks T A := { E with R := (Function.update E.R (rg 5)
    (binSyms (Nat.clog 2 (x+y+1+1)) (x+y+1))) }
  obtain ⟨v₅,hu₅,_,he₅⟩ := bclear_exec (body := body) (rg 3) v₄ F
  have hf3 : F.R (rg 3) = binSyms W x := by simp [F,E,C,hrg.eq_iff]
  rw [hf3,length_binSyms] at he₅
  let G : Stacks T A := { F with R := Function.update F.R (rg 3) [] }
  obtain ⟨v₆,hu₆,_,he₆⟩ := bclear_exec (body := body) (rg 4) v₅ G
  have hg4 : G.R (rg 4) = binSyms W y := by simp [G,F,E,C,hrg.eq_iff]
  rw [hg4,length_binSyms] at he₆
  have hfinal : ({ G with R := Function.update G.R (rg 4) [] } : Stacks T A) =
      { S with R := (Function.update S.R (rg 5)
        (binSyms (Nat.clog 2 (x+y+1+1)) (x+y+1))) } := by
    simp only [G,F,E,C]
    congr 1
    funext i
    by_cases h3 : i = rg 3
    · subst i; simp [hrg.eq_iff,hblank 3 (by decide) (by decide) (by decide)]
    by_cases h4 : i = rg 4
    · subst i; simp [hrg.eq_iff,hblank 4 (by decide) (by decide) (by decide)]
    simp [Function.update_apply,h3,h4]
  rw [hfinal] at he₆
  have he := Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆))))
  exact ⟨v₆,hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),
    Exec.cast he (by dsimp [W]; omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
