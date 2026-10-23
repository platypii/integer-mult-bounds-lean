module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Translate a live binary coordinate from one interval base to another.
Subtraction, addition and temporary erasure are executed and fully charged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

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

end IntegerMultBounds.MathlibTM2.Routing
