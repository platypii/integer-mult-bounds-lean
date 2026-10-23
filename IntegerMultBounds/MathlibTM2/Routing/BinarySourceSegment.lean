module

public import IntegerMultBounds.MathlibTM2.Host.BinArithDiv

/-! Decode a Y coordinate in the digit region into quotient and remainder.
The original coordinate, region base and stride are preserved; subtraction and
division scratch restore, leaving only the two decoded outputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binarySourceSegmentProgram (rg : Fin 13 → Fin T) : Pr P T Q A U :=
  .seq (bsub (rg 0) (rg 1) (rg 3) (rg 9) (rg 10) (rg 11) (rg 12))
    (.seq (bdivmod (rg 3) (rg 2) (rg 4) (rg 5) (rg 6) (rg 7) (rg 8)
      (rg 9) (rg 10) (rg 11) (rg 12)) (bclear (rg 3)))

theorem binarySourceSegment_exec (body : P → Pr P T Q A U)
    (rg : Fin 13 → Fin T) (hrg : Function.Injective rg)
    (L Lk q base k : ℕ) (hq : q < 2 ^ L) (hbase : base ≤ q)
    (hk : k < 2 ^ Lk) (hk0 : 0 < k)
    (v : HS T Q A U) (S : Stacks T A)
    (hqInput : S.R (rg 0) = binSyms L q) (hbaseInput : S.R (rg 1) = binSyms L base)
    (hkInput : S.R (rg 2) = binSyms Lk k)
    (hblank : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 12 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ L * (12 * Lk + 35) + 20 * Lk + 10 * L + 46 ∧
      Exec body (binarySourceSegmentProgram rg) (mk v S) steps
        (mk v' { S with R := Function.update (Function.update S.R (rg 4) (binSyms L ((q - base) / k))) (rg 5) (binSyms Lk ((q - base) % k)) }) := by
  have hb (j : Fin 13) (h0 : j ≠ 0) (h1 : j ≠ 1) (h2 : j ≠ 2) (h12 : j ≠ 12) := hblank j h0 h1 h2 h12
  obtain ⟨v₁, hu₁, _, _, hx₁⟩ := bsub_exec body
    (a := rg 0) (b := rg 1) (c := rg 3) (tx := rg 9) (ty := rg 10) (tz := rg 11) (cy := rg 12)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    hq (by omega : base < 2 ^ L) v S hqInput hbaseInput
    (hb 9 (by decide) (by decide) (by decide) (by decide))
    (hb 10 (by decide) (by decide) (by decide) (by decide))
    (hb 11 (by decide) (by decide) (by decide) (by decide))
  have hm : (q + 2 ^ L - base) % 2 ^ L = q - base := by
    rw [show q + 2 ^ L - base = (q - base) + 2 ^ L by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hm, hb 3 (by decide) (by decide) (by decide) (by decide), List.append_nil] at hx₁
  let G : Stacks T A := { S with R := Function.update S.R (rg 3) (binSyms L (q - base)) }
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := bdivmod_exec body
    (a := rg 3) (b := rg 2) (q := rg 4) (r := rg 5) (bw := rg 6) (rr := rg 7) (t := rg 8)
    (tx := rg 9) (ty := rg 10) (tz := rg 11) (cy := rg 12)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    (by omega : q - base < 2 ^ L) hk hk0 v₁ G (by simp [G]) (by simp [G, hrg.eq_iff, hkInput])
    (by simp [G, hrg.eq_iff, hb 6 (by decide) (by decide) (by decide) (by decide)])
    (by simp [G, hrg.eq_iff, hb 7 (by decide) (by decide) (by decide) (by decide)])
    (by simp [G, hrg.eq_iff, hb 8 (by decide) (by decide) (by decide) (by decide)])
    (by simp [G, hrg.eq_iff, hb 9 (by decide) (by decide) (by decide) (by decide)])
    (by simp [G, hrg.eq_iff, hb 10 (by decide) (by decide) (by decide) (by decide)])
    (by simp [G, hrg.eq_iff, hb 11 (by decide) (by decide) (by decide) (by decide)])
  have h4 : G.R (rg 4) = [] := by simp [G, hrg.eq_iff, hb 4 (by decide) (by decide) (by decide) (by decide)]
  have h5 : G.R (rg 5) = [] := by simp [G, hrg.eq_iff, hb 5 (by decide) (by decide) (by decide) (by decide)]
  rw [h4, h5, List.append_nil, List.append_nil] at hx₂
  let H : Stacks T A := { G with R := Function.update (Function.update G.R (rg 4) (binSyms L ((q - base) / k))) (rg 5) (binSyms Lk ((q - base) % k)) }
  obtain ⟨v₃, hu₃, _, hx₃⟩ := bclear_exec body (rg 3) v₂ H
  have h3 : H.R (rg 3) = binSyms L (q - base) := by simp [H, G, hrg.eq_iff]
  have hf : Function.update H.R (rg 3) [] = Function.update (Function.update S.R (rg 4)
      (binSyms L ((q - base) / k))) (rg 5) (binSyms Lk ((q - base) % k)) := by
    funext j
    by_cases h3 : j = rg 3 <;> by_cases h4 : j = rg 4 <;> by_cases h5 : j = rg 5 <;>
      simp_all [H, G, hrg.eq_iff, hb 3 (by decide) (by decide) (by decide) (by decide)]
  rw [hf, h3, length_binSyms] at hx₃
  exact ⟨v₃, (8 * L + 8) + (m₂ + (2 * L + 2)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq hx₁ (Exec.seq hx₂ hx₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
