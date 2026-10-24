module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryProductLowCopy
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirBudget
public import IntegerMultBounds.MathlibTM2.Host.BinArithDiv

/-! Compute `(n/K+1)*G` from compact binary inputs, restoring division and
multiplication temporaries. With `K=64*G` this is the canonical reservoir width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def reservoirWidthProductSlot : Fin 11 → Fin 14 := ![4,2,3,6,7,8,9,10,13,11,12]
theorem reservoirWidthProductSlot_injective : Function.Injective reservoirWidthProductSlot := by decide +kernel

def reservoirWidthGenerateProgram (rg : Fin 14 → Fin T) : Pr P T Q A U :=
  .seq (bdivmod (rg 0) (rg 1) (rg 4) (rg 5) (rg 6) (rg 7) (rg 8) (rg 9) (rg 10) (rg 11) (rg 12))
    (.seq (countIter (rg 4) (rg 9) (rg 12))
      (.seq (binaryProductLowCopyProgram (rg ∘ reservoirWidthProductSlot))
        (.seq (bclear (rg 4)) (bclear (rg 5)))))

theorem reservoirWidthGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 14 → Fin T) (hrg : Function.Injective rg) (M L n K G : ℕ)
    (hL : L < 2 ^ M) (hn : n < 2 ^ L) (hK : 1 < K) (hKn : K ≤ n) (hG : G < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hstride : S.R (rg 1) = binSyms L K)
    (hgap : S.R (rg 2) = binSyms L G) (hwidth : S.R (rg 3) = binSyms M L)
    (hblank : ∀ j : Fin 14, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → j ≠ 12 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 36 * L * L + 133 * L + 89 + M * (4 * L + 11) ∧
      Exec body (reservoirWidthGenerateProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg 13) (binSyms L ((n / K + 1) * G)) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := bdivmod_exec (body := body)
    (a := rg 0) (b := rg 1) (q := rg 4) (r := rg 5) (bw := rg 6) (rr := rg 7) (t := rg 8)
    (tx := rg 9) (ty := rg 10) (tz := rg 11) (cy := rg 12)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide)) hn (hKn.trans_lt hn)
    (by omega : 0 < K) v S hdimension hstride
    (hblank 6 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hblank 7 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hblank 8 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hblank 9 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hblank 10 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hblank 11 (by decide) (by decide) (by decide) (by decide) (by decide))
  rw [hblank 4 (by decide) (by decide) (by decide) (by decide) (by decide),
    hblank 5 (by decide) (by decide) (by decide) (by decide) (by decide)] at he₁
  simp only [List.append_nil] at he₁
  let C : Stacks T A := { S with R := (Function.update (Function.update S.R (rg 4) (binSyms L (n / K)))
    (rg 5) (binSyms L (n % K))) }
  obtain ⟨v₂, hu₂, he₂⟩ := countIter_exec body (c := rg 4) (tmp := rg 9) (W := L) (j := n / K) (hrg.ne (by decide)) (rg 12) v₁ C
    (by simp [C, hrg.eq_iff])
    (by simp [C, hrg.eq_iff, hblank 9 (by decide) (by decide) (by decide) (by decide) (by decide)])
  let D : Stacks T A := { C with R := Function.update C.R (rg 4) (binSyms L (n / K + 1)) }
  have keep (j : Fin 14) (hj4 : j ≠ 4) (hj5 : j ≠ 5) : D.R (rg j) = S.R (rg j) := by
    simp [D, C, hrg.eq_iff, hj4, hj5]
  have hsep : ∀ j : Fin 11, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 10 →
      let a := reservoirWidthProductSlot j
      a ≠ 4 ∧ a ≠ 5 ∧ a ≠ 0 ∧ a ≠ 1 ∧ a ≠ 2 ∧ a ≠ 3 ∧ a ≠ 12 := by decide +kernel
  have hproductBlank : ∀ j : Fin 11, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 10 →
      D.R ((rg ∘ reservoirWidthProductSlot) j) = [] := by
    intro j hj0 hj1 hj2 hj10
    obtain ⟨h4,h5,h0,h1,h2,h3,h12⟩ := hsep j hj0 hj1 hj2 hj10
    exact (keep _ h4 h5).trans (hblank _ h0 h1 h2 h3 h12)
  have hquotient : n / K + 1 < 2 ^ L := by
    have hd := Nat.div_lt_self (by omega : 0 < n) hK
    omega
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := binaryProductLowCopy_exec body (rg ∘ reservoirWidthProductSlot)
    (hrg.comp reservoirWidthProductSlot_injective) M L (n / K + 1) G hL hquotient hG v₂ D
    (by change D.R (rg 4) = _; simp [D]) ((keep 2 (by decide) (by decide)).trans hgap)
    ((keep 3 (by decide) (by decide)).trans hwidth) hproductBlank
  let E : Stacks T A := { D with R := Function.update D.R (rg 13) (binSyms L ((n / K + 1) * G)) }
  obtain ⟨v₄, hu₄, _, he₄⟩ := bclear_exec (body := body) (rg 4) v₃ E
  have hlen4 : (E.R (rg 4)).length = L := by simp [E, D, hrg.eq_iff, length_binSyms]
  rw [hlen4] at he₄
  let F : Stacks T A := { E with R := Function.update E.R (rg 4) [] }
  obtain ⟨v₅, hu₅, _, he₅⟩ := bclear_exec (body := body) (rg 5) v₄ F
  have hlen5 : (F.R (rg 5)).length = L := by simp [F, E, D, C, hrg.eq_iff, length_binSyms]
  have hfinal : ({ F with R := Function.update F.R (rg 5) [] } : Stacks T A) =
      { S with R := Function.update S.R (rg 13) (binSyms L ((n / K + 1) * G)) } := by
    congr 1
    funext x
    by_cases h4 : x = rg 4
    · subst x; simp [F, E, D, C, hrg.eq_iff, hblank 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
    · by_cases h5 : x = rg 5
      · subst x; simp [hrg.eq_iff, hblank 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
      · by_cases h13 : x = rg 13 <;> simp [F, E, D, C, h4, h5, h13, hrg.eq_iff]
  rw [hlen5, hfinal] at he₅
  refine ⟨v₅, m₁ + ((4 * L + 5) + (m₃ + ((2 * L + 2) + (2 * L + 2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_, Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))⟩
  nlinarith only [hm₁, hm₃]

/-- The chosen stride turns the executed arithmetic into the canonical reservoir. -/
theorem routingReservoirWidth_generate_exec (body : P → Pr P T Q A U)
    (rg : Fin 14 → Fin T) (hrg : Function.Injective rg) (M L n G : ℕ)
    (hL : L < 2 ^ M) (hn : n < 2 ^ L) (hG : 0 < G) (hlarge : 64 * G ≤ n)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hstride : S.R (rg 1) = binSyms L (64 * G))
    (hgap : S.R (rg 2) = binSyms L G) (hwidth : S.R (rg 3) = binSyms M L)
    (hblank : ∀ j : Fin 14, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → j ≠ 12 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 36 * L * L + 133 * L + 89 + M * (4 * L + 11) ∧
      Exec body (reservoirWidthGenerateProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg 13) (binSyms L (routingReservoirWidth n G)) }) := by
  simpa only [routingReservoirWidth] using
    reservoirWidthGenerate_exec body rg hrg M L n (64 * G) G hL hn (by omega) hlarge (by omega)
      v S hdimension hstride hgap hwidth hblank

end IntegerMultBounds.MathlibTM2.Routing
