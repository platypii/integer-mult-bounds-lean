module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpS1Dimensions
public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopies

/-! # Generate shared S1 unary dimensions and restore the binary bank -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR 10 → Fin T}

/-- Unary output order: p, l, w, input length, kernel length, batch count, m. -/
def chirpS1Assignments (dst : Fin 7 → Fin T) : List (Fin 10 × Fin T) :=
  [(5, dst 0), (4, dst 1), (3, dst 2), (6, dst 3), (7, dst 4), (8, dst 5), (2, dst 6)]

def chirpS1DimensionSetup (rg : TblR 10 → Fin T) (dst : Fin 7 → Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg tblChirpS1Dimensions)
    (.seq (tblUnaryCopies rg (chirpS1Assignments dst)) (tblCompile rg tblChirpS1DimensionsClear))

/-- All seven unary dimensions are computed from the retained dimension words. Every other stack,
including the full binary working bank, returns to its initial state. -/
theorem chirpS1DimensionSetup_exec (hrg : Function.Injective rg) (dst : Fin 7 → Fin T)
    (hout : ∀ i r, rg r ≠ dst i) {W e : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (st : TblSt 10 A) (q t m w l : ℕ) (hq : st.val 0 = q) (ht : st.val 1 = t) (hm : st.val 2 = m)
    (hw : st.val 3 = w) (hl : st.val 4 = l)
    (ht0 : 0 < t) (hm0 : 0 < m) (hp : q + 1 < 2 ^ W)
    (hsize : 3 * m + 1 < 2 ^ W) (hkernel : 4 * m < 2 ^ W)
    (hzero : ∀ i : Fin 10, 5 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' k, v'.user = v.user ∧
      k ≤ 18 * tblC W e + unaryCopiesCost W (chirpS1DimensionValues q t m w l) (chirpS1Assignments dst) ∧
      Exec body (chirpS1DimensionSetup rg dst) (mk v S) k
        (mk v' { S with R := unaryCopiesR (chirpS1DimensionValues q t m w l) S.R (chirpS1Assignments dst) }) := by
  classical
  obtain ⟨st₁, ⟨hv₁, ha₁, hfit₁⟩, hargs⟩ :=
    (tblChirpS1Dimensions_do (e := e) st q t m w l hq ht hm hw hl ht0 hm0 hp hsize hkernel hfit).host
      (body := body) hrg wl nl hwl hnl heW hfit
  obtain ⟨v₁, S₁, k₁, hu₁, hk₁, he₁, hb₁, hfr₁⟩ := hargs v S hS
  have hpout : ∀ p ∈ chirpS1Assignments dst, ∀ r, rg r ≠ p.2 := by
    intro p hp
    simp only [chirpS1Assignments, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hout 0
    · exact hout 1
    · exact hout 2
    · exact hout 3
    · exact hout 4
    · exact hout 5
    · exact hout 6
  obtain ⟨v₂, k₂, hu₂, hk₂, he₂⟩ := tblUnaryCopies_exec (body := body) hrg wl nl st₁ hfit₁
    (chirpS1Assignments dst) hpout v₁ S₁ hb₁
  let S₂ : Stacks T A := { S₁ with R := unaryCopiesR st₁.val S₁.R (chirpS1Assignments dst) }
  have hb₂ : tblHolds rg S₂ (tblRho W wl nl st₁) := by
    intro r
    change unaryCopiesR st₁.val S₁.R (chirpS1Assignments dst) (rg r) = _
    rw [unaryCopiesR_off _ _ _ _ (fun p hp => (hpout p hp r).symm)]
    exact hb₁ r
  have hf₁ : ∀ i : Fin 10, i.val < 5 → st₁.val i = st.val i := by
    intro i hi
    rw [hv₁]
    fin_cases i <;> first | (simp at hi; done) | simp [chirpS1DimensionValues, hq, ht, hm, hw, hl]
  obtain ⟨st₃, ⟨hv₃, ha₃⟩, hclear⟩ :=
    (tblChirpS1DimensionsClear_do (W := W) (e := e) st st₁ hf₁ hzero).host
      (body := body) hrg wl nl hwl hnl heW hfit₁
  have hst₃ : st₃ = st := by
    have ha : st₃.acc = st.acc := ha₃.trans ha₁
    cases st₃; cases st
    simp_all only
  subst st₃
  obtain ⟨v₃, S₃, k₃, hu₃, hk₃, he₃, hb₃, hfr₃⟩ := hclear v₂ S₂ hb₂
  rw [hv₁] at hk₂
  refine ⟨v₃, k₁ + (k₂ + k₃), hu₃.trans (hu₂.trans hu₁), by omega,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  congr 1
  ext1
  · exact hfr₃.1.trans hfr₁.1
  · exact hfr₃.2.1.trans hfr₁.2.1
  · exact hfr₃.2.2.1.trans hfr₁.2.2.1
  funext k
  by_cases hbank : ∃ r, rg r = k
  · obtain ⟨r, rfl⟩ := hbank
    change S₃.R (rg r) = unaryCopiesR (chirpS1DimensionValues q t m w l) S.R (chirpS1Assignments dst) (rg r)
    rw [unaryCopiesR_off _ _ _ _ (fun p hp => (hpout p hp r).symm)]
    exact (hb₃ r).trans (hS r).symm
  · have hoff : ∀ r, rg r ≠ k := by simpa using hbank
    rw [hfr₃.2.2.2 k hoff]
    change unaryCopiesR st₁.val S₁.R (chirpS1Assignments dst) k = _
    rw [unaryCopiesR_congr st₁.val (chirpS1DimensionValues q t m w l) S₁.R _
      (fun p hp => congrFun hv₁ p.1)]
    exact unaryCopiesR_congr_base _ _ _ _ k
      (fun p hp => hfr₁.2.2.2 p.2 (hpout p hp)) (hfr₁.2.2.2 k hoff)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
