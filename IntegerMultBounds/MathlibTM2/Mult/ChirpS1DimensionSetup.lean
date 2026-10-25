module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpS1Dimensions
public import IntegerMultBounds.MathlibTM2.Mult.ChirpDimensionScope

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
  apply tblComputedUnaryCopies_exec (body := body) hrg wl nl hwl hnl heW
    tblChirpS1Dimensions tblChirpS1DimensionsClear st (chirpS1DimensionValues q t m w l) 13 5
    (tblChirpS1Dimensions_do st q t m w l hq ht hm hw hl ht0 hm0 hp hsize hkernel hfit)
    (fun z hz => tblChirpS1DimensionsClear_do st z (by
      intro i hi
      rw [hz]
      fin_cases i <;> first | (simp at hi; done) |
        simp [chirpS1DimensionValues, hq, ht, hm, hw, hl]) hzero)
    hfit (chirpS1Assignments dst) (by
      intro a ha
      simp only [chirpS1Assignments, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hout _) v S hS

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
