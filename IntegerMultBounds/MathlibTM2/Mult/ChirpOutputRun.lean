module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputLayout

/-! # Run the complete output arithmetic through its register interface -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Node

/-- Counter values and scratch emptiness are the only metadata preconditions. -/
theorem chirpOutputRun_exec {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
    (O : ChirpOutputLayout T) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p q l Γ w t : ℕ) (hpq : p ≤ q) (hw : q + l + Γ + 5 ≤ w)
    (blocks : List (List GaussianInt)) (es : List ℤ) (a : ℤ) (hes0 : 1 ≤ es.length)
    (hlen : ∀ xs ∈ blocks, xs.length = es.length) (ht : t ≤ blocks.flatten.length)
    (hxs : ∀ c ∈ blocks.flatten, ‖value (q + 1) c‖ ≤ 1)
    (hes : ∀ e ∈ es, |(e : ℝ) / 2 ^ q| ≤ 2) (ha : |(a : ℝ) / 2 ^ q| ≤ 1)
    (v : HS T Q A U) (S : Stacks T A) (h : ChirpOutputState O S q w blocks es a)
    (hdim : ∀ i, (S.R (O.dim i)).length = chirpOutputDimensionCount p q l Γ w t i)
    (hwork : ∀ i : Fin 22, 9 ≤ i.val → S.R (O.bank i) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ chirpOutputCompleteCost blocks.flatten.length p q l Γ w t ∧
      Exec body (chirpOutputRun O hT hQ) (mk v S) n
        (mk v' { S with R := (Function.update (Function.update S.R (O.cr .xs) []) (O.nr .out)
          (cstream A (p + l + Γ + 5)
            (((chirpOutputNumerators q l Γ blocks es a).take t).map (tdivN (q - p))))) }) := by
  have hcrOff (r : CR) (i : Fin 22) : O.cr r ≠ O.bank i := (O.bank_cr i r).symm
  have hnrOff (r : CR) (i : Fin 22) : O.nr r ≠ O.bank i := (O.bank_nr i r).symm
  have hreg : [O.cr .xs, O.bank 9, O.dim 0, O.dim 1, O.bank 10, O.bank 11].Nodup := by
    simp [ChirpOutputLayout.dim, List.nodup_cons, O.bank_inj.eq_iff, hcrOff]
  have hnreg : [O.nr .xs, O.bank 12, O.dim 2, O.dim 3, O.bank 13, O.bank 14].Nodup := by
    simp [ChirpOutputLayout.dim, List.nodup_cons, O.bank_inj.eq_iff, hnrOff]
  have hround : [O.nr .out, O.bank 15, O.bank 16, O.dim 4, O.dim 5, O.dim 6, O.dim 7,
      O.bank 17, O.bank 18, O.bank 19].Nodup := by
    simp [ChirpOutputLayout.dim, List.nodup_cons, O.bank_inj.eq_iff, hnrOff]
  have hcrop : [O.dim 8, O.nr .out, O.bank 20, O.bank 21].Nodup := by
    simp [ChirpOutputLayout.dim, List.nodup_cons, O.bank_inj.eq_iff, hnrOff, O.bank_nr]
  have hnwork : ∀ k ∈ [O.bank 12, O.dim 2, O.dim 3, O.bank 13, O.bank 14],
      k ≠ O.cr .xs ∧ k ≠ O.cr .out := by
    simp only [ChirpOutputLayout.dim, List.mem_cons, List.not_mem_nil, or_false]
    rintro k (rfl | rfl | rfl | rfl | rfl)
    all_goals exact ⟨O.bank_cr _ _, O.bank_cr _ _⟩
  have hfinish : ∀ k ∈ [O.bank 15, O.bank 16, O.dim 4, O.dim 5, O.dim 6, O.dim 7,
      O.bank 17, O.bank 18, O.bank 19, O.dim 8, O.bank 20, O.bank 21],
      k ≠ O.cr .xs ∧ k ≠ O.nr .xs ∧ k ≠ O.nr .out := by
    simp only [ChirpOutputLayout.dim, List.mem_cons, List.not_mem_nil, or_false]
    rintro k (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals exact ⟨O.bank_cr _ _, O.bank_nr _ _, O.bank_nr _ _⟩
  have hg : topShiftG (O.bank 16) (O.dim 4) (O.dim 5) (O.dim 6) (O.dim 7)
      (O.bank 17) (O.bank 18) (O.bank 19) w (q - p) (p + l + Γ + 5) S.R := by
    refine ⟨?_, ?_, ?_, ?_, hwork 17 (by decide), hwork 18 (by decide),
      hwork 19 (by decide), hwork 16 (by decide)⟩
    · simpa [chirpOutputDimensionCount] using hdim 4
    · simpa [chirpOutputDimensionCount] using hdim 5
    · simpa [chirpOutputDimensionCount] using hdim 6
    · simpa [chirpOutputDimensionCount] using hdim 7
  exact chirpOutputComplete_exec (body := body) O.cr_inj O.cr_mul O.mul_inj hT hQ hA hreg
    q l Γ w hw blocks es hes0 hlen hxs hes (fun r => S.R (O.cr r)) h.cr_ready h.input h.factors
    (h.cr_empty .xsv (by simp)) (h.cr_empty .ysv (by simp)) (h.cr_empty .acc (by simp))
    v S h.mul_clean (fun _ => rfl)
    (by simpa [chirpOutputDimensionCount] using hdim 0)
    (by simpa [chirpOutputDimensionCount] using hdim 1)
    (hwork 9 (by decide)) (hwork 10 (by decide)) (hwork 11 (by decide))
    O.nr O.nr_inj O.nr_mul O.link O.input_frame a ha (fun r => S.R (O.nr r)) h.nr_ready
    (fun _ => rfl) h.normalization
    (h.nr_empty .xsv (by simp)) (h.nr_empty .ysv (by simp)) (h.nr_empty .acc (by simp))
    (h.cr_empty .out (by simp)) (O.bank 12) (O.dim 2) (O.dim 3) (O.bank 13) (O.bank 14)
    hnreg hnwork (by simpa [chirpOutputDimensionCount] using hdim 2)
    (by simpa [chirpOutputDimensionCount] using hdim 3)
    (hwork 12 (by decide)) (hwork 13 (by decide)) (hwork 14 (by decide))
    p t hpq (h.nr_empty .out (by simp)) hround hcrop hfinish (hwork 15 (by decide)) hg
    (by rw [Nat.min_eq_left ht]; simpa [chirpOutputDimensionCount] using hdim 8)
    (hwork 20 (by decide)) (hwork 21 (by decide))

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
