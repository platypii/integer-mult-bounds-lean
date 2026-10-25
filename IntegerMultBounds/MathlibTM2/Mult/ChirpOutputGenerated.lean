module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputRun

/-! # Output arithmetic from binary dimensions, with full counter cleanup

Generate all nine counters, execute the connected arithmetic, and erase the
counters. No shift length, precision-drop word or crop count is supplied.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

noncomputable def chirpOutputGenerated {T Q A : ℕ} {P U : Type} (O : ChirpOutputLayout T)
    (rg : TblR 14 → Fin T) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (chirpOutputDimensionSetup rg O.dim)
    (.seq (chirpOutputRun O hT hQ) (clearWords (List.ofFn O.dim)))

def chirpOutputGeneratedCost {T : ℕ} (O : ChirpOutputLayout T) (W e N p q l Γ w t : ℕ) : ℕ :=
  (25 * tblC W e + unaryCopiesCost W (chirpOutputDimensionValues p q l Γ w t) (chirpOutputAssignments O.dim)) +
    (chirpOutputCompleteCost N p q l Γ w t +
      (2 * (List.ofFn (chirpOutputDimensionCount p q l Γ w t)).sum + 19))

/-- Generate, run and erase all output counters, restoring every other working register. -/
theorem chirpOutputGenerated_exec {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
    (O : ChirpOutputLayout T) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (rg : TblR 14 → Fin T) (hrg : Function.Injective rg) (hout : ∀ i r, rg r ≠ O.dim i)
    {W e : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (st : TblSt 14 A) (p q l Γ w t : ℕ)
    (hp : st.val 0 = p) (hq : st.val 1 = q) (hl : st.val 2 = l)
    (hΓ : st.val 3 = Γ) (hw : st.val 4 = w) (ht : st.val 5 = t)
    (hpq : p ≤ q) (hwidth : q + l + Γ + 5 ≤ w)
    (hvolume : t * (p + l + Γ + 5) < 2 ^ W)
    (hzero : ∀ i : Fin 14, 6 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (blocks : List (List GaussianInt)) (es : List ℤ) (a : ℤ) (hes0 : 1 ≤ es.length)
    (hlen : ∀ xs ∈ blocks, xs.length = es.length) (htN : t ≤ blocks.flatten.length)
    (hxs : ∀ c ∈ blocks.flatten, ‖value (q + 1) c‖ ≤ 1)
    (hes : ∀ x ∈ es, |(x : ℝ) / 2 ^ q| ≤ 2) (ha : |(a : ℝ) / 2 ^ q| ≤ 1)
    (v : HS T Q A U) (S : Stacks T A) (h : ChirpOutputState O S q w blocks es a)
    (hbank : tblHolds rg S (tblRho W wl nl st)) (hblank : ∀ i, S.R (O.bank i) = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ chirpOutputGeneratedCost O W e blocks.flatten.length p q l Γ w t ∧
      Exec body (chirpOutputGenerated O rg hT hQ) (mk v S) n
        (mk v' { S with R := (Function.update (Function.update S.R (O.cr .xs) []) (O.nr .out)
          (cstream A (p + l + Γ + 5)
            (((chirpOutputNumerators q l Γ blocks es a).take t).map (tdivN (q - p))))) }) := by
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := chirpOutputDimensionSetup_exec (body := body) hrg O.dim hout
    wl nl hwl hnl heW st p q l Γ w t hp hq hl hΓ hw ht hpq hwidth hvolume hzero hfit v S hbank
  let R₁ := unaryCopiesR (chirpOutputDimensionValues p q l Γ w t) S.R (chirpOutputAssignments O.dim)
  let S₁ : Stacks T A := { S with R := R₁ }
  have hd (i : Fin 9) : R₁ (O.dim i) = List.replicate (chirpOutputDimensionCount p q l Γ w t i) tick := by
    have hi := chirpOutputDimensions_at O.dim O.dim_inj p q l Γ w t S.R i
    simpa only [ChirpOutputLayout.dim, hblank, List.append_nil] using hi
  have hdim : ∀ i, (S₁.R (O.dim i)).length = chirpOutputDimensionCount p q l Γ w t i := by
    intro i
    change (R₁ (O.dim i)).length = _
    rw [hd, List.length_replicate]
  have hwork (i : Fin 22) (hi : 9 ≤ i.val) : S₁.R (O.bank i) = [] := by
    have hoff : ∀ j, O.bank i ≠ O.dim j := by
      intro j he
      have hv := congrArg Fin.val (O.bank_inj he)
      change i.val = j.val at hv
      omega
    exact (chirpOutputDimensions_off O.dim p q l Γ w t S.R (O.bank i) hoff).trans (hblank i)
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := chirpOutputRun_exec (body := body) O hT hQ hA
    p q l Γ w t hpq hwidth blocks es a hes0 hlen htN hxs hes ha v₁ S₁ (h.install p l Γ t) hdim hwork
  let output := cstream A (p + l + Γ + 5)
    (((chirpOutputNumerators q l Γ blocks es a).take t).map (tdivN (q - p)))
  let S₂ : Stacks T A := { S₁ with R :=
    (Function.update (Function.update S₁.R (O.cr .xs) []) (O.nr .out) output) }
  have hd₂ (i : Fin 9) : S₂.R (O.dim i) = List.replicate (chirpOutputDimensionCount p q l Γ w t i) tick := by
    change Function.update (Function.update S₁.R (O.cr .xs) []) (O.nr .out) output (O.dim i) = _
    rw [Function.update_of_ne (show O.dim i ≠ O.nr .out from O.bank_nr _ _),
      Function.update_of_ne (show O.dim i ≠ O.cr .xs from O.bank_cr _ _)]
    exact hd i
  have hnd : (List.ofFn O.dim).Nodup := List.nodup_ofFn.mpr O.dim_inj
  obtain ⟨v₃, hu₃, he₃⟩ := clearWords_exec (body := body) (List.ofFn O.dim) hnd v₂ S₂
  have hclear : 2 * ((List.ofFn O.dim).map fun k => (S₂.R k).length).sum +
      2 * (List.ofFn O.dim).length + 1 = 2 * (List.ofFn (chirpOutputDimensionCount p q l Γ w t)).sum + 19 := by
    simp only [List.map_ofFn, Function.comp_def, List.length_ofFn, hd₂, List.length_replicate]
  rw [hclear] at he₃
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), Nat.add_le_add hn₁ (Nat.add_le_add_right hn₂ _),
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  clear he₁ he₂ he₃
  funext k
  by_cases hc : ∃ i, O.dim i = k
  · obtain ⟨i, rfl⟩ := hc
    simp only [List.mem_ofFn, exists_apply_eq_apply, ite_true]
    simp [O.bank_cr, O.bank_nr, ChirpOutputLayout.dim, hblank]
  · have hoff : ∀ i, k ≠ O.dim i := fun i he => hc ⟨i, he.symm⟩
    have hmem : k ∉ List.ofFn O.dim := by simpa only [List.mem_ofFn] using hc
    simp only [ite_eq_right hmem, S₂, S₁]
    by_cases hx : k = O.cr .xs
    · subst k; simp only [Function.update_of_ne (O.input_frame .out).symm, Function.update_self]
    by_cases ho : k = O.nr .out
    · subst k; simp only [Function.update_self, output, List.map_take]
    · simp only [Function.update_of_ne hx, Function.update_of_ne ho]
      exact chirpOutputDimensions_off O.dim p q l Γ w t S.R k hoff

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
