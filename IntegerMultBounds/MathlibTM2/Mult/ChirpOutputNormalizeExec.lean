module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputEExec

/-! # Execute the Γ shift and normalization product

The normalization table consists of one real word, reused across the complete stream.
Only the scaled source and product destination change; counters, table and scratch stay.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {cr : CR → Fin T} {ι : Fin 64 → Fin T}

def chirpOutputNormalize (q Γ : ℕ) (x : GaussianInt) (a : ℤ) : GaussianInt :=
  tdivN q ((⟨a, 0⟩ : GaussianInt) * ((2 : GaussianInt) ^ Γ * x))

/-- The normalization stage completes the integer output numerator. -/
theorem chirpOutputNormalize_EProduct (q l Γ : ℕ) (c : GaussianInt) (e a : ℤ) :
    chirpOutputNormalize q Γ (chirpOutputEProduct q l c e) a =
      chirpOutputNumerator q l Γ c e a := rfl

/-- Execute Γ scaling and the reused normalization product with derived signed fits. -/
theorem chirpOutputNormalize_exec (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {buf shift rest savedShift savedRest : Fin T}
    (hreg : [cr .xs, buf, shift, rest, savedShift, savedRest].Nodup)
    (q l Γ w : ℕ) (hw : q + l + Γ + 5 ≤ w) (xs : List GaussianInt) (a : ℤ)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ 8 * (2 : ℝ) ^ l) (ha : |(a : ℝ) / 2 ^ q| ≤ 1)
    (ρ : CR → List (Fin (A + 4))) (hr : Ready ρ w q)
    (hX : ρ .xs = cstream A w xs) (hAword : ρ .ys = csyms A w (⟨a, 0⟩ : GaussianInt))
    (hxsv : ρ .xsv = []) (hysv : ρ .ysv = []) (hacc : ρ .acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hc : CClean ι S) (hS : CHolds cr S ρ)
    (hshift : (S.R shift).length = Γ) (hrest : (S.R rest).length = w - Γ)
    (hbuf : S.R buf = []) (hsavedShift : S.R savedShift = []) (hsavedRest : S.R savedRest = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ xs.length * (6 * w + 4 * Γ + 14) + 4 +
        (xs.length * (rmulCost w + 6 * w + 8) + 6) ∧
      Exec body
        (.seq (shiftInto (cr .xs) buf (cr .xs) shift rest savedShift savedRest (pairSym A false false))
          (cmulTable cr (rmulOne ι hι hT hQ cr))) (mk v S) n
        (mk v' { S with R := (Function.update
          (Function.update S.R (cr .xs) (cstream A w (xs.map fun x => (2 : GaussianInt) ^ Γ * x)))
          (cr .out) (cstream A w (xs.map fun x => chirpOutputNormalize q Γ x a) ++ S.R (cr .out))) }) := by
  let shifted := xs.map fun x => (2 : GaussianInt) ^ Γ * x
  let words := cstream A w shifted
  obtain ⟨v₁, hu₁, he₁⟩ := chirpScale_exec (body := body) hreg w Γ (by omega) (by omega) xs
    v S ((hS .xs).trans hX) hshift hrest hbuf hsavedShift hsavedRest
  let S₁ : Stacks T A := { S with R := Function.update S.R (cr .xs) words }
  let ρ₁ := Function.update ρ CR.xs words
  have hS₁ : CHolds cr S₁ ρ₁ := holds_upd hcr hS .xs words
  have hc₁ : CClean ι S₁ := fun r => ⟨(hc r).1,
    (Function.update_of_ne (hdisj .xs r).symm _ _).trans (hc r).2⟩
  let rows := shifted.map (fun x => [x])
  have hflat : rows.flatten = shifted := by simp only [rows, ← List.flatMap_def, List.flatMap_singleton']
  have hresult : tableOut (fun x y => tdivN q (x * y)) rows [(⟨a, 0⟩ : GaussianInt)] =
      xs.map (fun x => chirpOutputNormalize q Γ x a) := by
    simp only [tableOut, rows, shifted, List.flatMap_map]
    simp only [List.zipWith_cons_cons, List.zipWith_nil_left, ← List.map_eq_flatMap]
    congr 1
    funext x
    exact congrArg (tdivN q) (mul_comm _ _)
  have run := rmulTable_runs (body := body) hcr hdisj hι hT hQ hA
    (hr.update .xs (by simp) words) (by omega) (by omega) rows [(⟨a, 0⟩ : GaussianInt)]
    (by simp) (by intro row hr; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr; rfl)
    (by
      intro x hx
      rw [hflat] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact chirpGammaScaled_fits q l Γ w y (hxs y hy) hw)
    (by
      intro y hy
      have hy' : y = (⟨a, 0⟩ : GaussianInt) := by simpa using hy
      subst y
      exact ⟨chirpRealFactor_fits q w a (ha.trans (by norm_num)) (by omega), rfl⟩)
    (ρ := ρ₁) (by simp only [ρ₁, Function.update_self, hflat]; rfl)
    (by simpa [ρ₁] using hAword) (by simpa [ρ₁] using hxsv)
    (by simpa [ρ₁] using hysv) (by simpa [ρ₁] using hacc)
  rw [hresult, hflat, show shifted.length = xs.length by simp [shifted]] at run
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := cruns_output_exec hcr run v₁ S₁ hc₁ hS₁
  refine ⟨v₂, _, hu₂.trans hu₁, Nat.add_le_add_left hn₂ _, (Exec.seq he₁ he₂).cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  simp only [S₁, Function.update_of_ne (hcr.ne (by decide : CR.out ≠ .xs))]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
