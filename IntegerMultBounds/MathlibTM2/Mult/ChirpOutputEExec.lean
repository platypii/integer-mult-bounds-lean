module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpScaleExec
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputBounds
public import IntegerMultBounds.MathlibTM2.Mult.ChirpWeightedExec

/-! # Execute the correlation scale and normalized E product

The correlation stream is shifted in place; one real table traversal emits the
first output product. Counter and multiplier scratch restoration is exact. Signed fit
of both inputs follows from the decoded correlation/factor bounds and the word envelope.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {cr : CR → Fin T} {ι : Fin 64 → Fin T}

/-- Integer numerators after scaling the correlation and multiplying normalized E. -/
def chirpOutputEProduct (q l : ℕ) (c : GaussianInt) (e : ℤ) : GaussianInt :=
  tdivN q ((⟨e, 0⟩ : GaussianInt) * ((2 : GaussianInt) ^ (l + 1) * c))

/-- Execute the first two output operations, retaining both the shifted stream and E table. -/
theorem chirpOutputETable_exec (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {buf shift rest savedShift savedRest : Fin T}
    (hreg : [cr .xs, buf, shift, rest, savedShift, savedRest].Nodup)
    (q l w : ℕ) (hw : q + l + 4 ≤ w) (blocks : List (List GaussianInt)) (es : List ℤ) (hes0 : 1 ≤ es.length)
    (hlen : ∀ xs ∈ blocks, xs.length = es.length)
    (hxs : ∀ c ∈ blocks.flatten, ‖value (q + 1) c‖ ≤ 1)
    (hes : ∀ e ∈ es, |(e : ℝ) / 2 ^ q| ≤ 2)
    (ρ : CR → List (Fin (A + 4))) (hr : Ready ρ w q)
    (hX : ρ .xs = cstream A w blocks.flatten)
    (hE : ρ .ys = cstream A w (es.map fun e => (⟨e, 0⟩ : GaussianInt)))
    (hxsv : ρ .xsv = []) (hysv : ρ .ysv = []) (hacc : ρ .acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hc : CClean ι S) (hS : CHolds cr S ρ)
    (hshift : (S.R shift).length = l + 1) (hrest : (S.R rest).length = w - (l + 1))
    (hbuf : S.R buf = []) (hsavedShift : S.R savedShift = []) (hsavedRest : S.R savedRest = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ blocks.flatten.length * (6 * w + 4 * (l + 1) + 14) + 4 +
        (blocks.flatten.length * (rmulCost w + 6 * w + 8) + 6) ∧
      Exec body
        (.seq (shiftInto (cr .xs) buf (cr .xs) shift rest savedShift savedRest (pairSym A false false))
          (cmulTable cr (rmulOne ι hι hT hQ cr))) (mk v S) n
        (mk v' { S with R := (Function.update
          (Function.update S.R (cr .xs) (cstream A w (blocks.flatten.map fun c => (2 : GaussianInt) ^ (l + 1) * c)))
          (cr .out) (cstream A w (blocks.flatMap (fun xs => List.zipWith (chirpOutputEProduct q l) xs es)) ++ S.R (cr .out))) }) := by
  let shifted := blocks.flatten.map fun c => (2 : GaussianInt) ^ (l + 1) * c
  let words := cstream A w shifted
  obtain ⟨v₁, hu₁, he₁⟩ := chirpScale_exec (body := body) hreg w (l + 1) (by omega) (by omega) blocks.flatten
    v S ((hS .xs).trans hX) hshift hrest hbuf hsavedShift hsavedRest
  let S₁ : Stacks T A := { S with R := Function.update S.R (cr .xs) words }
  let ρ₁ := Function.update ρ CR.xs words
  have hS₁ : CHolds cr S₁ ρ₁ := holds_upd hcr hS .xs words
  have hc₁ : CClean ι S₁ := fun r => ⟨(hc r).1,
    (Function.update_of_ne (hdisj .xs r).symm _ _).trans (hc r).2⟩
  let shiftedBlocks := blocks.map (fun xs => xs.map fun c => (2 : GaussianInt) ^ (l + 1) * c)
  have hflat : shiftedBlocks.flatten = shifted := by simp [shiftedBlocks, shifted]
  have hxy : tableOut (fun x y => tdivN q (x * y)) shiftedBlocks
      (es.map fun e => (⟨e, 0⟩ : GaussianInt)) =
      blocks.flatMap (fun xs => List.zipWith (chirpOutputEProduct q l) xs es) := by
    simp only [tableOut, shiftedBlocks, List.flatMap_map, List.zipWith_map]
    congr 1
    funext xs
    congr 1
    funext c e
    exact congrArg (tdivN q) (mul_comm _ _)
  have run := rmulTable_runs (body := body) hcr hdisj hι hT hQ hA
    (hr.update .xs (by simp) words) (by omega) (by omega) shiftedBlocks
    (es.map fun e => (⟨e, 0⟩ : GaussianInt)) (by simpa using hes0)
    (by
      intro xs hx
      obtain ⟨ys, hy, rfl⟩ := List.mem_map.mp hx
      simpa only [List.length_map] using hlen ys hy)
    (by
      intro x hx
      rw [hflat] at hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact chirpScaledCorrelation_fits q l w c (hxs c hc) hw)
    (by
      intro y hy
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
      exact ⟨chirpRealFactor_fits q w e (hes e he) (by omega), rfl⟩)
    (ρ := ρ₁) (by simp only [ρ₁, Function.update_self, hflat]; rfl) (by simpa [ρ₁] using hE)
    (by simpa [ρ₁] using hxsv) (by simpa [ρ₁] using hysv) (by simpa [ρ₁] using hacc)
  rw [hxy, hflat, show shifted.length = blocks.flatten.length by simp [shifted, Function.comp_def]] at run
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
