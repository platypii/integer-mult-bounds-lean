module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputProductNorm

/-! # Compose both chirp output products and shifts

The E stage feeds normalization directly through an identified intermediate tape.
Both real-factor tables and all private scratch are retained. The two source streams
are owned intermediates; cleanup and final precision reduction are separate stages.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {cr : CR → Fin T} {ι : Fin 64 → Fin T}

def chirpOutputProductsCost (N l Γ w : ℕ) : ℕ :=
  N * (6 * w + 4 * (l + 1) + 14) + 4 + (N * (rmulCost w + 6 * w + 8) + 6) +
    (N * (6 * w + 4 * Γ + 14) + 4 + (N * (rmulCost w + 6 * w + 8) + 6))

/-- Execute both output shifts and products, producing the exact pre-rounding numerators. -/
theorem chirpOutputProducts_exec (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {buf shift rest savedShift savedRest : Fin T}
    (hreg : [cr .xs, buf, shift, rest, savedShift, savedRest].Nodup)
    (q l Γ w : ℕ) (hw : q + l + Γ + 5 ≤ w) (blocks : List (List GaussianInt)) (es : List ℤ) (hes0 : 1 ≤ es.length)
    (hlen : ∀ xs ∈ blocks, xs.length = es.length)
    (hxs : ∀ c ∈ blocks.flatten, ‖value (q + 1) c‖ ≤ 1)
    (hes : ∀ e ∈ es, |(e : ℝ) / 2 ^ q| ≤ 2)
    (ρ : CR → List (Fin (A + 4))) (hr : Ready ρ w q)
    (hX : ρ .xs = cstream A w blocks.flatten)
    (hE : ρ .ys = cstream A w (es.map fun e => (⟨e, 0⟩ : GaussianInt)))
    (hxsv : ρ .xsv = []) (hysv : ρ .ysv = []) (hacc : ρ .acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hc : CClean ι S) (hS : CHolds cr S ρ)
    (hshift : (S.R shift).length = l + 1) (hrest : (S.R rest).length = w - (l + 1))
    (hbuf : S.R buf = []) (hsavedShift : S.R savedShift = []) (hsavedRest : S.R savedRest = [])
    (nr : CR → Fin T) (hnr : Function.Injective nr) (hndisj : ∀ r j, nr r ≠ ι j)
    (hlink : nr .xs = cr .out) (hnframe : ∀ r, nr r ≠ cr .xs)
    (a : ℤ) (ha : |(a : ℝ) / 2 ^ q| ≤ 1)
    (ν : CR → List (Fin (A + 4))) (hnready : Ready ν w q) (hnS : CHolds nr S ν)
    (hnA : ν .ys = csyms A w (⟨a, 0⟩ : GaussianInt))
    (hnxsv : ν .xsv = []) (hnysv : ν .ysv = []) (hnacc : ν .acc = [])
    (hout : ρ .out = [])
    (nbuf nshift nrest nsavedShift nsavedRest : Fin T)
    (hnreg : [nr .xs, nbuf, nshift, nrest, nsavedShift, nsavedRest].Nodup)
    (hnwork : ∀ k ∈ [nbuf, nshift, nrest, nsavedShift, nsavedRest], k ≠ cr .xs ∧ k ≠ cr .out)
    (hnshift : (S.R nshift).length = Γ) (hnrest : (S.R nrest).length = w - Γ)
    (hnbuf : S.R nbuf = []) (hnsavedShift : S.R nsavedShift = []) (hnsavedRest : S.R nsavedRest = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ chirpOutputProductsCost blocks.flatten.length l Γ w ∧
      Exec body
        (.seq
          (.seq (shiftInto (cr .xs) buf (cr .xs) shift rest savedShift savedRest (pairSym A false false))
            (cmulTable cr (rmulOne ι hι hT hQ cr)))
          (.seq (shiftInto (nr .xs) nbuf (nr .xs) nshift nrest nsavedShift nsavedRest (pairSym A false false))
            (cmulTable nr (rmulOne ι hι hT hQ nr)))) (mk v S) n
        (mk v' { S with R := (Function.update
          (Function.update
            (Function.update S.R (cr .xs) (cstream A w (blocks.flatten.map fun c => (2 : GaussianInt) ^ (l + 1) * c)))
            (nr .xs) (cstream A w ((blocks.flatMap (fun xs => List.zipWith (chirpOutputEProduct q l) xs es)).map
              (fun x => (2 : GaussianInt) ^ Γ * x))))
          (nr .out) (cstream A w (blocks.flatMap (fun xs => List.zipWith (fun c e => chirpOutputNumerator q l Γ c e a) xs es)) ++
            S.R (nr .out))) }) := by
  let products := blocks.flatMap (fun xs => List.zipWith (chirpOutputEProduct q l) xs es)
  let scaled := cstream A w (blocks.flatten.map fun c => (2 : GaussianInt) ^ (l + 1) * c)
  let prodWords := cstream A w products
  have hout0 : S.R (cr .out) = [] := (hS .out).trans hout
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := chirpOutputETable_exec (body := body) hcr hdisj hι hT hQ hA hreg
    q l w (by omega) blocks es hes0 hlen hxs hes ρ hr hX hE hxsv hysv hacc
    v S hc hS hshift hrest hbuf hsavedShift hsavedRest
  let Sbase : Stacks T A := { S with R := Function.update S.R (cr .xs) scaled }
  let S₁ : Stacks T A := { Sbase with R := Function.update Sbase.R (cr .out) prodWords }
  have he₁' : Exec body (.seq
      (shiftInto (cr .xs) buf (cr .xs) shift rest savedShift savedRest (pairSym A false false))
      (cmulTable cr (rmulOne ι hι hT hQ cr))) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hout0, List.append_nil] using he₁
  have hnbase : CHolds nr Sbase ν := by
    intro r
    simpa only [Sbase, Function.update_of_ne (hnframe r)] using hnS r
  let ν₁ := Function.update ν CR.xs prodWords
  have hnS₁ : CHolds nr S₁ ν₁ := by
    change CHolds nr { Sbase with R := Function.update Sbase.R (cr .out) prodWords } ν₁
    rw [← hlink]
    exact holds_upd hnr hnbase .xs prodWords
  have off (k : Fin T) (hk : k ≠ cr .xs ∧ k ≠ cr .out) : S₁.R k = S.R k := by
    simp only [S₁, Sbase, Function.update_of_ne hk.1, Function.update_of_ne hk.2]
  have hc₁ : CClean ι S₁ := fun j => ⟨(hc j).1,
    (off _ ⟨(hdisj .xs j).symm, (hdisj .out j).symm⟩).trans (hc j).2⟩
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := chirpOutputNormalize_exec (body := body) hnr hndisj hι hT hQ hA hnreg
    q l Γ w hw products a (chirpOutputEBlocks_norm q l blocks es hxs hes) ha ν₁
    (hnready.update .xs (by simp) prodWords) (by simp only [ν₁, Function.update_self]; rfl)
    (by simpa [ν₁] using hnA) (by simpa [ν₁] using hnxsv)
    (by simpa [ν₁] using hnysv) (by simpa [ν₁] using hnacc)
    v₁ S₁ hc₁ hnS₁
    (by rw [off _ (hnwork nshift (by simp))]; exact hnshift)
    (by rw [off _ (hnwork nrest (by simp))]; exact hnrest)
    (by rw [off _ (hnwork nbuf (by simp))]; exact hnbuf)
    (by rw [off _ (hnwork nsavedShift (by simp))]; exact hnsavedShift)
    (by rw [off _ (hnwork nsavedRest (by simp))]; exact hnsavedRest)
  have hlenProd : products.length = blocks.flatten.length := by
    simp only [products, List.length_flatMap, List.length_flatten]
    congr 1
    apply List.map_congr_left
    intro xs hx
    simp only [List.length_zipWith, hlen xs hx, Nat.min_self]
  have hresult : products.map (fun x => chirpOutputNormalize q Γ x a) =
      blocks.flatMap (fun xs => List.zipWith (fun c e => chirpOutputNumerator q l Γ c e a) xs es) := by
    simp only [products, List.map_flatMap, List.map_zipWith, chirpOutputNormalize_EProduct]
  rw [hlenProd] at hn₂
  refine ⟨v₂, n₁ + n₂, hu₂.trans hu₁, Nat.add_le_add hn₁ hn₂,
    (Exec.seq he₁' he₂).cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  simp only [S₁, Sbase, hresult, hlink,
    Function.update_of_ne (show nr CR.out ≠ cr CR.out by rw [← hlink]; exact hnr.ne (by decide)),
    Function.update_of_ne (hnframe .out), Function.update_idem]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
