module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputProductsExec
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputStream
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputFinish

/-! # Complete output arithmetic with intermediate erasure

Both products feed the actual signed rounding/crop pass. The shifted correlation
and E-product streams are owned and erased; every other working register is
restored. Only the consumed correlation source and final output change.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {cr : CR → Fin T} {ι : Fin 64 → Fin T}

def chirpOutputFinishCost (N p q l Γ w t : ℕ) : ℕ :=
  (1 + (N * (topShiftWordCost w (q - p) (p + l + Γ + 5) + 1) + 1) +
    (2 * (N * (p + l + Γ + 5)) + 2)) +
    (6 * ((min t N) * (p + l + Γ + 5)) +
      2 * ((N - t) * (p + l + Γ + 5)) + 8)

def chirpOutputCompleteCost (N p q l Γ w t : ℕ) : ℕ :=
  chirpOutputProductsCost N l Γ w + chirpOutputFinishCost N p q l Γ w t + 4 * N * w + 5

/-- Run all output arithmetic and erase both shifted intermediate streams. -/
theorem chirpOutputComplete_exec (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
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
    (hnbuf : S.R nbuf = []) (hnsavedShift : S.R nsavedShift = []) (hnsavedRest : S.R nsavedRest = [])
    (p t : ℕ) (hpq : p ≤ q) (hnout : ν .out = [])
    {rdst rtmp cW cS cE cD rsp rsg rcy count cropSaved cropTmp : Fin T}
    (hround : [nr .out, rdst, rtmp, cW, cS, cE, cD, rsp, rsg, rcy].Nodup)
    (hcrop : [count, nr .out, cropSaved, cropTmp].Nodup)
    (hfinishOff : ∀ k ∈ [rdst, rtmp, cW, cS, cE, cD, rsp, rsg, rcy, count, cropSaved, cropTmp],
      k ≠ cr .xs ∧ k ≠ nr .xs ∧ k ≠ nr .out)
    (hrdst : S.R rdst = [])
    (hroundG : topShiftG rtmp cW cS cE cD rsp rsg rcy w (q - p) (p + l + Γ + 5) S.R)
    (hcount : (S.R count).length = min t blocks.flatten.length * (p + l + Γ + 5))
    (hcropSaved : S.R cropSaved = []) (hcropTmp : S.R cropTmp = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ chirpOutputCompleteCost blocks.flatten.length p q l Γ w t ∧
      Exec body
        (.seq (.seq
          (.seq (shiftInto (cr .xs) buf (cr .xs) shift rest savedShift savedRest (pairSym A false false))
            (cmulTable cr (rmulOne ι hι hT hQ cr)))
          (.seq (shiftInto (nr .xs) nbuf (nr .xs) nshift nrest nsavedShift nsavedRest (pairSym A false false))
            (cmulTable nr (rmulOne ι hι hT hQ nr))))
          (.seq (.seq
            (topPass (nr .out) rdst (topShiftWord (nr .out) rdst rtmp cW cS cE cD rsp rsg rcy))
            (chirpCrop count (nr .out) cropSaved cropTmp))
            (clearWords [cr .xs, nr .xs]))) (mk v S) n
        (mk v' { S with R := (Function.update (Function.update S.R (cr .xs) []) (nr .out)
          (cstream A (p + l + Γ + 5)
            (((chirpOutputNumerators q l Γ blocks es a).take t).map (tdivN (q - p))))) }) := by
  let nums := chirpOutputNumerators q l Γ blocks es a
  let scaled := cstream A w (blocks.flatten.map fun c => (2 : GaussianInt) ^ (l + 1) * c)
  let shifted := cstream A w ((blocks.flatMap (fun xs => List.zipWith (chirpOutputEProduct q l) xs es)).map
    (fun x => (2 : GaussianInt) ^ Γ * x))
  have hlenNums : nums.length = blocks.flatten.length :=
    chirpOutputNumerators_length q l Γ blocks es a hlen
  have hneInput : cr .xs ≠ nr .xs := (hnframe .xs).symm
  have hneOut : nr .out ≠ cr .xs := hnframe .out
  have hneMid : nr .out ≠ nr .xs := hnr.ne (by decide)
  have hmid0 : S.R (nr .xs) = [] := by rw [hlink]; exact (hS .out).trans hout
  have hout0 : S.R (nr .out) = [] := (hnS .out).trans hnout
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := chirpOutputProducts_exec (body := body)
    hcr hdisj hι hT hQ hA hreg q l Γ w hw blocks es hes0 hlen hxs hes
    ρ hr hX hE hxsv hysv hacc v S hc hS hshift hrest hbuf hsavedShift hsavedRest
    nr hnr hndisj hlink hnframe a ha ν hnready hnS hnA hnxsv hnysv hnacc hout
    nbuf nshift nrest nsavedShift nsavedRest hnreg hnwork hnshift hnrest hnbuf hnsavedShift hnsavedRest
  let S₁ : Stacks T A := { S with R := (Function.update
    (Function.update (Function.update S.R (cr .xs) scaled) (nr .xs) shifted)
      (nr .out) (cstream A w nums)) }
  have he₁' : Exec body (.seq
          (.seq (shiftInto (cr .xs) buf (cr .xs) shift rest savedShift savedRest (pairSym A false false))
            (cmulTable cr (rmulOne ι hι hT hQ cr)))
          (.seq (shiftInto (nr .xs) nbuf (nr .xs) nshift nrest nsavedShift nsavedRest (pairSym A false false))
            (cmulTable nr (rmulOne ι hι hT hQ nr)))) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [S₁, scaled, shifted, nums, chirpOutputNumerators, hout0, List.append_nil] using he₁
  have off (k : Fin T) (hk : k ≠ cr .xs ∧ k ≠ nr .xs ∧ k ≠ nr .out) : S₁.R k = S.R k := by
    simp only [S₁, Function.update_of_ne hk.1, Function.update_of_ne hk.2.1,
      Function.update_of_ne hk.2.2]
  have hg₁ : topShiftG rtmp cW cS cE cD rsp rsg rcy w (q - p) (p + l + Γ + 5) S₁.R := by
    rcases hroundG with ⟨hW, hS, hE, hD, hsp, hsg, hcy, htmp⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (rwa [off _ (hfinishOff _ (by simp))])
  obtain ⟨v₂, hu₂, he₂⟩ := chirpOutputFinish_exec (body := body) (by omega) hround hcrop
    p q l Γ w t hpq hw nums (chirpOutputNumerators_norm q l Γ blocks es a hxs hes ha)
    v₁ S₁ (by simp [S₁])
    ((off _ (hfinishOff _ (by simp))).trans hrdst) hg₁
    (by rw [off _ (hfinishOff _ (by simp)), hlenNums]; exact hcount)
    ((off _ (hfinishOff _ (by simp))).trans hcropSaved)
    ((off _ (hfinishOff _ (by simp))).trans hcropTmp)
  let output := cstream A (p + l + Γ + 5) ((nums.take t).map (tdivN (q - p)))
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (nr .out) output }
  have hscaled : S₂.R (cr .xs) = scaled := by
    simp [S₂, S₁, hneInput, hneOut.symm]
  have hshifted : S₂.R (nr .xs) = shifted := by
    simp [S₂, S₁, hneMid.symm]
  have hshiftedLen : shifted.length = blocks.flatten.length * w := by
    simp only [shifted, length_cstream, List.length_map, List.length_flatMap, List.length_flatten]
    congr 1
    congr 1
    apply List.map_congr_left
    intro xs hx
    simp only [List.length_zipWith, hlen xs hx, Nat.min_self]
  obtain ⟨v₃, hu₃, he₃⟩ := clearWords_exec (body := body) [cr .xs, nr .xs]
    (by simp [hneInput]) v₂ S₂
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), ?_, (Exec.seq he₁' (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil, hscaled, hshifted, hshiftedLen, scaled, length_cstream, List.length_map]
    change n₁ + (chirpOutputFinishCost nums.length p q l Γ w t + _) ≤ _
    rw [hlenNums]
    unfold chirpOutputCompleteCost
    simp only [Nat.mul_assoc]
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₁' he₂ he₃
    funext k
    by_cases hx : k = cr .xs
    · subst k
      simp [hneOut.symm]
    by_cases hm : k = nr .xs
    · subst k
      simp [hneInput.symm, hneMid.symm, hmid0]
    by_cases ho : k = nr .out
    · subst k
      simp [hx, hm, S₂, S₁, output, nums, List.map_take]
    · simp [hx, hm, ho, S₂, S₁]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
