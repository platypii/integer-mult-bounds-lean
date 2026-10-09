import IntegerMultBounds.ExactRecovery
import IntegerMultBounds.NLogN.Carry

/-! Exact-width output from recovered coefficients. Carry normalization may
produce more than twice the input length; the proven product bound justifies
removing that leading padding. These are output semantics, not a tape compiler
or a runtime bound for carry propagation. -/
namespace IntegerMultBounds.ExactRecoveryOutput
noncomputable section
open Machine NLogN

/-- If the value fits in the retained suffix, every discarded leading bit is
zero and dropping it preserves the represented integer. -/
theorem binaryValue_drop (bs : List Bool) (m : ℕ) (hm : m ≤ bs.length)
    (hfit : binaryValue bs < 2^(bs.length-m)) :
    binaryValue (bs.drop m) = binaryValue bs := by
  induction m generalizing bs with
  | zero => simp
  | succ m ih =>
    cases bs with
    | nil => simp at hm
    | cons b bs =>
      have hm' : m ≤ bs.length := by simpa using hm
      have he : (b::bs).length-(m+1) = bs.length-m := by simp
      rw [he] at hfit
      cases b with
      | false =>
        have hf : binaryValue bs < 2^(bs.length-m) := by simpa [binaryValue] using hfit
        simpa [binaryValue] using ih bs hm' hf
      | true =>
        have hp : 2^(bs.length-m) ≤ 2^bs.length :=
          Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
        simp only [binaryValue,ite_true,one_mul] at hfit
        omega

/-- Number of complete chunks needed for the exact output width. -/
def chunkCount (k n : ℕ) : ℕ := (2*n+k-1)/k

theorem chunkCount_covers {k : ℕ} (hk : 0 < k) (n : ℕ) :
    2*n ≤ k*chunkCount k n := by
  have hm := Nat.mod_lt (2*n+k-1) hk
  have hd := Nat.mod_add_div (2*n+k-1) k
  unfold chunkCount
  omega

/-- Carry normalization followed by removal of excess leading padding. -/
def output (k L n : ℕ) (ds : List ℕ) : List Bool :=
  (toBits k L ds).drop (k*L-2*n)

/-- Recovered coefficients of an n-bit product give exactly 2n output bits,
even when the input length is not divisible by the chunk width. -/
theorem output_spec {k L n : ℕ} (hk : 0 < k) (hwidth : 2*n ≤ k*L)
    {x y : List Bool} (hx : x.length = n) (hy : y.length = n) (ds : List ℕ)
    (hcorrect : evalBase (2^k) ds = binaryValue x*binaryValue y) :
    (output k L n ds).length = 2*n ∧
      binaryValue (output k L n ds) = binaryValue x*binaryValue y := by
  have hfit := product_fits hx hy
  have hcap : 2^(2*n) ≤ (2^k)^L := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) hwidth
  have hds : evalBase (2^k) ds < (2^k)^L := by rw [hcorrect]; exact hfit.trans_le hcap
  obtain ⟨hvalue,hlen⟩ := binaryValue_toBits hk hds
  have hd : (toBits k L ds).length-(k*L-2*n) = 2*n := by rw [hlen]; omega
  refine ⟨by simpa only [output,List.length_drop] using hd,?_⟩
  unfold output
  rw [binaryValue_drop _ _ (by rw [hlen]; omega)]
  · exact hvalue.trans hcorrect
  · rw [hd,hvalue,hcorrect]
    exact hfit

/-- The canonical chunk count covers every input length. -/
theorem output_spec_chunks {k n : ℕ} (hk : 0 < k)
    {x y : List Bool} (hx : x.length = n) (hy : y.length = n) (ds : List ℕ)
    (hcorrect : evalBase (2^k) ds = binaryValue x*binaryValue y) :
    (output k (chunkCount k n) n ds).length = 2*n ∧
      binaryValue (output k (chunkCount k n) n ds) = binaryValue x*binaryValue y :=
  output_spec hk (chunkCount_covers hk n) hx hy ds hcorrect

/-- The exact list-level result discharges the literal machine output contract
when that word is installed on the designated output tape. -/
theorem outputCorrect_of_recovered {t q a k L n : ℕ} (M : Program t q a)
    (c : Config t q a) (hk : 0 < k) (hwidth : 2*n ≤ k*L)
    {x y : List Bool} (hx : x.length = n) (hy : y.length = n) (ds : List ℕ)
    (hcorrect : evalBase (2^k) ds = binaryValue x*binaryValue y)
    (htape : c.tape ⟨0,M.tapes_pos⟩ = wordTape ((output k L n ds).map bitSymbol)) :
    outputCorrect M n x y c := by
  obtain ⟨hlen,hvalue⟩ := output_spec hk hwidth hx hy ds hcorrect
  exact ⟨output k L n ds,hlen,hvalue,htape⟩


section Computed
variable {κ : Type*} [Fintype κ] {S p k : ℕ} [NeZero S] {Es : ℝ}
  (F : (ZMod S → ℂ) →L[ℂ] (κ → ℂ)) (F' : (ZMod S → ℂ) → (κ → ℂ))
  (G : (κ → ℂ) →L[ℂ] (ZMod S → ℂ)) (G' : (κ → ℂ) → (ZMod S → ℂ))

/-- The actual rounded coefficient list from the computed convolution. -/
def coefficients (x y : List Bool) : List ℕ := List.ofFn fun i : Fin S =>
  (round (((2 : ℂ)^(2*k)*S)*
    ExactRecovery.computedConv (p := p) (k := k) F' G' x y (i.val : ZMod S)).re).toNat

variable (hk : 0 < k) {x y : List Bool}
  (hS : (digitsOf k x).length+(digitsOf k y).length ≤ S+1)
  (hF : ‖F‖ ≤ 1)
  (hF' : ∀ u : ZMod S → ℂ, ‖u‖ ≤ 1/2 → 2^p*‖F' u-F u‖ ≤ Es)
  (hG : ‖G‖ ≤ 1)
  (hG' : ∀ v : κ → ℂ, ‖v‖ ≤ 1/2 → 2^p*‖G' v-G v‖ ≤ Es)
  (hEs : Es ≤ 2^p/100)
  (hconv : ∀ u v : ZMod S → ℂ,
    G (fun j => F u j*F v j) = fun i => cconv u v i/(S : ℂ)^2)
  (hfinal : (2 : ℝ)^(2*k+4)*S^2*(3*Es+2) < 2^p/2)

include hk hS hF hF' hG hG' hEs hconv hfinal in
/-- The numerical recovery theorem instantiated at the required literal
output length, with no additional coefficient-correctness assumption. -/
theorem computed_output_spec {L n : ℕ} (hwidth : 2*n ≤ k*L)
    (hx : x.length = n) (hy : y.length = n) :
    (output k L n (coefficients (p := p) (k := k) F' G' x y)).length = 2*n ∧
      binaryValue (output k L n (coefficients (p := p) (k := k) F' G' x y)) =
        binaryValue x*binaryValue y := by
  have hcorrect := ExactRecovery.exact_product F F' G G' hk hS hF hF' hG hG' hEs hconv hfinal
  exact output_spec hk hwidth hx hy _ hcorrect

include hk hS hF hF' hG hG' hEs hconv hfinal in
/-- Once the normalized recovered word is physically installed at tape zero,
its semantics are exactly the EndToEnd output contract. Installation and
runtime remain separate proof obligations. -/
theorem outputCorrect_of_computed {t q a L n : ℕ} (M : Program t q a)
    (c : Config t q a) (hwidth : 2*n ≤ k*L) (hx : x.length = n) (hy : y.length = n)
    (htape : c.tape ⟨0,M.tapes_pos⟩ = wordTape
      ((output k L n (coefficients (p := p) (k := k) F' G' x y)).map bitSymbol)) :
    outputCorrect M n x y c := by
  obtain ⟨hlen,hvalue⟩ := computed_output_spec F F' G G' hk hS hF hF' hG hG' hEs hconv hfinal hwidth hx hy
  exact ⟨output k L n (coefficients (p := p) (k := k) F' G' x y),hlen,hvalue,htape⟩

end Computed

end
end IntegerMultBounds.ExactRecoveryOutput
