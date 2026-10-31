module

public import IntegerMultBounds.MathlibTM2.Host.WordBankStock
public import IntegerMultBounds.Schoenhage.RingPointwise

/-! The prepared pointwise bank has shared scalar stock plus a linear operand
allowance. Structural assignment accounting avoids expanding the tape bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host.WordCmd
open IntegerMultBounds.Schoenhage IntegerMultBounds.Schoenhage.Tp
  IntegerMultBounds.Schoenhage.Strm

/-- Unary constants, the ruler, masks and two fixed packed words. -/
def ringConstantStock (p l w : ℕ) : ℕ :=
  let W := wOf p l w
  p+l+w+3*W+3*(W*2^l)+2*2^l*(W+2)+13

def ringSharedBankStock (p l w H : ℕ) : ℕ :=
  H+p+l+w+ringConstantStock p l w+2*2^l+10

private theorem decodedBank_stock_le (p l w : ℕ) (hdr F G : List Bool) :
    let τ := Function.update (Function.update (Function.update (startBank hdr F G)
      iP (reg (ones p))) iL (reg (ones l))) iW (reg (ones w))
    wordBankStock τ ≤ hdr.length+F.length+G.length+p+l+w+6 := by
  let xs : List (Fin 𝕌 × WTape) := [(zH,reg hdr),(zF,reg F),(zG,reg G),
    (iP,reg (ones p)),(iL,reg (ones l)),(iW,reg (ones w))]
  have h := wordBankStock_updates_le (fun _ : Fin 𝕌 => emp) xs
  change wordBankStock _ ≤ _
  convert h using 1 <;> simp [xs,wordBankStock,emp,reg,startBank,clen_cons,length_ones]
  omega

private theorem constantBank_stock_le (p l w : ℕ) (τ : Fin 𝕌 → WTape) :
    wordBankStock (constBank p l w τ) ≤ wordBankStock τ+ringConstantStock p l w := by
  let W := wOf p l w
  let xs : List (Fin 𝕌 × WTape) := [
    (kS,reg (ones (p+l))),(kw,reg (ones w)),(kW,reg (ones W)),(kN,reg (ones (W*2^l))),
    (kR,reg (Rules.ruler W (W+1) (2^l))),(kH,reg (bits (W+1) (2^(W-1)))),
    (kC,reg (bits (W+1) (2^(p+l)-1))),
    (kO,reg (rwd (W*2^l) (wsum W (List.replicate (2^l) (2^(W-1)))))),
    (kI,reg (rwd (W*2^l) (wsum W (List.replicate (2^l) (2^(w-1))))))]
  have h := wordBankStock_updates_le τ xs
  change wordBankStock (constBank p l w τ) ≤
    wordBankStock τ+(xs.map (fun x => clen x.2.left+clen x.2.right)).sum at h
  simp only [xs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,reg,clen_cons,clen_nil,
    length_ones,length_bits,rwd_length] at h
  have hr := length_ruler (show W+1 ≤ W+1 from le_rfl) (2^l)
  simp only [Nat.add_assoc] at hr
  dsimp only [ringConstantStock]
  dsimp only [W] at h hr
  nlinarith only [h,hr]

/-- Bits enter only through their lengths; all scalar storage is shared. -/
theorem pwPreparedBank_stock_le (p l w : ℕ) (hw : 1 ≤ w) (hdr F G : List Bool) :
    wordBankStock (pwPreparedBank p l w hdr F G) ≤
      4*(F.length+G.length)+ringSharedBankStock p l w hdr.length := by
  let τ₁ := Function.update (Function.update (Function.update (startBank hdr F G)
    iP (reg (ones p))) iL (reg (ones l))) iW (reg (ones w))
  let τ₂ := constBank p l w τ₁
  have hd : wordBankStock τ₁ ≤ hdr.length+F.length+G.length+p+l+w+6 :=
    decodedBank_stock_le p l w hdr F G
  have hc := constantBank_stock_le p l w τ₁
  let xs : List (Fin 𝕌 × WTape) := [
    (iW,reg (ones (2*2^l))),(iP,⟨[],cut w F⟩),(iL,⟨[],cut w G⟩),
    (zF,⟨[F],[]⟩),(zG,⟨[G],[]⟩),(zO,⟨[[]],[]⟩)]
  have h := wordBankStock_updates_le τ₂ xs
  change wordBankStock (pwPreparedBank p l w hdr F G) ≤
    wordBankStock τ₂+(xs.map (fun x => clen x.2.left+clen x.2.right)).sum at h
  simp only [xs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,reg,clen_cons,clen_nil,List.length_nil,length_ones] at h
  have hf := clen_cut_le w hw _ F le_rfl
  have hg := clen_cut_le w hw _ G le_rfl
  change wordBankStock τ₂ ≤ wordBankStock τ₁+ringConstantStock p l w at hc
  dsimp only [ringSharedBankStock]
  omega

end IntegerMultBounds.MathlibTM2.Fast
