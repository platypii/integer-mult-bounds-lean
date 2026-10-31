module

public import IntegerMultBounds.MathlibTM2.Host.WordCmd
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.Host.RegisterBankStock

/-! Exact stock balance for arbitrary placed word banks. Both halves of every
word tape include their separators; spectator host storage is counted once. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host.WordCmd
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Schoenhage (WTape clen)
variable {t T Q A : ℕ} {U : Type}

def wordBankStock (τ : Fin t → WTape) : ℕ := ∑ i, (clen (τ i).left+clen (τ i).right)

/-- Placing a different word bank changes stock by exactly the bank difference. -/
theorem place_stock_balance (ι : Fin t → Fin T) (hι : Function.Injective ι)
    (v w : HS T Q A U) (S : Stacks T A) (σ τ : Fin t → WTape) :
    mnSize (mk v (place S ι σ))+wordBankStock τ =
      mnSize (mk w (place S ι τ))+wordBankStock σ := by
  have h := sum_replace_embedding ι hι
    (fun j => ((place S ι σ).L j).length+((place S ι σ).R j).length)
    (fun j => ((place S ι τ).L j).length+((place S ι τ).R j).length)
    (fun i => clen (σ i).left+clen (σ i).right) (by
      intro i
      simp only [place_L_at hι,place_R_at hι,length_lcells,Schoenhage.length_cells]) (by
      intro j hj
      have hoff : ∀ i, ι i ≠ j := by simpa only [not_exists] using hj
      rw [place_L_off _ _ hoff,place_R_off _ _ hoff,place_L_off _ _ hoff,place_R_off _ _ hoff])
  simp only [place_L_at hι,place_R_at hι,length_lcells,Schoenhage.length_cells] at h
  rw [mnSize_mk_registerBankStock,mnSize_mk_registerBankStock]
  change S.inp.length+S.out.length+registerBankStock (place S ι σ)+wordBankStock τ =
    S.inp.length+S.out.length+registerBankStock (place S ι τ)+wordBankStock σ
  change registerBankStock (place S ι σ)+wordBankStock τ =
    registerBankStock (place S ι τ)+wordBankStock σ at h
  omega

/-- One word-tape update has an exact stock balance, with no tape enumeration. -/
theorem wordBankStock_update (τ : Fin t → WTape) (i : Fin t) (x : WTape) :
    wordBankStock (Function.update τ i x)+(clen (τ i).left+clen (τ i).right) =
      wordBankStock τ+(clen x.left+clen x.right) := by
  have h := sum_replace_embedding (fun _ : Fin 1 => i) (Function.injective_of_subsingleton _)
    (fun j => clen (Function.update τ i x j).left+clen (Function.update τ i x j).right)
    (fun j => clen (τ j).left+clen (τ j).right)
    (fun _ => clen x.left+clen x.right) (by intro j; simp) (by
      intro j hj
      have hji : j ≠ i := by intro h; exact hj ⟨0,h.symm⟩
      simp only [Function.update_of_ne hji])
  simpa only [wordBankStock,Fin.sum_univ_one] using h

end IntegerMultBounds.MathlibTM2.Host.WordCmd
