module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearReady
public import IntegerMultBounds.MathlibTM2.Host.StatePlacement

/-! Run the row shear inside a larger column host, preserving all off-bank stacks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T Q A d W b w : ℕ} {P U α : Type} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

theorem columnReady_project (bank : Fin 35 ↪ Fin T) (H J : ℕ) (matrix : Matrix (Fin d) (Fin d) (ZMod M))
    (tail : List (Fin (A+4))) (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (original : Fin (M^d*W) → α) (addr : (Fin d → ZMod M) → Fin d → ZMod M) (S : Stacks T A) :
    ColumnReady bank H J matrix tail sym source dest p q original addr S ↔
      ColumnReady (Function.Embedding.refl _) H J matrix tail sym source dest p q original addr (embStk bank S) := by
  constructor <;> rintro ⟨a,layout,placed⟩ <;> exact ⟨a,⟨layout.modulus,layout.width,layout.one,layout.padded,
    layout.clock,layout.archive,layout.scratch,layout.src,layout.dst⟩,placed⟩

def placedShear (bank : Fin 35 ↪ Fin T) (capacity : 217 ≤ Q) (k t col target pivot : Fin d) (b : ℕ) :
    Pr P T Q A U := statePlacedNormalized bank capacity (by decide) Empty.elim
      (reverseMatrixShear k t b col target pivot (Function.Embedding.refl _))

theorem placedShear_exec (bank : Fin 35 ↪ Fin T) (capacity : 217 ≤ Q) (k t col target pivot : Fin d) (hk : k < t)
    (matrix : Matrix (Fin d) (Fin d) (ZMod M)) (hb : b.Prime) (unit : IsUnit (matrix pivot col))
    (body : P → Pr P T Q A U) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4))) (sym : α → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (original : Fin (M^d*W) → α) (addr : (Fin d → ZMod M) → Fin d → ZMod M)
    (ready : ColumnReady bank H J matrix tail sym source dest p q original addr S) :
    let c := matrix (Equiv.swap col pivot target) col * Ring.inverse (matrix pivot col)
    ∃ z F n, z.user = v.user ∧ n ≤ 1 + reverseRowTime (P := Empty) (A := A) (U := U) Empty.elim
      (Function.Embedding.refl _) k t col target pivot b w W H J ∧
      Exec body (placedShear bank capacity k t col target pivot b) (mk v S) n (mk z F) ∧
      ColumnReady bank H J matrix tail sym source dest p q original
        (fun x => Function.update (addr x) t (addr x t + c * addr x k)) F ∧
      ∀ i, (∀ j, bank j ≠ i) → F.L i = S.L i ∧ F.R i = S.R i := by
  intro c
  have before := (columnReady_project ..).mp ready
  obtain ⟨u,D,n,hu,hn,run,next⟩ := columnReady_shear k t col target pivot hk matrix hb unit (P := Empty)
    Empty.elim (Function.Embedding.refl _) H J hm hw hW (stateLiftDown (by decide : 0 < 217) (embDn bank v))
    (embStk bank S) tail sym source dest p q empty original addr before
  obtain ⟨z,_,hz,placed⟩ := statePlaced_exec_normalized bank bank.injective capacity (by decide) Empty.elim
    (body' := body) (fun e => nomatch e) v S run
  refine ⟨z,_,_,hz.trans hu,Nat.add_le_add_left hn 1,placed,(columnReady_project ..).mpr ?_,fun i hi => embOvr_off _ _ hi⟩
  rwa [embStk_ovr bank.injective]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
