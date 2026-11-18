module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackReverseColumn
public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearReady

/-! Undo a column of the archived matrix using the scheduled row additions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open Matrix GoodForm IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T A d W b w : ℕ} {P U α : Type} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

theorem reverseColumn_ready [Fintype P] (k : Fin d) (rows : Fin d → Fin d)
    (matrix : Matrix (Fin d) (Fin d) (ZMod M)) (hb : b.Prime) (unit : IsUnit (matrix (rows k) k))
    (body : P → Pr P T 217 A U) (bank : Fin 35 ↪ Fin T) (stream : Fin T) (H J : ℕ)
    (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W) (v : HS T 217 A U) (S : Stacks T A)
    (tail rest : List (Fin (A+4))) (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank) (original : Fin (M^d*W) → α)
    (swap : Fin d → Fin d → Pr P T 217 A U) (swapTime : ℕ)
    (addr : (Fin d → ZMod M) → Fin d → ZMod M)
    (code : S.R stream = orderedScheduleCode (((List.finRange d).take (k.val+1)).reverse) rows ++ rest) :
    let pivot := rows k
    let inv := Ring.inverse (matrix pivot k)
    let ready := ColumnReady bank H J matrix tail sym source dest p q original
    let cost := fun i : Fin d => if k < i then reverseRowTime body bank k i k i pivot b w W H J
      else swapTime + reverseRowTime body bank i k k i pivot b w W H J + swapTime
    let add := fun r i => reverseRowAdd k i r b bank (swap i k)
    ready (fun x => stepOp k pivot matrix inv *ᵥ addr x) {S with R := Function.update S.R stream (orderedScheduleCode (((List.finRange d).take k.val).reverse) rows ++ rest)} →
    (∀ i j y u D, ready y D → ∃ z F n, z.user = u.user ∧ n ≤ swapTime ∧
      Exec body (swap i j) (mk u D) n (mk z F) ∧ ready (fun x => y x ∘ Equiv.swap i j) F) →
    ∃ z F n, z.user = v.user ∧ n ≤ 2*(pivot.val+1)+(d-1)*Finset.univ.sup cost+swapTime ∧
      Exec body (reverseColumn stream k add (swap k)) (mk v S) n (mk z F) ∧ ready addr F := by
  intro pivot inv ready cost add initial exchange
  apply reverseColumn_exec body stream k rows matrix inv add (swap k) ready _ swapTime v S rest addr code initial
  · intro i ne y u D ok
    obtain ⟨z,F,n,hz,hn,run,next⟩ := columnReady_add k i pivot ne matrix hb unit body bank H J hm hw hW
      u D tail sym source dest p q empty original (swap i k) swapTime (exchange i k) y ok
    exact ⟨z,F,n,hz,hn.trans (Finset.le_sup (f := cost) (Finset.mem_univ i)),run,next⟩
  · exact exchange k pivot

end IntegerMultBounds.MathlibTM2.Cover.Fallback
