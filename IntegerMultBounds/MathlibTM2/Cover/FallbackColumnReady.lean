module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackReverseColumn
public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearReady

/-! Undo a column of the archived matrix using the scheduled row additions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open Matrix GoodForm IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T A d W b w : ℕ} {P U α : Type} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

def coordinateSwap {Q : ℕ} (ordered : Fin d → Fin d → Pr P T Q A U) (i j : Fin d) : Pr P T Q A U :=
  if i < j then ordered i j else if j < i then ordered j i else .act .done

theorem reverseColumn_ready [Fintype P] (k : Fin d) (rows : Fin d → Fin d)
    (matrix : Matrix (Fin d) (Fin d) (ZMod M)) (hb : b.Prime) (unit : IsUnit (matrix (rows k) k))
    (body : P → Pr P T 217 A U) (bank : Fin 35 ↪ Fin T) (stream : Fin T) (outside : ∀ i, bank i ≠ stream) (H J : ℕ)
    (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W) (v : HS T 217 A U) (S : Stacks T A)
    (tail rest : List (Fin (A+4))) (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank) (original : Fin (M^d*W) → α)
    (ordered : Fin d → Fin d → Pr P T 217 A U) (swapTime : ℕ) (positive : 0 < swapTime)
    (addr : (Fin d → ZMod M) → Fin d → ZMod M)
    (code : S.R stream = orderedScheduleCode (((List.finRange d).take (k.val+1)).reverse) rows ++ rest) :
    let pivot := rows k
    let inv := Ring.inverse (matrix pivot k)
    let ready := ColumnReady bank H J matrix tail sym source dest p q original
    let cost := fun i : Fin d => if k < i then reverseRowTime body bank k i k i pivot b w W H J
      else swapTime + reverseRowTime body bank i k k i pivot b w W H J + swapTime
    let swap := coordinateSwap ordered
    let add := fun r i => reverseRowAdd k i r b bank (swap i k)
    ready (fun x => stepOp k pivot matrix inv *ᵥ addr x) S →
    (∀ i j, i < j → ∀ y u D, ready y D → ∃ z F n, z.user = u.user ∧ n ≤ swapTime ∧
      Exec body (ordered i j) (mk u D) n (mk z F) ∧ ready (fun x => y x ∘ Equiv.swap i j) F) →
    ∃ z F n, z.user = v.user ∧ n ≤ 2*(pivot.val+1)+(d-1)*Finset.univ.sup cost+swapTime ∧
      Exec body (reverseColumn stream k add (swap k)) (mk v S) n (mk z F) ∧ ready addr F := by
  intro pivot inv ready cost swap add initial orderedRun
  have exchange (i j : Fin d) (y) (u : HS T 217 A U) D (ok : ready y D) :
      ∃ z F n, z.user = u.user ∧ n ≤ swapTime ∧ Exec body (swap i j) (mk u D) n (mk z F) ∧
        ready (fun x => y x ∘ Equiv.swap i j) F := by
    rcases lt_trichotomy i j with h | rfl | h
    · simpa [swap,coordinateSwap,h] using orderedRun i j h y u D ok
    · exact ⟨u,D,1,rfl,positive,by simpa [swap,coordinateSwap] using Exec.act (body := body) .done (mk u D),
        by simpa using ok⟩
    · simpa [swap,coordinateSwap,h,h.not_gt,Equiv.swap_comm j i] using orderedRun j i h y u D ok
  apply reverseColumn_exec body stream k rows matrix inv add (swap k) ready _ swapTime v S rest addr code
  · obtain ⟨word,layout,placed⟩ := initial
    refine ⟨word,?_,placed⟩
    rcases layout with ⟨base,width,one,padded,clock,archive,scratch,src,dst⟩
    constructor <;> simp only [Function.update_of_ne (outside _)] <;> assumption
  · intro i ne y u D ok
    obtain ⟨z,F,n,hz,hn,run,next⟩ := columnReady_add k i pivot ne matrix hb unit body bank H J hm hw hW
      u D tail sym source dest p q empty original (swap i k) swapTime (exchange i k) y ok
    exact ⟨z,F,n,hz,hn.trans (Finset.le_sup (f := cost) (Finset.mem_univ i)),run,next⟩
  · exact exchange k pivot

end IntegerMultBounds.MathlibTM2.Cover.Fallback
