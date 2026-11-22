module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepSelectorLoop

/-! One complete destination cycle restores the radix counter and matrix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Node RadixDigits RadixCounterData Routing

theorem sweepSelectorCycle_exec {T Q q L M : ℕ} {P U : Type} (body : P → Pr P T Q q U)
    (hq : 2 ≤ q) (pos : 0 < L) (size : M = q^L) (r : Fin 7 ↪ Fin T)
    (matrix count saved : Fin T) (apart : ∀ i, r i ≠ matrix) (ports : [matrix,count,saved].Nodup)
    (outside : ∀ i, r i ≠ count ∧ r i ≠ saved) (H cost : ℕ) (source : Fin M → Fin M)
    (mat : Fin M → List (Fin (q+4))) (evaluate : Pr P T Q q U) (v : HS T Q q U) (S : Stacks T q)
    (counter : S.R (r 0) = (zeros hq L).map digitSymbol) (width : (S.R (r 5)).length = L)
    (ticks : (S.R count).length = M) (blank : S.R (r 2) = [])
    (free : ∀ i : Fin 7, i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 6 → S.R (r i) = []) :
    let last : Fin M := ⟨M-1,by have : 0 < M := size ▸ pow_pos (by omega) _; omega⟩
    S.R matrix = mat last →
    (∀ old dest (ds : List (Fin q)), ds.length = L → value ds = dest.val →
      ∀ u (B : Stacks T q), B.R (r 0) = ds.map digitSymbol → B.R matrix = mat old →
      (∀ k, k ≠ matrix → k ≠ count → k ≠ saved → k ≠ r 0 → k ≠ r 2 → B.R k = S.R k) →
      ∃ z n, z.user = u.user ∧ n ≤ cost ∧ Exec body evaluate (mk u B) n (mk z {B with
        R := Function.update (Function.update B.R matrix (mat dest)) (r 1) (binSyms H (source dest).val)})) →
    ∃ z R n, z.user = v.user ∧ n ≤ M*(cost+(2*H+9*L+15)+3)+2 ∧
      Exec body (eachSym count saved (.seq evaluate (advanceSweepRank hq r))) (mk v S) n (mk z {S with R := R}) ∧
      R count = [] ∧ R saved = (S.R count).reverse ++ S.R saved ∧
      R (r 2) = (descriptorSelectorFrames H (List.ofFn source)).reverse ∧
      ∀ k, k ≠ count → k ≠ saved → k ≠ r 2 → R k = S.R k := by
  intro last initial run
  have positive : 0 < M := size ▸ pow_pos (by omega) _
  let dest (j : ℕ) : Fin M := ⟨j%M,Nat.mod_lt _ positive⟩
  let old (j : ℕ) := if j = 0 then last else dest (j-1)
  have next (j) : old (j+1) = dest j := by simp [old]
  regs_ne ports
  obtain ⟨z,R,n,hz,hn,loop,done,stock,endState⟩ := sweepSelectorLoop_exec body hq r matrix count saved
    apart (by simp_all) outside (zeros hq L) (by simpa using pos) H cost (source ∘ dest) (mat ∘ old)
    evaluate v S counter (by simpa using width) (by simpa [old] using initial) free (by
      intro j hj u B agree
      let ds := advance hq j (zeros hq L)
      have small : j < M := ticks ▸ hj
      have valueEq : value ds = (dest j).val := by
        rw [show (dest j).val = j from Nat.mod_eq_of_lt small]
        exact enumerate_value hq L j (size ▸ small)
      simp only [Function.comp_apply,next]
      apply run (old j) (dest j) ds (by simp [ds]) valueEq u B
      · simpa [ds] using agree (r 0) (outside 0).1 (outside 0).2
      · simpa [Ne.symm (apart 0),Ne.symm (apart 2)] using agree matrix ‹matrix ≠ count› ‹matrix ≠ saved›
      · intro k hm hc hs h₀ h₂; simpa [hm,h₀,h₂] using agree k hc hs)
  have order : (List.range M).map (source ∘ dest) = List.ofFn source := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have h : i < M := by simpa using hj
      simp [dest,Nat.mod_eq_of_lt h]
  have back : old M = last := by
    simp only [old,if_neg positive.ne']
    apply Fin.ext
    exact Nat.mod_eq_of_lt last.isLt
  simp only [ticks,Function.comp_apply,back,order,blank,List.append_nil] at endState
  refine ⟨z,R,n,hz,by simpa [ticks] using hn,loop,done,stock,?_,?_⟩
  · simpa using endState (r 2) (outside 2).1 (outside 2).2
  · intro k hc hs hb
    have cycle : advance hq M (zeros hq L) = zeros hq L := size ▸ full_cycle hq L
    simpa [hb,cycle,← counter,← initial] using endState k hc hs

end IntegerMultBounds.MathlibTM2.M6.BitNode
