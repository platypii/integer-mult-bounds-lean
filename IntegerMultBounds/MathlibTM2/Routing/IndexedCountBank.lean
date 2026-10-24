module

public import IntegerMultBounds.MathlibTM2.Routing.IndexedCountStep

/-! Closed bank invariant for counted profile generation. Earlier profiles are
prepended in reverse iteration order, while count symbols are archived for rewind. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {T A : ℕ}

def indexedCountOutput (profile : ℕ → List (Fin (A + 4))) : ℕ → List (Fin (A + 4))
  | 0 => []
  | i + 1 => profile i ++ indexedCountOutput profile i

def indexedCountBank (R : Fin T → List (Fin (A + 4))) (count saved index dst : Fin T)
    (L : ℕ) (cs : List (Fin (A + 4))) (profile : ℕ → List (Fin (A + 4))) (i : ℕ) :
    Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update R count (cs.drop i))
    saved ((cs.take i).reverse ++ R saved)) index (binSyms L i))
    dst (indexedCountOutput profile i ++ R dst)

theorem indexedCountBank_keep (R : Fin T → List (Fin (A + 4))) (count saved index dst : Fin T)
    (L : ℕ) (cs : List (Fin (A + 4))) (profile : ℕ → List (Fin (A + 4))) (i : ℕ)
    (j : Fin T) (hc : j ≠ count) (hs : j ≠ saved) (hi : j ≠ index) (hd : j ≠ dst) :
    indexedCountBank R count saved index dst L cs profile i j = R j := by
  simp [indexedCountBank, hc, hs, hi, hd]

theorem indexedCountBank_count_flag (R : Fin T → List (Fin (A + 4)))
    (count saved index dst : Fin T) (hreg : [count,saved,index,dst].Nodup)
    (L : ℕ) (cs : List (Fin (A + 4))) (profile : ℕ → List (Fin (A + 4))) (i : ℕ) :
    (indexedCountBank R count saved index dst L cs profile i count).head?.isSome = decide (i < cs.length) := by
  have hn := hreg
  regs_ne hn
  have hc : indexedCountBank R count saved index dst L cs profile i count = cs.drop i := by
    simp [indexedCountBank, ‹count ≠ saved›, ‹count ≠ index›, ‹count ≠ dst›]
  rw [hc]
  cases hd : cs.drop i with
  | nil =>
    have hh := congrArg List.length hd
    simp only [List.length_drop, List.length_nil] at hh
    simp [show ¬ i < cs.length by omega]
  | cons c rest =>
    have hh := congrArg List.length hd
    simp only [List.length_drop, List.length_cons] at hh
    simp [show i < cs.length by omega]

theorem indexedCountBank_step (R : Fin T → List (Fin (A + 4))) (count saved index dst : Fin T)
    (hreg : [count,saved,index,dst].Nodup) (L : ℕ) (cs : List (Fin (A + 4)))
    (profile : ℕ → List (Fin (A + 4))) (i : ℕ) (c : Fin (A + 4)) (rest : List (Fin (A + 4)))
    (hc : cs.drop i = c :: rest) :
    let B := indexedCountBank R count saved index dst L cs profile i
    indexedCountStepBank B count saved index dst L i c rest (profile i ++ B dst) =
      indexedCountBank R count saved index dst L cs profile (i + 1) := by
  have hn := hreg
  regs_ne hn
  have hdrop : cs.drop (i + 1) = rest := by
    rw [← List.drop_drop, hc]
    rfl
  have htake : cs.take (i + 1) = cs.take i ++ [c] := by
    rw [List.take_add, hc]
    rfl
  dsimp only
  funext j
  by_cases hcount : j = count
  · subst j; simp [indexedCountBank, indexedCountStepBank, hdrop, ‹count ≠ saved›, ‹count ≠ index›, ‹count ≠ dst›]
  by_cases hsaved : j = saved
  · subst j; simp [indexedCountBank, indexedCountStepBank, htake, ‹saved ≠ index›, ‹saved ≠ dst›]
  by_cases hindex : j = index
  · subst j; simp [indexedCountBank, indexedCountStepBank, (Ne.symm ‹count ≠ index›), (Ne.symm ‹saved ≠ index›), ‹index ≠ dst›]
  by_cases hdst : j = dst
  · subst j; simp [indexedCountBank, indexedCountStepBank, indexedCountOutput,
      (Ne.symm ‹count ≠ dst›), (Ne.symm ‹saved ≠ dst›), (Ne.symm ‹index ≠ dst›), List.append_assoc]
  · simp [indexedCountBank, indexedCountStepBank, hcount, hsaved, hindex, hdst]

theorem indexedCountOutput_order (profile : ℕ → List (Fin (A + 4))) (N : ℕ) :
    indexedCountOutput profile N = ((List.range N).reverse.map profile).flatten := by
  induction N with
  | zero => rfl
  | succ N ih => simp [indexedCountOutput, List.range_succ, ih]

end IntegerMultBounds.MathlibTM2.Routing
