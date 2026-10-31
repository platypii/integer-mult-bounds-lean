module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.CommonBank

/-! Head bounds for the permanent bank are structural in its component banks.
Header contents do not affect heads; optional counters have heads zero or one. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.CommonBank
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
noncomputable section
variable {t : ℕ}

private theorem append_heads {s u : ℕ} (B : ℕ) {x x' : Tapes s prime} {y y' : Tapes u prime}
    (hx : ∀ i, x.head i-B ≤ x'.head i ∧ x'.head i ≤ x.head i+B)
    (hy : ∀ i, y.head i-B ≤ y'.head i ∧ y'.head i ≤ y.head i+B) :
    ∀ i, (x.append y).head i-B ≤ (x'.append y').head i ∧
      (x'.append y').head i ≤ (x.append y).head i+B := by
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [Tapes.append,Fin.addCases_left] using hx i
  | right i => simpa only [Tapes.append,Fin.addCases_right] using hy i

theorem counters_head_bounds (c : Fin K → Option ℕ) :
    ∀ i, 0 ≤ (counters c).head i ∧ (counters c).head i ≤ 1 := by
  intro i
  cases h : c i <;> simp [counters,word,CounterDimensions.descriptorHead,h]

theorem bank_heads_close (B : ℕ) (hB : 1 ≤ B)
    (roles roles' : Tapes t prime) (hs hs' : Fin 6 → List Bool)
    (f f' : ℤ → Fin (prime+4)) (p p' : ℤ) (node node' scalar scalar' : Tapes 1 prime)
    (c c' : Fin K → Option ℕ) (st st' : Tapes 2 prime)
    (hr : ∀ i, roles.head i-B ≤ roles'.head i ∧ roles'.head i ≤ roles.head i+B)
    (hp : p-B ≤ p' ∧ p' ≤ p+B)
    (hn : ∀ i, node.head i-B ≤ node'.head i ∧ node'.head i ≤ node.head i+B)
    (hscalar : ∀ i, scalar.head i-B ≤ scalar'.head i ∧ scalar'.head i ≤ scalar.head i+B)
    (ht : ∀ i, st.head i-B ≤ st'.head i ∧ st'.head i ≤ st.head i+B) :
    ∀ i, (bank roles hs f p node scalar c st).head i-B ≤ (bank roles' hs' f' p' node' scalar' c' st').head i ∧
      (bank roles' hs' f' p' node' scalar' c' st').head i ≤ (bank roles hs f p node scalar c st).head i+B := by
  have he : ∀ i, (SharedBank.empty 1 prime).head i-B ≤ (SharedBank.empty 1 prime).head i ∧
      (SharedBank.empty 1 prime).head i ≤ (SharedBank.empty 1 prime).head i+B := by
    intro i; constructor <;> omega
  have hh : ∀ i, (RecursiveShiftRoleBank.headers hs).head i-B ≤ (RecursiveShiftRoleBank.headers hs').head i ∧
      (RecursiveShiftRoleBank.headers hs').head i ≤ (RecursiveShiftRoleBank.headers hs).head i+B := by
    intro i; simp only [RecursiveShiftRoleBank.headers]; constructor <;> omega
  have hw : ∀ i, (RecursiveCallBank.work f p).head i-B ≤ (RecursiveCallBank.work f' p').head i ∧
      (RecursiveCallBank.work f' p').head i ≤ (RecursiveCallBank.work f p).head i+B := by
    intro i
    fin_cases i <;> simp [RecursiveCallBank.work]
    all_goals omega
  have hc : ∀ i, (counters c).head i-B ≤ (counters c').head i ∧ (counters c').head i ≤ (counters c).head i+B := by
    intro i
    have h := counters_head_bounds c i
    have h' := counters_head_bounds c' i
    omega
  simp only [bank,Shared50RecursiveBank.bank,RecursiveCallBank.bank,RecursiveShiftRoleBank.common]
  exact append_heads B hr (append_heads B (append_heads B he hh)
    (append_heads B (append_heads B hw (append_heads B hn (append_heads B hscalar hc))) ht))

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.CommonBank
