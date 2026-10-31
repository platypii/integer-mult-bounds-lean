module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphContract
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphRunWithin

/-! The actual test and return decoder preserve fixed head intervals. Their
small runtime bounds pay for head travel; the controller edge costs no space. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphRun
open IntegerMultBounds.Machine Graph
open SharedBankStageInput (raw)
noncomputable section
variable {Seg Call : Type} {t a k : ℕ} (pieces : List (Piece Seg Call))
  (capacity : Fintype.card (PC pieces.length) ≤ 2^k) (stack : Fin t) (ht : 0 < t)
  (impl : Implementation t a k Seg Call)

theorem test_run_within_heads (x : Tapes t a) (e : Exit) (B : ℕ)
    (h : GraphContract.Tests impl x e B) (lo hi : ℤ)
    (hbank : ∀ i, lo+B ≤ (raw x (tapeCount pieces capacity stack ht impl)).head i ∧
      (raw x (tapeCount pieces capacity stack ht impl)).head i+B ≤ hi) :
    ∃ n ≤ B+1, RunWithin (program pieces capacity stack ht impl)
      (fun v => ∀ i, lo ≤ v.head i ∧ v.head i ≤ hi) n
      (entryConfig pieces capacity stack ht impl .test x)
      (entryConfig pieces capacity stack ht impl (exitPC pieces e) x) := by
  obtain ⟨n,hn,st,he,hr,hh⟩ := h
  obtain ⟨c,hc,hhalt,hpost,hedge⟩ := test_block pieces capacity stack ht impl x n st hr hh
  have hw := RunWithin.heads_of_run hc lo hi (fun i => by
    have hb := hbank i
    change lo+n ≤ (raw x (tapeCount pieces capacity stack ht impl)).head i ∧
      (raw x (tapeCount pieces capacity stack ht impl)).head i+n ≤ hi
    omega)
  have hj := member_jump_within pieces capacity stack ht impl .test
    (exitPC pieces (impl.exit st)) x x hw hhalt hpost hedge
  rw [he] at hj
  exact ⟨n+1,by omega,hj⟩

theorem pop_run_within_heads (pc : PC pieces.length) (x y : Tapes t a)
    (h : GraphContract.Pops pieces capacity stack x pc y) (lo hi : ℤ)
    (hbank : ∀ i, lo+(k+1 : ℕ) ≤ (raw x (tapeCount pieces capacity stack ht impl)).head i ∧
      (raw x (tapeCount pieces capacity stack ht impl)).head i+(k+1 : ℕ) ≤ hi) :
    RunWithin (program pieces capacity stack ht impl)
      (fun v => ∀ i, lo ≤ v.head i ∧ v.head i ≤ hi) (k+2)
      (entryConfig pieces capacity stack ht impl .pop x)
      (entryConfig pieces capacity stack ht impl pc y) := by
  obtain ⟨f,p,hs,hh,hf,rfl⟩ := h
  obtain ⟨c,hr,hhalt,hpost,hedge⟩ := pop_block pieces capacity stack ht impl pc x f p hs hh hf
  have hw := RunWithin.heads_of_run hr lo hi hbank
  exact member_jump_within pieces capacity stack ht impl .pop pc x _ hw hhalt hpost hedge

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphRun
