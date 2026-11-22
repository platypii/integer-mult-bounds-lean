module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperFanRun
public import Mathlib.Logic.Embedding.Basic

/-! Tape placement for adjacent stages sharing an owner bank. -/
@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.BitNode

/-- The first stage occupies the prefix. The second stage reuses the output
ports of the first for its input ports and has its own tapes everywhere else. -/
theorem adjacentStagePlacement {k m n : ℕ}
    (out : Fin k ↪ Fin m) (input : Fin k ↪ Fin n) :
    ∃ bank : Fin n ↪ Fin (m+n),
      (∀ i, bank (input i) = (out i).castAdd n) ∧
      ∀ j, (∀ i, input i ≠ j) → bank j = j.natAdd m := by
  classical
  let place (j : Fin n) : Fin m ⊕ Fin n :=
    if h : ∃ i, input i = j then Sum.inl (out h.choose) else Sum.inr j
  have shared (i : Fin k) : place (input i) = Sum.inl (out i) := by
    dsimp [place]
    rw [dite_eq_left ⟨i,rfl⟩]
    congr 2
    exact input.injective (Exists.choose_spec (show ∃ a, input a = input i from ⟨i,rfl⟩))
  have privateTape (j : Fin n) (off : ∀ i, input i ≠ j) : place j = Sum.inr j := by
    simp [place, not_exists.mpr off]
  have inj : Function.Injective place := by
    intro x y eq
    by_cases hx : ∃ i, input i = x <;> by_cases hy : ∃ i, input i = y
    · obtain ⟨i,rfl⟩ := hx
      obtain ⟨j,rfl⟩ := hy
      rw [shared, shared] at eq
      exact congrArg input (out.injective (Sum.inl.inj eq))
    · obtain ⟨i,rfl⟩ := hx
      rw [shared, privateTape y (not_exists.mp hy)] at eq
      contradiction
    · obtain ⟨j,rfl⟩ := hy
      rw [privateTape x (not_exists.mp hx), shared] at eq
      contradiction
    · rwa [privateTape x (not_exists.mp hx), privateTape y (not_exists.mp hy), Sum.inr.injEq] at eq
  refine ⟨(⟨place,inj⟩ : Fin n ↪ Fin m ⊕ Fin n).trans finSumFinEquiv.toEmbedding, ?_, ?_⟩
  · intro i
    change finSumFinEquiv (place (input i)) = _
    simp [shared]
  · intro j off
    change finSumFinEquiv (place j) = _
    simp [privateTape j off]

open IntegerMultBounds.Machine Stack Host

/-- A common initial configuration for two prepared workspaces. The first
program owns the input and output streams at entry. -/
def adjacentStageStacks {m n A : ℕ} (L : Stacks m A) (R : Stacks n A) : Stacks (m+n) A :=
  ⟨L.inp, L.out, Fin.addCases L.L R.L, Fin.addCases L.R R.R⟩

private theorem adjacentStageStacks_left {m n A : ℕ} (L : Stacks m A) (R : Stacks n A) :
    embStk (Fin.castAdd n) (adjacentStageStacks L R) = L := by
  cases L
  simp [embStk, adjacentStageStacks, Function.comp_def]

/-- Sequence two separately allocated programs. The second receives the first
program's output on their common bank and its original private workspace.
Its procedure calls dispatch to its own table, and both step counts are charged. -/
theorem runAdjacentStages {P R U : Type} {k m n q A : ℕ}
    (out : Fin k ↪ Fin m) (input : Fin k ↪ Fin n) :
    ∃ bank : Fin n ↪ Fin (m+n), ∀ (left : P → Pr P m q A U) (right : R → Pr R n q A U) a b,
    let leftBank := Fin.castAdd n (n := m)
    let body := Sum.elim (fun g => embProg leftBank Sum.inl (left g))
      (fun g => embProg bank Sum.inr (right g))
    ∀ (u : HS (m+n) q A U) (L : Stacks m A) (R₀ : Stacks n A) v F t (budget : ℕ)
      (post : U → Stacks n A → Prop),
      Exec left a (mk (embDn leftBank u) L) t (mk v F) →
      (∀ w D, w.user = v.user →
        (∀ i, D.L (input i) = F.L (out i) ∧ D.R (input i) = F.R (out i)) →
        (∀ j, (∀ i, input i ≠ j) → D.L j = R₀.L j ∧ D.R j = R₀.R j) →
        ∃ z B s, Exec right b (mk w D) s (mk z B) ∧ s ≤ budget ∧ post z.user B) →
      ∃ z B steps, Exec body ((embProg leftBank Sum.inl a).seq (embProg bank Sum.inr b))
        (mk u (adjacentStageStacks L R₀)) steps (mk z B) ∧ steps ≤ t+budget ∧ post z.user (embStk bank B) := by
  obtain ⟨bank, shared, privateTape⟩ := adjacentStagePlacement out input
  refine ⟨bank, ?_⟩
  intro left right a b leftBank body u L R₀ v F t budget post exec next
  obtain ⟨w,D,ran,_,user,view,frame⟩ := exec_emb (ι := Sum.inl) (body' := body)
    (Fin.castAddEmb n (n := m)).injective (fun _ => rfl) exec u rfl (adjacentStageStacks L R₀) (adjacentStageStacks_left L R₀)
  obtain ⟨z,B,s,ranNext,paid,result⟩ := next (embDn bank w) (embStk bank D) user (by
    intro i
    change D.L (bank (input i)) = _ ∧ D.R (bank (input i)) = _
    rw [shared]
    exact ⟨congrArg (fun C => C.L (out i)) view, congrArg (fun C => C.R (out i)) view⟩) (by
    intro j off
    have outside : ∀ i, leftBank i ≠ j.natAdd m := by
      intro i eq
      have h := congrArg Fin.val eq
      change i.val = m+j.val at h
      omega
    change D.L (bank j) = _ ∧ D.R (bank j) = _
    rw [privateTape j off]
    simpa [adjacentStageStacks] using frame _ outside)
  obtain ⟨z',B',placed,_,same,endView,_⟩ := exec_emb (ι := Sum.inr) (body' := body)
    bank.injective (fun _ => rfl) ranNext w rfl D rfl
  exact ⟨z',B',t+s,Exec.seq ran placed,Nat.add_le_add_left paid t,same ▸ endView ▸ result⟩

open IntegerMultBounds.Networks
open Shared50ModularControl (prime)

/-- Compose PR589 programs across a represented owner bank, including its two controls. -/
theorem runAdjacentHelperFans {P R U : Type} {k m n q V : ℕ}
    (out : Fin (k+2) ↪ Fin m) (input : Fin (k+2) ↪ Fin n) :
    ∃ bank : Fin n ↪ Fin (m+n), ∀ (left : P → Pr P m q prime U) (right : R → Pr R n q prime U) a b,
    let leftBank := Fin.castAdd n (n := m)
    let body := Sum.elim (fun g => embProg leftBank Sum.inl (left g))
      (fun g => embProg bank Sum.inr (right g))
    ∀ (u : HS (m+n) q prime U) (L : Stacks m prime) (R₀ : Stacks n prime) v F t budget
      (data : Fin k → Fin V → ZMod 2) (post : U → Stacks n prime → Prop),
      Exec left a (mk (embDn leftBank u) L) t (mk v F) →
      HelperFan out data F →
      (∀ w D, w.user = v.user → HelperFan input data D →
        (∀ j, (∀ i, input i ≠ j) → D.L j = R₀.L j ∧ D.R j = R₀.R j) →
        ∃ z B s, Exec right b (mk w D) s (mk z B) ∧ s ≤ budget ∧ post z.user B) →
      ∃ z B steps, Exec body ((embProg leftBank Sum.inl a).seq (embProg bank Sum.inr b))
        (mk u (adjacentStageStacks L R₀)) steps (mk z B) ∧ steps ≤ t+budget ∧ post z.user (embStk bank B) := by
  obtain ⟨bank,compose⟩ := runAdjacentStages (P := P) (R := R) (U := U) (A := prime) (q := q) out input
  refine ⟨bank, ?_⟩
  intro left right a b leftBank body u L R₀ v F t budget data post exec rep next
  apply compose left right a b u L R₀ v F t budget post exec
  intro w D user ports off
  apply next w D user _ off
  intro i z
  simpa only [embStk, Function.comp_apply, (ports i).1, (ports i).2] using rep i z

end IntegerMultBounds.MathlibTM2.M6.BitNode
