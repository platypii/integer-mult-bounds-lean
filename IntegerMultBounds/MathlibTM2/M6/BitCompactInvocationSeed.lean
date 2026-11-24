module

public import IntegerMultBounds.MathlibTM2.M6.BitAllocatedPhaseSeed

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

/-- The three component loaders share their seven control tapes. Each private
tape is written by its own loader and survives both of the other loaders. -/
theorem invocationSeed {T Q k : ℕ} {U : Type} (ts count : Fin 3 → ℕ)
    (fan : Fin k ↪ Fin T) (owner : ∀ j, Fin k ↪ Fin (ts j))
    (bank : ∀ j, Fin (ts j) ↪ Fin T)
    (cover : ∀ z, (∀ h, fan h ≠ z) → ∃ i l, (∀ h, owner i h ≠ l) ∧ bank i l = z)
    (apart : ∀ i l, (∀ h, owner i h ≠ l) →
      (∀ h, fan h ≠ bank i l) ∧ ∀ j, j ≠ i → ∀ m, bank j m ≠ bank i l)
    (setup : ∀ j, Pr Empty (ts j+7) Q prime U) :
    ∃ program : Pr Empty (T+7) Q prime U, ∀ (c : CutoffNodeInput) (seed : ∀ j, Stacks (ts j) prime) (prepared : Stacks T prime),
      (∀ i l, (∀ h, owner i h ≠ l) → prepared.L (bank i l) = (seed i).L l ∧ prepared.R (bank i l) = (seed i).R l) →
      (∀ j, PhaseSeedExec (setup j) (owner j) (count j) c (seed j)) →
      PhaseSeedExec program fan (count 0+count 1+count 2) c prepared 6 := by
  let place := Fin.castAddEmb 7 (n := T)
  let ext := Fin.natAddEmb T (m := 7)
  have disjoint (i : Fin T) (j : Fin 7) : place i ≠ ext j := by
    intro eq
    have h := congrArg Fin.val eq
    change i.val = T+j.val at h
    omega
  let ports j := appendPorts ((bank j).trans place) ext (fun i s => disjoint _ s)
  let code j := embProg (ports j) (Empty.elim : Empty → Empty) (setup j)
  refine ⟨((code 0).seq (code 1)).seq (code 2),?_⟩
  intro c seed prepared initial run u S modulus spectator unit atom ht hs cut blank
  let inputs := fun D : Stacks (T+7) prime => ∀ s, D.R (ext s) = S.R (ext s)
  let state := fun j (D : Stacks (T+7) prime) (X : Stacks (ts j) prime) =>
    ∀ l, (∀ h, owner j h ≠ l) → D.L (place (bank j l)) = X.L l ∧ D.R (place (bank j l)) = X.R l
  let empty (j : Fin 3) : Stacks (ts j) prime := ⟨[],[],fun _ => [],fun _ => []⟩
  let frame := fun (D F : Stacks (T+7) prime) =>
    (∀ h, F.L (place (fan h)) = D.L (place (fan h)) ∧ F.R (place (fan h)) = D.R (place (fan h))) ∧
    ∀ s, F.L (ext s) = D.L (ext s) ∧ F.R (ext s) = D.R (ext s)
  let price j := 178*count j*c.cells+count j*(8*(S.R (ext 6)).length+6)+2
  have load (i : Fin 3) u D (input : inputs D) (clear : state i D (empty i)) := (run i).place
    (P := Empty) Empty.elim (ports i) u D
  have step (i : Fin 3) u D (input : inputs D) (clear : state i D (empty i)) :
      ∃ z F t, Exec Empty.elim (code i) (mk u D) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound D F t (price i) ∧ inputs F ∧ state i F (seed i) ∧ frame D F ∧
        ∀ j, j ≠ i → (state j D (empty j) → state j F (empty j)) ∧ (state j D (seed j) → state j F (seed j)) := by
    have placed := load i u D input clear
    simp only [ports,appendPorts,Function.Embedding.trans_apply,Function.Embedding.coeFn_mk,
      Fin.castAddEmb_apply,Fin.natAddEmb_apply,Fin.addCases_left,Fin.addCases_right] at placed
    obtain ⟨z,F,t,exec,user,paid,ready,keep⟩ := placed ((input 0).trans modulus)
      ((input 1).trans spectator) ((input 2).trans unit) ((input 3).trans atom)
      ((input 4).trans ht) ((input 5).trans hs) ((input 6).trans cut) clear
    have ctrl s := keep (ext s) (fun l _ => disjoint _ _)
    refine ⟨z,F,t,?_,user,?_,fun s => (ctrl s).2.trans (input s),ready,?_,?_⟩
    · simpa only [code,ports,appendPorts,Function.Embedding.coeFn_mk] using exec
    · simpa only [price,show D.R (ext 6) = S.R (ext 6) from input 6] using paid
    · exact ⟨fun h => keep _ (fun l off => place.injective.ne (Ne.symm ((apart i l off).1 h))),ctrl⟩
    · intro j ne
      have kept l := keep (place (bank j l)) (fun q off => place.injective.ne (Ne.symm ((apart i q off).2 j ne l)))
      exact ⟨fun before l off => ⟨(kept l).1.trans (before l off).1,(kept l).2.trans (before l off).2⟩,
        fun before l off => ⟨(kept l).1.trans (before l off).1,(kept l).2.trans (before l off).2⟩⟩
  obtain ⟨z,F,t,exec,user,paid,_,ready,keep⟩ := loadComponentList Empty.elim code inputs
    (fun j D => state j D (empty j)) (fun j D => state j D (seed j)) price frame
    (fun a b => ⟨fun h => ⟨(b.1 h).1.trans (a.1 h).1,(b.1 h).2.trans (a.1 h).2⟩,
      fun s => ⟨(b.2 s).1.trans (a.2 s).1,(b.2 s).2.trans (a.2 s).2⟩⟩)
    step 0 [1,2] (by decide) u S (fun _ => rfl) (fun i _ l off => blank _ ((apart i l off).1))
  refine ⟨z,F,t,exec,user,?_,?_,keep⟩
  · convert paid using 1
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,price]
    ring
  · intro l privateSlot
    obtain ⟨i,q,off,rfl⟩ := cover l privateSlot
    have h := ready i (by fin_cases i <;> decide) q off
    exact ⟨h.1.trans (initial i q off).1.symm,h.2.trans (initial i q off).2.symm⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
