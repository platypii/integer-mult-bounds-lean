module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatDispatchedHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderWindowLoader

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open Shared50ModularControl (prime)

/-- Both sides of the node read the same cutoff, modulus, unit and width clock.
Only the binary idle width and the successor clock are additional inputs. -/
noncomputable def nodeSeedWords (c : CutoffNodeInput) : Fin 12 → List (Fin (prime+4)) :=
  fun j => Fin.addCases (motive := fun _ => List (Fin (prime+4))) (sweepSeedWords c) (![binSyms c.idleWidth.size c.idleWidth,
    List.replicate (c.w+1) blank] : Fin 2 → _) j

private theorem selectSeedWords {A B : Type} {h k t : ℕ}
    {words : A → Fin h → List (Fin (prime+4))} {V : A → ℕ} {seed : A → Stacks t prime}
    (load : LoadsPackedSeed words V seed) (input : B → A)
    (headers : B → Fin k → List (Fin (prime+4))) (field : Fin h → Fin k)
    (read : ∀ c i, headers c (field i) = words (input c) i) :
    LoadsPackedSeed headers (V ∘ input) (seed ∘ input) := by
  obtain ⟨rate,compile⟩ := load
  refine ⟨rate,?_⟩
  intro P U T Q body bank source apart
  obtain ⟨code,run⟩ := compile body bank (source ∘ field) (fun i j => apart i _)
  exact ⟨code,fun c u S ready => run (input c) u S (fun i => (ready _).trans (read c i))⟩

theorem nodeSweepLoader {Config : Type} {T : ℕ} (input : Config → CutoffNodeInput)
    {seed : CutoffNodeInput → Stacks T prime} (load : LoadsPackedSeed sweepSeedWords CutoffNodeInput.cells seed) :
    LoadsPackedSeed (nodeSeedWords ∘ input) (CutoffNodeInput.cells ∘ input) (seed ∘ input) :=
  selectSeedWords load input _ (Fin.castAdd 2) (fun c i => by simp only [Function.comp_apply,nodeSeedWords,Fin.addCases_left])

theorem nodeIdleLoader {Config Job : Type} {H N : ℕ} (input : Config → CutoffNodeInput)
    (origin : Fin H → Option (Σ _ : Job, Fin (72+N)))
    (free : ∃ a b, a ≠ b ∧ origin a = none ∧ origin b = none) :
    LoadsPackedSeed (nodeSeedWords ∘ input) (CutoffNodeInput.cells ∘ input) (fun c =>
      let v := input c
      idleWindowSeed origin (fun _ => idleDispatchStacks N v.w v.idleWidth v.root.width.size v.cutoff)) := by
  apply selectSeedWords (idleWindowDispatchLoader origin free) input _ (![7,8,10,11,9,0] : Fin 6 → Fin 12)
  intro c i
  fin_cases i <;> rfl

end IntegerMultBounds.MathlibTM2.M6.BitNode
