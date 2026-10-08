import IntegerMultBounds.Networks.Shared50GlobalBudget
import IntegerMultBounds.Networks.Shared50SparseInvocation
import IntegerMultBounds.Networks.TripleNeighborPermutation

/-! The actual three-coordinate scalar schedule on the padded two-bank world.
Stages one and three reuse complete auxiliary banks through the neighbor
permutation; the middle stage has separate banks and reversed local block order.
All dirty scratch is restored. Grouped topology, projector ranks and tape costs
are separate obligations. -/

namespace IntegerMultBounds.Networks.Shared50GlobalCircuit

noncomputable section
open Circuit
open GlobalCircuit (address fixed varying address_injective fixed_address varying_address
  address_fixed_varying embed embed_run embed_outside keys keys_nodup mem_keys)
open Shared50GlobalBudget (Triple Address Side Control Invocation Scratch World)

set_option synthInstance.maxSize 2048 in
instance worldDecidableEq : DecidableEq World := inferInstance

attribute [local irreducible] Shared50Finite.program SharedPointExecution.code

variable {n : ℕ}

/-- Stage-three key `(B, pi(A))` reuses precisely stage-one key `(A,B)`. -/
def scratchKey (j : Fin 3) (q : Triple × Triple) : Invocation :=
  if j = 0 then (0,q) else if j = 1 then (1,q)
  else (0, TripleNeighborPermutation.permutation50.symm q.2, q.1)

@[simp] theorem scratchKey_first (q : Triple × Triple) : scratchKey 0 q = (0,q) := by
  simp [scratchKey]

@[simp] theorem scratchKey_middle (q : Triple × Triple) : scratchKey 1 q = (1,q) := by
  simp [scratchKey]

@[simp] theorem scratchKey_reuse (A B : Triple) :
    scratchKey 2 (B, TripleNeighborPermutation.permutation50 A) = scratchKey 0 (A,B) := by
  simp [scratchKey]

/-- Within each stage, distinct coordinate lines have distinct auxiliary banks. -/
theorem scratchKey_injective (j : Fin 3) : Function.Injective (scratchKey j) := by
  fin_cases j
  · intro q q' hh
    simpa [scratchKey] using hh
  · intro q q' hh
    simpa [scratchKey] using hh
  · rintro ⟨a,b⟩ ⟨c,d⟩ hh
    have he : TripleNeighborPermutation.permutation50.symm b =
        TripleNeighborPermutation.permutation50.symm d ∧ a = c := by
      simpa [scratchKey] using hh
    exact Prod.ext he.2 (TripleNeighborPermutation.permutation50.symm.injective he.1)

theorem first_middle_disjoint (q q' : Triple × Triple) : scratchKey 0 q ≠ scratchKey 1 q' := by
  simp [scratchKey]

theorem third_middle_disjoint (q q' : Triple × Triple) : scratchKey 2 q ≠ scratchKey 1 q' := by
  simp [scratchKey]

/-- A local invocation sees only its coordinate line and its own scratch. -/
def localMap (eB : Fin n ≃ Triple)
    (j : Fin 3) (q : Triple × Triple) : Role n 509194 50 0 → World
  | Sum.inl i => Sum.inl (address j q (eB i))
  | Sum.inr (Sum.inl i) => Sum.inr (Sum.inl (address j q (eB i)))
  | Sum.inr (Sum.inr (Sum.inl i)) => Sum.inr (Sum.inr (scratchKey j q, Sum.inl i))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) => Sum.inr (Sum.inr (scratchKey j q, Sum.inr i))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr i))) => Fin.elim0 i

theorem localMap_injective (eB : Fin n ≃ Triple)
    (j : Fin 3) (q : Triple × Triple) : Function.Injective (localMap eB j q) := by
  intro i i' h
  rcases i with i | i | i | i | i <;> rcases i' with i' | i' | i' | i' | i' <;>
    simp only [localMap, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
      Prod.mk.injEq, true_and] at h ⊢
  all_goals try exact eB.injective (address_injective j q h)
  all_goals try exact h
  all_goals first | exact Fin.elim0 i | exact Fin.elim0 i'

def localEmbedding (eB : Fin n ≃ Triple)
    (j : Fin 3) (q : Triple × Triple) : Role n 509194 50 0 ↪ World :=
  ⟨localMap eB j q, localMap_injective eB j q⟩

/-- Reuse identifies matching allocated side slots, with no remapping of roles. -/
theorem side_reused (eB : Fin n ≃ Triple) (A B : Triple) (i : Fin 509194) :
    localEmbedding eB 2 (B, TripleNeighborPermutation.permutation50 A) (side i) =
      localEmbedding eB 0 (A,B) (side i) := by
  simp [localEmbedding, localMap, side]

/-- The same physical central slot is also reused across the two outer stages. -/
theorem center_reused (eB : Fin n ≃ Triple) (A B : Triple) (i : Fin 50) :
    localEmbedding eB 2 (B, TripleNeighborPermutation.permutation50 A) (center i) =
      localEmbedding eB 0 (A,B) (center i) := by
  simp [localEmbedding, localMap, center]

/-- Middle-stage execution uses the explicitly inverted local block order. -/
def localProgram (eB : Fin n ≃ Triple) (j : Fin 3) :
    Program (Role n 509194 50 0) (ZMod 2) :=
  if j = 1 then Shared50SparseInvocation.opposite eB else Shared50SparseInvocation.program eB

def invocationProgram (eB : Fin n ≃ Triple)
    (j : Fin 3) (q : Triple × Triple) :
    Program World (ZMod 2) :=
  embed (localEmbedding eB j q) (localProgram eB j)

/-- Complete contents of the physical data banks and every invocation's scratch. -/
def contents (X Y : Address → ZMod 2) (S : Scratch → ZMod 2) : World → ZMod 2 :=
  Sum.elim X (Sum.elim Y S)

/-- Apply a shear only along the selected coordinate line. -/
def onLine (j : Fin 3) (q : Triple × Triple) (f g : Address → ZMod 2) : Address → ZMod 2 :=
  fun b => if fixed j b = q then f b else g b

private theorem contents_local (eB : Fin n ≃ Triple)
    (j : Fin 3) (q : Triple × Triple) (X Y : Address → ZMod 2) (S : Scratch → ZMod 2) :
    contents X Y S ∘ localEmbedding eB j q =
      banks (fun i => X (address j q (eB i))) (fun i => Y (address j q (eB i)))
        (fun i => S (scratchKey j q, Sum.inl i)) (fun i => S (scratchKey j q, Sum.inr i))
        (Fin.elim0) := by
  funext k
  rcases k with i | i | i | i | i <;> try rfl
  exact Fin.elim0 i

/-- The complete effect of one invocation on the full physical register file. -/
def invocationEffect (j : Fin 3) (q : Triple × Triple) (X Y : Address → ZMod 2)
    (S : Scratch → ZMod 2) : World → ZMod 2 :=
  if j = 1 then contents (onLine j q (X + Y) X) Y S
  else contents X (onLine j q (Y + X) Y) S

/-- Every invocation is compiled from the certified twelve-block local list. Its selected scratch
bank and all other invocations' scratch are restored for arbitrary inputs. -/
theorem invocation_run (eB : Fin n ≃ Triple)
    (j : Fin 3) (q : Triple × Triple) (X Y : Address → ZMod 2)
    (S : Scratch → ZMod 2) :
    run (invocationProgram eB j q) (contents X Y S) =
      invocationEffect j q X Y S := by
  have hl : run (localProgram eB j)
      (contents X Y S ∘ localEmbedding eB j q) =
      invocationEffect j q X Y S ∘ localEmbedding eB j q := by
    by_cases hj : j = 1
    · simp only [localProgram, invocationEffect, hj, ↓reduceIte, contents_local,
        Shared50SparseInvocation.opposite_run]
      simp [onLine]
      rfl
    · simp only [localProgram, invocationEffect, hj, ↓reduceIte, contents_local,
        Shared50SparseInvocation.program_run]
      simp [onLine]
      rfl
  funext k
  by_cases hk : ∃ i, localEmbedding eB j q i = k
  · obtain ⟨i, rfl⟩ := hk
    exact congrFun ((embed_run (localEmbedding eB j q) _ _).trans hl) i
  · have hout : ∀ i, localEmbedding eB j q i ≠ k := by simpa using hk
    rw [invocationProgram, embed_outside _ _ _ _ hout]
    rcases k with b | b | scratch
    · have hb : fixed j b ≠ q := by
        intro hb
        apply hout (x (eB.symm (varying j b)))
        simp [localEmbedding, localMap, x, ← hb]
      unfold invocationEffect
      split <;> simp [contents, onLine, hb]
    · have hb : fixed j b ≠ q := by
        intro hb
        apply hout (y (eB.symm (varying j b)))
        simp [localEmbedding, localMap, y, ← hb]
      unfold invocationEffect
      split <;> simp [contents, onLine, hb]
    · by_cases hj : j = 1 <;> simp [invocationEffect, hj, contents]

/-- Accumulate a shear on a list of distinct coordinate lines. -/
def onLines (j : Fin 3) (qs : List (Triple × Triple)) (f g : Address → ZMod 2) : Address → ZMod 2 :=
  fun b => if fixed j b ∈ qs then f b else g b

private theorem onLines_step (j : Fin 3) (q : Triple × Triple) (qs : List (Triple × Triple))
    (hq : q ∉ qs) (base : Address → ZMod 2) (F : Address → ZMod 2 → ZMod 2) :
    onLines j qs (fun b => F b (onLine j q (fun b => F b (base b)) base b))
      (onLine j q (fun b => F b (base b)) base) =
      onLines j (q :: qs) (fun b => F b (base b)) base := by
  funext b
  by_cases he : fixed j b = q
  · simp [onLines, onLine, he, hq]
  · simp [onLines, onLine, he]

/-- Flatten an explicitly enumerated finite collection of invocation programs. -/
def partialStage (eB : Fin n ≃ Triple)
    (j : Fin 3) (qs : List (Triple × Triple)) : Program World (ZMod 2) :=
  qs.flatMap (invocationProgram eB j)

theorem partialStage_run (eB : Fin n ≃ Triple)
    (j : Fin 3) (qs : List (Triple × Triple)) (hq : qs.Nodup)
    (X Y : Address → ZMod 2) (S : Scratch → ZMod 2) :
    run (partialStage eB j qs) (contents X Y S) =
      if j = 1 then contents (onLines j qs (X + Y) X) Y S
      else contents X (onLines j qs (Y + X) Y) S := by
  induction qs generalizing X Y with
  | nil =>
    simp only [partialStage, List.flatMap_nil, run_nil]
    split <;> rfl
  | cons q qs ih =>
    obtain ⟨hmem, hnodup⟩ := List.nodup_cons.mp hq
    simp only [partialStage, List.flatMap_cons, run_append]
    rw [invocation_run eB]
    by_cases hj : j = 1
    · subst j
      simp only [invocationEffect, ↓reduceIte]
      rw [show run (List.flatMap (invocationProgram eB 1) qs)
          (contents (onLine 1 q (X + Y) X) Y S) = _ from ih hnodup _ Y]
      simp only [↓reduceIte]
      congr 1
      exact onLines_step 1 q qs hmem X (fun b x => x + Y b)
    · simp only [invocationEffect, hj, ↓reduceIte]
      rw [show run (List.flatMap (invocationProgram eB j) qs)
          (contents X (onLine j q (Y + X) Y) S) = _ from ih hnodup X _]
      simp only [hj, ↓reduceIte]
      congr 1
      exact onLines_step j q qs hmem Y (fun b y => y + X b)

def stage (eB : Fin n ≃ Triple)
    (j : Fin 3) :
    Program World (ZMod 2) := partialStage eB j (keys eB)

/-- Every coordinate line is updated exactly once by the literal finite list. -/
theorem stage_run (eB : Fin n ≃ Triple)
    (j : Fin 3) (X Y : Address → ZMod 2) (S : Scratch → ZMod 2) :
    run (stage eB j) (contents X Y S) =
      if j = 1 then contents (X + Y) Y S else contents X (Y + X) S := by
  have full (f g : Address → ZMod 2) : onLines j (keys eB) f g = f := by
    funext b
    simp only [onLines, mem_keys, ↓reduceIte]
  rw [stage, partialStage_run eB j _ (keys_nodup eB)]
  simp only [full]

/-- Chronological three-coordinate instruction list on the reused world. -/
def program (eB : Fin n ≃ Triple) : Program World (ZMod 2) :=
  stage eB 0 ++ stage eB 1 ++ stage eB 2

/-- Both data banks exchange values and every reused scratch scalar is restored. -/
theorem program_run (eB : Fin n ≃ Triple) (X Y : Address → ZMod 2) (S : Scratch → ZMod 2) :
    run (program eB) (contents X Y S) = contents Y X S := by
  simp only [program, run_append, stage_run,
    show (0 : Fin 3) ≠ 1 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
  have hd (f : Address → ZMod 2) : f + f = 0 := by
    funext b
    simpa only [Pi.add_apply, Pi.zero_apply, ZMod.neg_eq_self_mod_two] using add_neg_cancel (f b)
  have hx : X + (Y + X) = Y := by
    have hh := hd X
    linear_combination hh
  rw [hx, add_assoc Y X Y, add_comm X Y, ← add_assoc, hd, zero_add]

/-- Reversing and exchanging the local banks does not change list length. -/
@[simp] theorem localProgram_length (eB : Fin n ≃ Triple) (j : Fin 3) :
    (localProgram eB j).length = (Shared50SparseInvocation.program (s := 0) eB).length := by
  unfold localProgram
  split
  · rw [Shared50SparseInvocation.opposite, rename_length,
      Shared50SparseInvocation.inverse_length, Shared50SparseInvocation.program_length]
  · rfl

@[simp] theorem invocationProgram_length (eB : Fin n ≃ Triple) (j : Fin 3) (q : Triple × Triple) :
    (invocationProgram eB j q).length = (Shared50SparseInvocation.program (s := 0) eB).length := by
  rw [invocationProgram, GlobalCircuit.embed_length, localProgram_length]

theorem partialStage_length (eB : Fin n ≃ Triple) (j : Fin 3) (qs : List (Triple × Triple)) :
    (partialStage eB j qs).length = qs.length * (Shared50SparseInvocation.program (s := 0) eB).length := by
  induction qs with
  | nil => simp [partialStage]
  | cons q qs ih =>
    simp only [partialStage, List.flatMap_cons, List.length_append, invocationProgram_length,
      List.length_cons] at *
    rw [ih]
    ring

/-- Exact scalar instruction accounting, before any tape implementation. -/
theorem program_length (eB : Fin n ≃ Triple) :
    (program eB).length = 3 * n ^ 2 * (Shared50SparseInvocation.program (s := 0) eB).length := by
  simp only [program, List.length_append, stage, partialStage_length, GlobalCircuit.keys_length]
  ring

/-- Fix the finite enumeration once for the entire concrete scalar network. -/
def enumeration : Fin 19600 ≃ Triple :=
  (Fintype.equivFinOfCardEq Shared50GlobalBudget.triple_card).symm

def program50 : Program World (ZMod 2) := program enumeration

theorem program50_run (X Y : Address → ZMod 2) (S : Scratch → ZMod 2) :
    run program50 (contents X Y S) = contents Y X S := program_run enumeration X Y S

/-- This bounds scalar instructions only, not multi-tape transition costs. -/
theorem program50_instruction_bound : program50.length ≤ 3 * 19600 ^ 2 * 5209540 := by
  rw [program50, program_length]
  exact Nat.mul_le_mul_left _ (Shared50SparseInvocation.instruction_bound50 (s := 0) enumeration)

end
end IntegerMultBounds.Networks.Shared50GlobalCircuit
