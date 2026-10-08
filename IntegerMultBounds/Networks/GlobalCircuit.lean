import IntegerMultBounds.Networks.CircuitRouting
import IntegerMultBounds.Networks.Wires

/-! A literal global scalar circuit with one dirty-scratch bank per invocation.
The elementary lists preserve the eight-row order, including the reversed middle
schedule. They do not establish the manuscript's grouped incidence topology:
`rowGate` retains zero-coefficient terms and splits multi-output gates. No label,
residual-rank, or tape-cost claim is made for these elementary lists. -/

namespace IntegerMultBounds.Networks.GlobalCircuit

open Circuit

section Embedding
variable {ι κ R : Type*} [DecidableEq ι] [DecidableEq κ] [CommRing R]

/-- Compile a local gate into distinct global register names. -/
def embedGate (f : ι ↪ κ) (g : Gate ι R) : Gate κ R :=
  ⟨f g.target, g.terms.map fun p => (f p.1, p.2)⟩

def embed (f : ι ↪ κ) (p : Program ι R) : Program κ R := p.map (embedGate f)

theorem embedGate_run (f : ι ↪ κ) (g : Gate ι R) (r : κ → R) :
    (embedGate f g).run r ∘ f = g.run (r ∘ f) := by
  funext k
  simp only [Gate.run, embedGate, List.map_map, Function.comp_apply]
  by_cases hk : k = g.target
  · subst k; simp [Function.comp_def]
  · simp [Function.update_of_ne hk, Function.update_of_ne (f.injective.ne hk)]

theorem embed_run (f : ι ↪ κ) (p : Program ι R) (r : κ → R) :
    run (embed f p) r ∘ f = run p (r ∘ f) := by
  induction p generalizing r with
  | nil => rfl
  | cons g gs ih =>
    simp only [embed, List.map_cons, run_cons] at *
    rw [ih, embedGate_run]

omit [DecidableEq ι] in
theorem embed_outside (f : ι ↪ κ) (p : Program ι R) (r : κ → R)
    (k : κ) (hk : ∀ i, f i ≠ k) : run (embed f p) r k = r k := by
  apply run_preserves
  simp only [embed, List.mem_map]
  rintro g ⟨g', _, rfl⟩
  exact hk g'.target

omit [DecidableEq ι] [DecidableEq κ] [CommRing R] in
@[simp] theorem embed_length (f : ι ↪ κ) (p : Program ι R) :
    (embed f p).length = p.length := List.length_map _
end Embedding

abbrev Address (B : Type*) := B × B × B
abbrev Invocation (B : Type*) := Fin 3 × B × B
abbrev World (B A C : Type*) := Address B ⊕ Address B ⊕ (Invocation B × (A ⊕ C))

set_option synthInstance.maxSize 1024 in
/-- Cache the finite product/sum decision procedure, avoiding repeated
large instance searches at each circuit evaluation. -/
instance worldDecidableEq {B A C : Type*} [DecidableEq B] [DecidableEq A] [DecidableEq C] :
    DecidableEq (World B A C) := inferInstanceAs
      (DecidableEq ((B × B × B) ⊕ (B × B × B) ⊕ ((Fin 3 × B × B) × (A ⊕ C))))

/-- Insert the varying coordinate into its physical position. -/
def address {B : Type*} (j : Fin 3) (q : B × B) (b : B) : Address B :=
  if j = 0 then (b, q.1, q.2) else if j = 1 then (q.1, b, q.2) else (q.1, q.2, b)

def fixed {B : Type*} (j : Fin 3) (b : Address B) : B × B :=
  if j = 0 then (b.2.1, b.2.2) else if j = 1 then (b.1, b.2.2) else (b.1, b.2.1)

def varying {B : Type*} (j : Fin 3) (b : Address B) : B :=
  if j = 0 then b.1 else if j = 1 then b.2.1 else b.2.2

@[simp] theorem fixed_address {B : Type*} (j : Fin 3) (q : B × B) (b : B) :
    fixed j (address j q b) = q := by
  fin_cases j <;> simp [fixed, address]

@[simp] theorem varying_address {B : Type*} (j : Fin 3) (q : B × B) (b : B) :
    varying j (address j q b) = b := by
  fin_cases j <;> simp [varying, address]

@[simp] theorem address_fixed_varying {B : Type*} (j : Fin 3) (b : Address B) :
    address j (fixed j b) (varying j b) = b := by
  fin_cases j <;> simp [varying, fixed, address]

theorem address_injective {B : Type*} (j : Fin 3) (q : B × B) :
    Function.Injective (address j q) := by
  intro b b' h
  simpa using congrArg (varying j) h

section Schedule
variable {B A C R : Type*} [DecidableEq B] [DecidableEq A] [DecidableEq C] [CommRing R]
variable {n a c : ℕ}

/-- A local invocation sees only its coordinate line and its own scratch. -/
def localMap (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (j : Fin 3) (q : B × B) : Role n a c 0 → World B A C
  | Sum.inl i => Sum.inl (address j q (eB i))
  | Sum.inr (Sum.inl i) => Sum.inr (Sum.inl (address j q (eB i)))
  | Sum.inr (Sum.inr (Sum.inl i)) => Sum.inr (Sum.inr ((j, q), Sum.inl (eA i)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) => Sum.inr (Sum.inr ((j, q), Sum.inr (eC i)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr i))) => Fin.elim0 i

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
theorem localMap_injective (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (j : Fin 3) (q : B × B) : Function.Injective (localMap eB eA eC j q) := by
  intro i i' h
  rcases i with i | i | i | i | i <;> rcases i' with i' | i' | i' | i' | i' <;>
    simp only [localMap, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
      Prod.mk.injEq, true_and] at h ⊢
  all_goals try exact eB.injective (address_injective j q h)
  all_goals try exact eA.injective h
  all_goals try exact eC.injective h
  all_goals first | exact Fin.elim0 i | exact Fin.elim0 i'

def localEmbedding (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (j : Fin 3) (q : B × B) : Role n a c 0 ↪ World B A C :=
  ⟨localMap eB eA eC j q, localMap_injective eB eA eC j q⟩

/-- The physical stage-two order is the reversed inverse schedule, with
logical banks exchanged; it is not merely a negatively weighted forward run. -/
def localProgram (V : Fin a → Fin n → R) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) :
    Program (Role n a c 0) R :=
  if j = 1 then rename (exchangeRoles n a c 0) (dirtyInverse V G J H)
  else dirty V G J H

def invocationProgram (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (V : Fin a → Fin n → R) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) (q : B × B) :
    Program (World B A C) R :=
  embed (localEmbedding eB eA eC j q) (localProgram V G J H j)

/-- Complete contents of the physical data banks and every invocation's scratch. -/
def contents (X Y : Address B → R) (S : Invocation B × (A ⊕ C) → R) : World B A C → R :=
  Sum.elim X (Sum.elim Y S)

/-- Apply a shear only along the selected coordinate line. -/
def onLine (j : Fin 3) (q : B × B) (f g : Address B → R) : Address B → R :=
  fun b => if fixed j b = q then f b else g b

omit [CommRing R] [DecidableEq B] [DecidableEq A] [DecidableEq C] in
private theorem contents_local (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (j : Fin 3) (q : B × B) (X Y : Address B → R) (S : Invocation B × (A ⊕ C) → R) :
    contents X Y S ∘ localEmbedding eB eA eC j q =
      banks (fun i => X (address j q (eB i))) (fun i => Y (address j q (eB i)))
        (fun i => S ((j, q), Sum.inl (eA i))) (fun i => S ((j, q), Sum.inr (eC i)))
        (Fin.elim0) := by
  funext k
  rcases k with i | i | i | i | i <;> try rfl
  exact Fin.elim0 i

/-- The complete effect of one invocation on the full physical register file. -/
def invocationEffect (j : Fin 3) (q : B × B) (X Y : Address B → R)
    (S : Invocation B × (A ⊕ C) → R) : World B A C → R :=
  if j = 1 then contents (onLine j q (X - Y) X) Y S
  else contents X (onLine j q (Y + X) Y) S

/-- Every invocation is compiled from the eight row lists. Its distinct scratch
bank and all other invocations' scratch are restored for arbitrary inputs. -/
theorem invocation_run (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (V : Fin a → Fin n → R) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (reconstruct : ∀ X, mv J (mv V X) + mv H (mv G X) = X)
    (j : Fin 3) (q : B × B) (X Y : Address B → R)
    (S : Invocation B × (A ⊕ C) → R) :
    run (invocationProgram eB eA eC V G J H j q) (contents X Y S) =
      invocationEffect j q X Y S := by
  have hl : run (localProgram V G J H j)
      (contents X Y S ∘ localEmbedding eB eA eC j q) =
      invocationEffect j q X Y S ∘ localEmbedding eB eA eC j q := by
    by_cases hj : j = 1
    · simp only [localProgram, invocationEffect, hj, ↓reduceIte, contents_local,
        opposite_run V G J H reconstruct]
      simp [onLine]
      rfl
    · simp only [localProgram, invocationEffect, hj, ↓reduceIte, contents_local,
        dirty_run_shear V G J H reconstruct]
      simp [onLine]
      rfl
  funext k
  by_cases hk : ∃ i, localEmbedding eB eA eC j q i = k
  · obtain ⟨i, rfl⟩ := hk
    exact congrFun ((embed_run (localEmbedding eB eA eC j q) _ _).trans hl) i
  · have hout : ∀ i, localEmbedding eB eA eC j q i ≠ k := by simpa using hk
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
def onLines (j : Fin 3) (qs : List (B × B)) (f g : Address B → R) : Address B → R :=
  fun b => if fixed j b ∈ qs then f b else g b

omit [CommRing R] in
private theorem onLines_step (j : Fin 3) (q : B × B) (qs : List (B × B))
    (hq : q ∉ qs) (base : Address B → R) (F : Address B → R → R) :
    onLines j qs (fun b => F b (onLine j q (fun b => F b (base b)) base b))
      (onLine j q (fun b => F b (base b)) base) =
      onLines j (q :: qs) (fun b => F b (base b)) base := by
  funext b
  by_cases he : fixed j b = q
  · simp [onLines, onLine, he, hq]
  · simp [onLines, onLine, he]

/-- Flatten an explicitly enumerated finite collection of invocation programs. -/
def partialStage (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (V : Fin a → Fin n → R) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (j : Fin 3) (qs : List (B × B)) : Program (World B A C) R :=
  qs.flatMap (invocationProgram eB eA eC V G J H j)

theorem partialStage_run (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (V : Fin a → Fin n → R) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (reconstruct : ∀ X, mv J (mv V X) + mv H (mv G X) = X)
    (j : Fin 3) (qs : List (B × B)) (hq : qs.Nodup)
    (X Y : Address B → R) (S : Invocation B × (A ⊕ C) → R) :
    run (partialStage eB eA eC V G J H j qs) (contents X Y S) =
      if j = 1 then contents (onLines j qs (X - Y) X) Y S
      else contents X (onLines j qs (Y + X) Y) S := by
  induction qs generalizing X Y with
  | nil =>
    simp only [partialStage, List.flatMap_nil, run_nil]
    split <;> rfl
  | cons q qs ih =>
    obtain ⟨hmem, hnodup⟩ := List.nodup_cons.mp hq
    simp only [partialStage, List.flatMap_cons, run_append]
    rw [invocation_run eB eA eC V G J H reconstruct]
    by_cases hj : j = 1
    · subst j
      simp only [invocationEffect, ↓reduceIte]
      rw [show run (List.flatMap (invocationProgram eB eA eC V G J H 1) qs)
          (contents (onLine 1 q (X - Y) X) Y S) = _ from ih hnodup _ Y]
      simp only [↓reduceIte]
      congr 1
      exact onLines_step 1 q qs hmem X (fun b x => x - Y b)
    · simp only [invocationEffect, hj, ↓reduceIte]
      rw [show run (List.flatMap (invocationProgram eB eA eC V G J H j) qs)
          (contents X (onLine j q (Y + X) Y) S) = _ from ih hnodup X _]
      simp only [hj, ↓reduceIte]
      congr 1
      exact onLines_step j q qs hmem Y (fun b y => y + X b)

/-- Executable row-major enumeration of the two fixed coordinates. -/
def keyEquiv (eB : Fin n ≃ B) : Fin (n * n) ≃ B × B :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr eB eB)

def keys (eB : Fin n ≃ B) : List (B × B) := List.ofFn (keyEquiv eB)

omit [DecidableEq B] in
@[simp] theorem keys_nodup (eB : Fin n ≃ B) : (keys eB).Nodup :=
  List.nodup_ofFn.mpr (keyEquiv eB).injective

omit [DecidableEq B] in
@[simp] theorem mem_keys (eB : Fin n ≃ B) (q : B × B) : q ∈ keys eB :=
  List.mem_ofFn.mpr ⟨(keyEquiv eB).symm q, (keyEquiv eB).apply_symm_apply q⟩

omit [DecidableEq B] in
@[simp] theorem keys_length (eB : Fin n ≃ B) : (keys eB).length = n * n := List.length_ofFn

def stage (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (V : Fin a → Fin n → R) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) :
    Program (World B A C) R := partialStage eB eA eC V G J H j (keys eB)

/-- Every coordinate line is updated exactly once by the literal finite list. -/
theorem stage_run (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (V : Fin a → Fin n → R) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (reconstruct : ∀ X, mv J (mv V X) + mv H (mv G X) = X)
    (j : Fin 3) (X Y : Address B → R) (S : Invocation B × (A ⊕ C) → R) :
    run (stage eB eA eC V G J H j) (contents X Y S) =
      if j = 1 then contents (X - Y) Y S else contents X (Y + X) S := by
  have full (f g : Address B → R) : onLines j (keys eB) f g = f := by
    funext b
    simp only [onLines, mem_keys, ↓reduceIte]
  rw [stage, partialStage_run eB eA eC V G J H reconstruct j _ (keys_nodup eB)]
  simp only [full]

/-- Three stages, varying the first, second, and third coordinates respectively.
Their auxiliary registers are physically disjoint because the stage is part of
every scratch address. -/
def program (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (V : Fin a → Fin n → R) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) : Program (World B A C) R :=
  stage eB eA eC V G J H 0 ++ stage eB eA eC V G J H 1 ++ stage eB eA eC V G J H 2

/-- The actual global circuit performs the signed exchange on every triple
address and restores every one of the distinct invocation scratch banks. -/
theorem program_run (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (V : Fin a → Fin n → R) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (reconstruct : ∀ X, mv J (mv V X) + mv H (mv G X) = X)
    (X Y : Address B → R) (S : Invocation B × (A ⊕ C) → R) :
    run (program eB eA eC V G J H) (contents X Y S) = contents (-Y) X S := by
  simp only [program, run_append, stage_run eB eA eC V G J H reconstruct,
    show (0 : Fin 3) ≠ 1 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
  congr 1 <;> abel

@[simp] theorem localProgram_length (V : Fin a → Fin n → R) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) :
    (localProgram V G J H j).length = 4 * n + 2 * a + 2 * c := by
  unfold localProgram
  split <;> simp

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
@[simp] theorem invocationProgram_length (eB : Fin n ≃ B) (eA : Fin a ≃ A)
    (eC : Fin c ≃ C) (V : Fin a → Fin n → R) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) (q : B × B) :
    (invocationProgram eB eA eC V G J H j q).length = 4 * n + 2 * a + 2 * c := by
  simp [invocationProgram]

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
theorem partialStage_length (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (V : Fin a → Fin n → R) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) (qs : List (B × B)) :
    (partialStage eB eA eC V G J H j qs).length = qs.length * (4 * n + 2 * a + 2 * c) := by
  induction qs with
  | nil => simp [partialStage]
  | cons q qs ih =>
    simp only [partialStage, List.flatMap_cons, List.length_append, invocationProgram_length,
      List.length_cons] at *
    rw [ih]
    ring

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
theorem program_length (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (V : Fin a → Fin n → R) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) :
    (program eB eA eC V G J H).length = 3 * n ^ 2 * (4 * n + 2 * a + 2 * c) := by
  simp only [program, List.length_append, stage, partialStage_length, keys_length]
  ring

end Schedule
section Complex
open NeighborCounts

/-- Translate the actual physical side-wire enumeration to local bank indices. -/
def complexLocalPairs {h n a : ℕ} (eB : Fin n ≃ Triple h) (eA : Fin a ≃ ComplexPairs h) :
    Fin a ≃ ComplexPair (fun i => (eB i).val) :=
  eA.trans (pairsEquiv eB (@ComplexNeighbor h)).symm

/-- The global rational-scalar network on exactly the named complex wire layout.
All three stages receive distinct copies of the complete neighboring-pair bank. -/
def complexProgram {h n a : ℕ} (eB : Fin n ≃ Triple h) (eA : Fin a ≃ ComplexPairs h) :
    Program (Wires.ComplexRole h) ℚ :=
  program eB eA (Equiv.refl (Fin (h + 1)))
    (complexCopy (complexLocalPairs eB eA)) (complexGather (fun i => (eB i).val))
    (complexInject (complexLocalPairs eB eA)) (complexScatter (fun i => (eB i).val))

theorem complexProgram_run {h n a : ℕ} (eB : Fin n ≃ Triple h) (eA : Fin a ≃ ComplexPairs h)
    (X Y : Wires.Address h → ℚ)
    (S : Wires.Invocation h × (ComplexPairs h ⊕ Fin (h + 1)) → ℚ) :
    run (complexProgram eB eA) (contents X Y S) = contents (-Y) X S := by
  apply program_run
  apply complex_reconstruct
  · exact Subtype.val_injective.comp eB.injective
  · exact fun i => (eB i).property

theorem complexProgram_length {h n a : ℕ} (eB : Fin n ≃ Triple h)
    (eA : Fin a ≃ ComplexPairs h) :
    (complexProgram eB eA).length = 3 * n ^ 2 * (4 * n + 2 * a + 2 * (h + 1)) :=
  program_length _ _ _ _ _ _ _

end Complex
end IntegerMultBounds.Networks.GlobalCircuit
