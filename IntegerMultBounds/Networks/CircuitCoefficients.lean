import IntegerMultBounds.Networks.GlobalCircuit

/-! Static coefficient certificates survive literal block, inverse, role
renaming and global invocation compilation. No execution premise is used. -/
namespace IntegerMultBounds.Networks.CircuitCoefficients
open Circuit
variable {ι κ R : Type*} [CommRing R] [DecidableEq ι] [DecidableEq κ]

def All (P : R → Prop) (gs : Program ι R) := ∀ g ∈ gs,∀ t ∈ g.terms,P t.2

omit [CommRing R] [DecidableEq ι] in
theorem append (P : R → Prop) (gs hs : Program ι R) (hg : All P gs) (hh : All P hs) :
    All P (gs++hs) := by
  intro g h t ht
  rcases List.mem_append.mp h with h | h
  · exact hg g h t ht
  · exact hh g h t ht

omit [CommRing R] [DecidableEq ι] in
theorem block {n m : ℕ} (P : R → Prop) (dst : Fin n → ι) (src : Fin m → ι)
    (M : Fin n → Fin m → R) (h : ∀ i j,P (M i j)) : All P (Circuit.block dst src M) := by
  intro g hg t ht
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hg
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht
  exact h i j

omit [CommRing R] [DecidableEq ι] [DecidableEq κ] in
theorem rename (P : R → Prop) (e : ι ≃ κ) (gs : Program ι R) (h : All P gs) :
    All P (Circuit.rename e gs) := by
  intro g hg t ht
  change g∈gs.map (Gate.rename e) at hg
  obtain ⟨g0,hg0,rfl⟩ := List.mem_map.mp hg
  obtain ⟨t0,ht0,rfl⟩ := List.mem_map.mp ht
  exact h g0 hg0 t0 ht0

omit [CommRing R] [DecidableEq ι] [DecidableEq κ] in
theorem embed (P : R → Prop) (e : ι ↪ κ) (gs : Program ι R) (h : All P gs) :
    All P (GlobalCircuit.embed e gs) := by
  intro g hg t ht
  change g∈gs.map (GlobalCircuit.embedGate e) at hg
  obtain ⟨g0,hg0,rfl⟩ := List.mem_map.mp hg
  obtain ⟨t0,ht0,rfl⟩ := List.mem_map.mp ht
  exact h g0 hg0 t0 ht0

theorem dirty {n a c z : ℕ} (P : R → Prop) (hn : ∀ x,P x → P (-x))
    (V : Fin a → Fin n → R) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (hV : ∀ i j,P (V i j)) (hG : ∀ i j,P (G i j))
    (hJ : ∀ i j,P (J i j)) (hH : ∀ i j,P (H i j)) :
    All P (Circuit.dirty (s := z) V G J H) := by
  unfold Circuit.dirty
  repeat' apply append
  all_goals apply block
  all_goals first | exact hV | exact hG | exact hJ | exact hH |
    exact fun i j => hn _ (hV i j) | exact fun i j => hn _ (hG i j) |
    exact fun i j => hn _ (hJ i j) | exact fun i j => hn _ (hH i j)

theorem dirtyInverse {n a c z : ℕ} (P : R → Prop) (hn : ∀ x,P x → P (-x))
    (V : Fin a → Fin n → R) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (hV : ∀ i j,P (V i j)) (hG : ∀ i j,P (G i j))
    (hJ : ∀ i j,P (J i j)) (hH : ∀ i j,P (H i j)) :
    All P (Circuit.dirtyInverse (s := z) V G J H) := by
  unfold Circuit.dirtyInverse
  repeat' apply append
  all_goals apply block
  all_goals first | exact hV | exact hG | exact hJ | exact hH |
    exact fun i j => hn _ (hV i j) | exact fun i j => hn _ (hG i j) |
    exact fun i j => hn _ (hJ i j) | exact fun i j => hn _ (hH i j)

variable {B A C : Type*} [DecidableEq B] [DecidableEq A] [DecidableEq C]
variable {n a c : ℕ}

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq B] [DecidableEq A] [DecidableEq C] in
theorem global (P : R → Prop) (hn : ∀ x,P x → P (-x))
    (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (V : Fin a → Fin n → R) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (hV : ∀ i j,P (V i j)) (hG : ∀ i j,P (G i j))
    (hJ : ∀ i j,P (J i j)) (hH : ∀ i j,P (H i j)) :
    All P (GlobalCircuit.program eB eA eC V G J H) := by
  have hlocal (j : Fin 3) : All P (GlobalCircuit.localProgram V G J H j) := by
    unfold GlobalCircuit.localProgram
    split_ifs
    · exact rename P _ _ (dirtyInverse P hn V G J H hV hG hJ hH)
    · exact dirty P hn V G J H hV hG hJ hH
  have hstage (j : Fin 3) : All P (GlobalCircuit.stage eB eA eC V G J H j) := by
    intro g hg t ht
    obtain ⟨q,_,hmem⟩ := List.mem_flatMap.mp hg
    exact embed P _ _ (hlocal j) g hmem t ht
  unfold GlobalCircuit.program
  exact append P _ _ (append P _ _ (hstage 0) (hstage 1)) (hstage 2)

end IntegerMultBounds.Networks.CircuitCoefficients
