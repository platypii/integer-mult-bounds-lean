import IntegerMultBounds.Networks.CircuitCoefficients
import IntegerMultBounds.Networks.GlobalGrouped

/-! Static coefficient bounds of the exact sparse grouped compiler, including
inverse stage orientation and every physical invocation embedding. -/
namespace IntegerMultBounds.Networks.GroupedCoefficients
open Circuit GroupedCircuit CircuitCoefficients
variable {ι κ R : Type*} [CommRing R] [DecidableEq R] [DecidableEq ι] [DecidableEq κ]

def AllGroups (P : R → Prop) (gs : List (Group ι R)) := ∀ g ∈ gs,CircuitCoefficients.All P g.rows

omit [DecidableEq ι] in
theorem compile (P : R → Prop) (g : Group ι R) (h : CircuitCoefficients.All P g.rows) :
    CircuitCoefficients.All P (GroupedCircuit.compile g) := by
  intro row hr t ht
  obtain ⟨row0,hr0,rfl⟩ := List.mem_map.mp hr
  exact h row0 hr0 t (List.mem_filter.mp ht).1

omit [DecidableEq ι] in
theorem compileGroups (P : R → Prop) (gs : List (Group ι R)) (h : AllGroups P gs) :
    CircuitCoefficients.All P (GroupedCircuit.compileGroups gs) := by
  intro row hr t ht
  obtain ⟨g,hg,hr⟩ := List.mem_flatMap.mp hr
  exact compile P g (h g hg) row hr t ht

omit [DecidableEq R] [DecidableEq ι] in
theorem matrix {n m : ℕ} (P : R → Prop) (dst : Fin n → ι) (src : Fin m → ι)
    (M : Fin n → Fin m → R) (sep : ∀ i j,dst i≠src j) (h : ∀ i j,P (M i j)) :
    CircuitCoefficients.All P (matrixGroup dst src M sep).rows := CircuitCoefficients.block P dst src M h

omit [DecidableEq R] [DecidableEq ι] in
theorem fanin {n m : ℕ} (P : R → Prop) (dst : Fin n → ι) (src : Fin m → ι)
    (M : Fin n → Fin m → R) (sep : ∀ i j,dst i≠src j) (h : ∀ i j,P (M i j)) :
    AllGroups P (faninGroups dst src M sep) := by
  intro g hg
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hg
  exact matrix P _ _ _ _ (fun _ j => h i j)

omit [DecidableEq ι] in
theorem copy {n a : ℕ} (P : R → Prop) (dst : Fin a → ι) (src : Fin n → ι)
    (owner : Fin a → Fin n) (c : R) (sep : ∀ i j,dst i≠src j) (hc : P c) (h0 : P 0) :
    AllGroups P (copyGroups dst src owner c sep) := by
  intro g hg row hr t ht
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hg
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
  have he := List.mem_singleton.mp ht
  subst t
  change P (if owner i=j then c else 0)
  split_ifs <;> assumption

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq R] in
theorem rename (P : R → Prop) (e : ι ≃ κ) (gs : List (Group ι R)) (h : AllGroups P gs) :
    AllGroups P (GroupedCircuit.renameGroups e gs) := by
  intro g hg
  obtain ⟨g0,hg0,rfl⟩ := List.mem_map.mp hg
  exact CircuitCoefficients.rename P e g0.rows (h g0 hg0)

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq R] in
theorem embed (P : R → Prop) (e : ι ↪ κ) (gs : List (Group ι R)) (h : AllGroups P gs) :
    AllGroups P (GlobalGrouped.embedGroups e gs) := by
  intro g hg
  obtain ⟨g0,hg0,rfl⟩ := List.mem_map.mp hg
  exact CircuitCoefficients.embed P e g0.rows (h g0 hg0)

omit [DecidableEq ι] [DecidableEq R] in
theorem append (P : R → Prop) (gs hs : List (Group ι R)) (hg : AllGroups P gs) (hh : AllGroups P hs) :
    AllGroups P (gs++hs) := by
  intro g h
  rcases List.mem_append.mp h with h | h
  · exact hg g h
  · exact hh g h

omit [DecidableEq ι] [DecidableEq R] in
theorem singleton (P : R → Prop) (g : Group ι R) (h : CircuitCoefficients.All P g.rows) :
    AllGroups P [g] := by
  intro g0 hg
  have he := List.mem_singleton.mp hg
  subst g0
  exact h

variable {n a c z : ℕ}

theorem dirty (P : R → Prop) (hn : ∀ x,P x → P (-x)) (h0 : P 0) (h1 : P 1)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (hG : ∀ i j,P (G i j)) (hJ : ∀ i j,P (J i j)) (hH : ∀ i j,P (H i j)) :
    AllGroups P (dirtyGroups (s := z) owner G J H) := by
  unfold dirtyGroups
  repeat' apply append
  all_goals first | apply fanin | apply singleton; apply matrix | apply copy
  all_goals first | exact hG | exact hJ | exact hH | exact h0 | exact h1 | exact hn _ h1 |
    exact fun i j => hn _ (hG i j) | exact fun i j => hn _ (hJ i j) | exact fun i j => hn _ (hH i j)

theorem inverse (P : R → Prop) (hn : ∀ x,P x → P (-x)) (h0 : P 0) (h1 : P 1)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (hG : ∀ i j,P (G i j)) (hJ : ∀ i j,P (J i j)) (hH : ∀ i j,P (H i j)) :
    AllGroups P (dirtyInverseGroups (s := z) owner G J H) := by
  unfold dirtyInverseGroups
  repeat' apply append
  all_goals first | apply fanin | apply singleton; apply matrix | apply copy
  all_goals first | exact hG | exact hJ | exact hH | exact h0 | exact h1 | exact hn _ h1 |
    exact fun i j => hn _ (hG i j) | exact fun i j => hn _ (hJ i j) | exact fun i j => hn _ (hH i j)

variable {B A C : Type*}

theorem global (P : R → Prop) (hn : ∀ x,P x → P (-x)) (h0 : P 0) (h1 : P 1)
    (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (hG : ∀ i j,P (G i j)) (hJ : ∀ i j,P (J i j)) (hH : ∀ i j,P (H i j)) :
    AllGroups P (GlobalGrouped.program eB eA eC owner G J H) := by
  have hl (j : Fin 3) : AllGroups P (GlobalGrouped.localGroups owner G J H j) := by
    unfold GlobalGrouped.localGroups
    split_ifs
    · exact rename P _ _ (inverse P hn h0 h1 owner G J H hG hJ hH)
    · exact dirty P hn h0 h1 owner G J H hG hJ hH
  have hs (j : Fin 3) : AllGroups P (GlobalGrouped.stage eB eA eC owner G J H j) := by
    intro g hg
    obtain ⟨q,_,hg⟩ := List.mem_flatMap.mp hg
    exact embed P _ _ (hl j) g hg
  unfold GlobalGrouped.program
  exact append P _ _ (append P _ _ (hs 0) (hs 1)) (hs 2)

end IntegerMultBounds.Networks.GroupedCoefficients
