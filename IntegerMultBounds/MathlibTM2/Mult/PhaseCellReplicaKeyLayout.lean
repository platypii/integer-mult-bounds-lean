module

public import IntegerMultBounds.MathlibTM2.Host.SwapList
public import Mathlib.Data.List.OfFn
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Host

/-- Rectangular packed halos, with replica outermost and key next. The last
coordinate is an arbitrary symbol inside a halo block. -/
def replicaKeyWords {α : Type*} {N K W : ℕ} (f : Fin N → Fin K → Fin W → α) : List α :=
  List.ofFn fun z : Fin (N*(K*W)) =>
    let r := finProdFinEquiv.symm z
    let k := finProdFinEquiv.symm r.2
    f r.1 k.1 k.2

/-- Complete-key order retains replica order and every symbol inside a block. -/
def keyReplicaWords {α : Type*} {N K W : ℕ} (f : Fin N → Fin K → Fin W → α) : List α :=
  replicaKeyWords (fun k r b => f r k b)

theorem replicaKeyWords_map {α β : Type*} {N K W : ℕ}
    (g : α → β) (f : Fin N → Fin K → Fin W → α) :
    (replicaKeyWords f).map g = replicaKeyWords (fun r k b => g (f r k b)) := by
  simp [replicaKeyWords,List.map_ofFn,Function.comp_def]

theorem keyReplicaWords_map {α β : Type*} {N K W : ℕ}
    (g : α → β) (f : Fin N → Fin K → Fin W → α) :
    (keyReplicaWords f).map g = keyReplicaWords (fun r k b => g (f r k b)) :=
  replicaKeyWords_map g (fun k r b => f r k b)

theorem zipWith_ofFn_same {α β γ : Type*} {n : ℕ} (op : α → β → γ)
    (f : Fin n → α) (g : Fin n → β) :
    List.zipWith op (List.ofFn f) (List.ofFn g) = List.ofFn (fun i => op (f i) (g i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.ofFn_succ,List.zipWith_cons_cons,ih]

theorem replicaKeyWords_zipWith {α β γ : Type*} {N K W : ℕ}
    (op : α → β → γ) (f : Fin N → Fin K → Fin W → α) (g : Fin N → Fin K → Fin W → β) :
    List.zipWith op (replicaKeyWords f) (replicaKeyWords g) =
      replicaKeyWords (fun r k b => op (f r k b) (g r k b)) := by
  simp only [replicaKeyWords,zipWith_ofFn_same]

theorem keyReplicaWords_zipWith {α β γ : Type*} {N K W : ℕ}
    (op : α → β → γ) (f : Fin N → Fin K → Fin W → α) (g : Fin N → Fin K → Fin W → β) :
    List.zipWith op (keyReplicaWords f) (keyReplicaWords g) =
      keyReplicaWords (fun r k b => op (f r k b) (g r k b)) := by
  simp only [keyReplicaWords,replicaKeyWords,zipWith_ofFn_same]

/-- Any correctly sized owned word has a finite-array view; no encoding
certificate or concrete enumeration is needed. -/
theorem listArray_of_length {α : Type*} {V : ℕ} (xs : List α) (hlen : xs.length = V) :
    ∃ x : Fin V → α, List.ofFn x = xs := by
  subst V
  exact ⟨xs.get,List.ofFn_get xs⟩

/-- Recover a rectangular view of an actual owned word, including padded tiles. -/
theorem replicaKeyWords_of_length {α : Type*} {N K W : ℕ} (xs : List α)
    (hlen : xs.length = N*(K*W)) :
    ∃ f : Fin N → Fin K → Fin W → α, replicaKeyWords f = xs := by
  obtain ⟨x,hx⟩ := listArray_of_length xs hlen
  refine ⟨fun r k b => x (finProdFinEquiv (r,finProdFinEquiv (k,b))),?_⟩
  rw [←hx]
  unfold replicaKeyWords
  apply congrArg List.ofFn
  funext i
  dsimp only
  simp only [Prod.mk.eta,Equiv.apply_symm_apply]

/-- Supply the finite-array view required by the existing tape interchange. -/
theorem replicaKeyWords_array {α : Type*} {N K W : ℕ}
    (f : Fin N → Fin K → Fin W → α) (V : ℕ) (hV : V = N*(K*W)) :
    ∃ x : Fin V → α, List.ofFn x = replicaKeyWords f := by
  subst V
  exact ⟨_,rfl⟩

theorem replicaKeyWords_getElem? {α : Type*} {N K W : ℕ}
    (f : Fin N → Fin K → Fin W → α) (r : Fin N) (k : Fin K) (b : Fin W) :
    (replicaKeyWords f)[(r.val*K+k.val)*W+b.val]? = some (f r k b) := by
  have hi : (r.val*K+k.val)*W+b.val < N*(K*W) := by
    simpa only [Nat.mul_assoc] using mix_lt (mix_lt r.isLt k.isLt) b.isLt
  have hz : (⟨(r.val*K+k.val)*W+b.val,hi⟩ : Fin (N*(K*W))) =
      finProdFinEquiv (r,finProdFinEquiv (k,b)) := by
    apply Fin.ext
    change (r.val*K+k.val)*W+b.val = (b.val+W*k.val)+(K*W)*r.val
    simp only [Nat.add_mul,Nat.mul_assoc]
    ac_rfl
  simp only [replicaKeyWords,List.getElem?_ofFn,dite_eq_left hi,hz,Equiv.symm_apply_apply]

/-- Flattening a rectangular function is independent of its index encoding. -/
theorem ofFn_finProd {α : Type*} {m n : ℕ} (f : Fin m → Fin n → α) :
    (List.ofFn fun z : Fin (m*n) => f (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2) =
      (List.ofFn fun i => List.ofFn fun j => f i j).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hz : (⟨i.val*n+j.val,mix_lt i.isLt j.isLt⟩ : Fin (m*n)) =
      finProdFinEquiv (i,j) := by
    apply Fin.ext
    change i.val*n+j.val = j.val+n*i.val
    ac_rfl
  rw [hz]
  simp only [Equiv.symm_apply_apply]

/-- The grouped stream is a concatenation of one complete replica batch per
key. Each replica contributes one unchanged fixed-size halo block. -/
theorem keyReplicaWords_blocks {α : Type*} {N K W : ℕ} (f : Fin N → Fin K → Fin W → α) :
    keyReplicaWords f =
      (List.ofFn fun k : Fin K => (List.ofFn fun r : Fin N => List.ofFn fun b : Fin W => f r k b).flatten).flatten := by
  let g : Fin K → Fin (N*W) → α := fun k z =>
    f (finProdFinEquiv.symm z).1 k (finProdFinEquiv.symm z).2
  change (List.ofFn fun z : Fin (K*(N*W)) => g (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2) = _
  rw [ofFn_finProd g]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext k
  exact ofFn_finProd (fun r b => f r k b)

/-- One rectangular interchange changes replica-major into complete-key-major
order. No halo contents are inspected, and no individual key cases are generated. -/
theorem replicaKeyWords_swap {α : Type*} {N K W : ℕ} (dflt : α)
    (f : Fin N → Fin K → Fin W → α) :
    swapList 1 N 1 K W dflt (replicaKeyWords f) = keyReplicaWords f := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < K*(N*W)
  · let z : Fin (K*(N*W)) := ⟨i,hi⟩
    let p := finProdFinEquiv.symm z
    let rb := finProdFinEquiv.symm p.2
    have hz : finProdFinEquiv (p.1,finProdFinEquiv (rb.1,rb.2)) = z := by
      have hrb : finProdFinEquiv rb = p.2 := Equiv.apply_symm_apply _ _
      have hp : finProdFinEquiv p = z := Equiv.apply_symm_apply _ _
      simpa only [Prod.mk.eta,hrb] using hp
    have hindex : (p.1.val*N+rb.1.val)*W+rb.2.val = i := by
      have hh := congrArg Fin.val hz
      change (rb.2.val+W*rb.1.val)+(N*W)*p.1.val = i at hh
      have ha : (p.1.val*N+rb.1.val)*W+rb.2.val = (rb.2.val+W*rb.1.val)+(N*W)*p.1.val := by
        simp only [Nat.add_mul,Nat.mul_assoc]
        ac_rfl
      exact ha.trans hh
    rw [←hindex]
    have hs := swapList_getElem? dflt (replicaKeyWords f)
      (by simp [replicaKeyWords,Nat.mul_assoc])
      (p := 0) (h := rb.1.val) (g := 0) (d := p.1.val) (b := rb.2.val)
      (by decide : 0 < 1) rb.1.isLt (by decide : 0 < 1) p.1.isLt rb.2.isLt
    simp only [Nat.zero_mul,Nat.zero_add,Nat.mul_one,Nat.add_zero] at hs
    rw [hs,replicaKeyWords_getElem?]
    exact (replicaKeyWords_getElem? (fun k r b => f r k b) p.1 rb.1 rb.2).symm
  · have hlen₁ : (swapList 1 N 1 K W dflt (replicaKeyWords f)).length = K*(N*W) := by
      simp [swapList,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    have hlen₂ : (keyReplicaWords f).length = K*(N*W) := by simp [keyReplicaWords,replicaKeyWords]
    rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
