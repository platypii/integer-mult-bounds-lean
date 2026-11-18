module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackFormulaInputs

/-! A finite depth-indexed layout for the recursive arithmetic compiler. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal Node
variable {T D A M : ℕ} {ι : Type}

def depth : RingFormula ι → ℕ
  | .input _ | .zero | .one => 0
  | .sub x y | .mul x y => max x.depth y.depth + 1

/-- A level uses its own operand and scratch registers; register 3 is redirected
to the parent's destination. The extra frame makes the bank total at leaf depth. -/
def frame (pool : Fin ((D+1)*13) ↪ Fin T) (l : ℕ) : Fin 13 ↪ Fin T :=
  (⟨fun i => finProdFinEquiv (⟨l % (D+1),Nat.mod_lt _ (by omega)⟩,i),
    fun _ _ h => congrArg Prod.snd (finProdFinEquiv.injective h)⟩ : Fin 13 ↪ Fin ((D+1)*13)).trans pool

def registerBank (pool : Fin ((D+1)*13) ↪ Fin T) (l : ℕ) (out : Fin T) : Fin 13 ↪ Fin T :=
  (frame pool l).trans (Equiv.swap (frame pool l 3) out).toEmbedding

private theorem separate (pool : Fin ((D+1)*13) ↪ Fin T) {l k : ℕ} (hl : l < k) (hk : k ≤ D)
    (i j : Fin 13) : frame pool k i ≠ frame pool l j := by
  intro h
  have eq := congrArg (fun t : Fin (D+1) × Fin 13 => t.1.val) (finProdFinEquiv.injective (pool.injective h))
  change k % (D+1) = l % (D+1) at eq
  rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at eq
  omega

theorem layout_prepared (pool : Fin ((D+1)*13) ↪ Fin T) (read : ι → ZMod M) (H : ℕ)
    (ready : Leaf ι → Fin T → Regs T A → Prop) (R : Regs T A) (f : RingFormula ι) (l : ℕ) (out : Fin T)
    (fits : l+f.depth ≤ D) (empty : R out = [])
    (outside : ∀ k, l ≤ k → k ≤ D → ∀ i, frame pool k i ≠ out)
    (modulus : ∀ k, l ≤ k → k ≤ D → R (frame pool k 2) = binSyms H M)
    (free : ∀ k, l ≤ k → k ≤ D → ∀ i : Fin 13, i ≠ 2 → R (frame pool k i) = [])
    (allowed : Fin T → Prop) (target : allowed out)
    (operand : ∀ k, k < D → ∀ i : Fin 13, i ≤ 1 → allowed (frame pool k i))
    (leaves : ∀ a dst, allowed dst → ready a dst R)
    (retain : ∀ a dst k xs (S : Regs T A), allowed dst → ready a dst S →
      ready a dst (Function.update S (frame pool k 0) xs)) :
    prepared (registerBank pool) read H ready f l out R := by
  induction f generalizing l out R with
  | input i => exact leaves _ _ target
  | zero => exact leaves _ _ target
  | one => exact leaves _ _ target
  | sub x y ix iy | mul x y ix iy =>
    simp only [depth] at fits
    have hl : l ≤ D := by omega
    have slot (i : Fin 13) (hi : i ≠ 3) : registerBank pool l out i = frame pool l i :=
      Equiv.swap_apply_of_ne_of_ne ((frame pool l).injective.ne hi) (outside l le_rfl hl i)
    have dest : registerBank pool l out 3 = out := Equiv.swap_apply_left ..
    refine ⟨dest,(slot 2 (by decide)) ▸ modulus l le_rfl hl,?_,?_,?_⟩
    · intro i hi _
      by_cases h : i = 3
      · simpa [h,dest] using empty
      · rw [slot i h]; exact free l le_rfl hl i hi
    · rw [slot 0 (by decide)]
      exact ix R (l+1) _ (by omega) (free _ le_rfl hl _ (by decide))
        (fun k hk hd i => separate pool hk hd i 0)
        (fun k hk => modulus k (by omega)) (fun k hk => free k (by omega)) (operand l (by omega) 0 (by decide)) leaves
    · rw [slot 0 (by decide),slot 1 (by decide)]
      apply iy _ (l+1) _ (by omega)
      · rw [Function.update_of_ne ((frame pool l).injective.ne (by decide : (1 : Fin 13) ≠ 0))]
        exact free _ le_rfl hl _ (by decide)
      · exact fun k hk hd i => separate pool hk hd i 1
      · intro k hk hd
        rw [Function.update_of_ne (separate pool hk hd 2 0)]
        exact modulus k (by omega) hd
      · intro k hk hd i hi
        rw [Function.update_of_ne (separate pool hk hd i 0)]
        exact free k (by omega) hd i hi
      · exact operand l (by omega) 1 (by decide)
      · exact fun a dst hd => retain a dst l _ _ hd (leaves a dst hd)

variable {m : ℕ} [NeZero M] {P U : Type} {Q : ℕ}

def leafBank (source : Leaf (Entry ι m) → Fin 7 ↪ Fin T) (a : Leaf (Entry ι m)) (dst : Fin T) : Fin 7 ↪ Fin T :=
  (source a).trans (Equiv.swap (source a 3) dst).toEmbedding

theorem allocated_writes (body : P → Pr P T Q A U) (pool : Fin ((D+1)*13) ↪ Fin T)
    (source : Leaf (Entry ι m) → Fin 7 ↪ Fin T) (apart : ∀ a i j, source a i ≠ pool j)
    (mat : ι → Matrix (Fin m) (Fin m) (ZMod M)) (H : ℕ) (hm : M < 2^H) (f : RingFormula (Entry ι m))
    (fits : f.depth ≤ D) (out : Fin T) (outside : ∀ j, pool j ≠ out) (dest : ∀ a i, source a i ≠ out) :
    Writes body (fun R => R out = [] ∧ (∀ k ≤ D, R (frame pool k 2) = binSyms H M) ∧
      (∀ k ≤ D, ∀ i : Fin 13, i ≠ 2 → R (frame pool k i) = []) ∧
      ∀ a, leafReady (fun b _ => source b) mat H a (source a 3) R)
      out (compile (readLeaf (leafBank source)) (registerBank pool) f 0 out)
      (binSyms H (eval (entryValue mat) f).val) (time H (readTime H) f) := by
  intro v S ⟨empty,modulus,free,inputs⟩
  apply compile_from_matrices body _ _ mat H hm f out v S
  let allowed := fun dst => ∀ a i, source a i ≠ dst
  have slot (a) (dst) (hd : allowed dst) (i : Fin 7) (hi : i ≠ 3) :
      leafBank source a dst i = source a i :=
    Equiv.swap_apply_of_ne_of_ne ((source a).injective.ne hi) (hd a i)
  apply layout_prepared pool _ H _ S.R f 0 out (by simpa using fits) empty
    (fun _ _ _ _ => outside _) (fun k _ => modulus k) (fun k _ => free k) allowed dest
    (fun _ _ _ _ a i => apart a i _)
  · intro a dst hd
    refine ⟨Equiv.swap_apply_left ..,?_⟩
    have src := inputs a
    cases a with
    | input a =>
      obtain ⟨b,i,j⟩ := a
      obtain ⟨_,h,w,s⟩ := inputs (.input (b,i,j))
      exact ⟨by rwa [slot _ _ hd 2 (by decide)],by rwa [slot _ _ hd 1 (by decide)],
        fun k hk => (slot _ _ hd k (by omega)) ▸ s k hk⟩
    | zero | one =>
      obtain ⟨_,h,w,s⟩ := src
      exact ⟨by rwa [slot _ _ hd 2 (by decide)],by rwa [slot _ _ hd 4 (by decide)],by rwa [slot _ _ hd 5 (by decide)]⟩
  · intro a dst k xs R hd h
    have keep (i : Fin 7) (hi : i ≠ 3) : Function.update R (frame pool k 0) xs (leafBank source a dst i) =
        R (leafBank source a dst i) := by
      rw [slot _ _ hd i hi]; exact Function.update_of_ne (apart a i _) _ _
    refine ⟨h.1,?_⟩
    cases a with
    | input a =>
      obtain ⟨b,i,j⟩ := a
      obtain ⟨_,h,w,s⟩ := h
      exact ⟨by rwa [keep 2 (by decide)],by rwa [keep 1 (by decide)],fun i hi => (keep i (by omega)).trans (s i hi)⟩
    | zero | one =>
      obtain ⟨_,h,w,s⟩ := h
      exact ⟨(keep 2 (by decide)).trans h,(keep 4 (by decide)).trans w,(keep 5 (by decide)).trans s⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
