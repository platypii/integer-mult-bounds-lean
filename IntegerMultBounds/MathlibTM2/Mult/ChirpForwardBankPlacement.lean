module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardConsumers

/-! # A fixed allocation of the scalar source and all five consumer banks

193 tapes hold the 16-variable source and consumers of sizes 10,10,14,48,5.
Each bank owns its variables, three headers/accumulator roles and twelve scratch
roles. This allocation does not include correlation or output arithmetic tapes.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.ForwardBankPlacement

open IntegerMultBounds.MathlibTM2.Fast.TableVM

def code {n : ℕ} : TblR n → Fin (n + 15)
  | .v i => ⟨i.val, by omega⟩
  | .wr => ⟨n, by omega⟩
  | .wn => ⟨n + 1, by omega⟩
  | .acc => ⟨n + 2, by omega⟩
  | .z i => ⟨n + 3 + i.val, by omega⟩

theorem code_injective {n : ℕ} : Function.Injective (@code n) := by
  intro r s h
  have hv := congrArg Fin.val h
  cases r <;> cases s <;> simp only [code] at hv
  all_goals first
    | rfl
    | (congr 1; apply Fin.ext; omega)
    | omega

def place {n : ℕ} (offset : ℕ) (h : offset + (n + 15) ≤ 193) (r : TblR n) : Fin 193 :=
  ⟨offset + (code r).val, by have := (code r).isLt; omega⟩

theorem place_injective {n : ℕ} (offset : ℕ) (h : offset + (n + 15) ≤ 193) :
    Function.Injective (place offset h) := by
  intro r s he
  apply code_injective
  apply Fin.ext
  have hv := congrArg Fin.val he
  simp only [place] at hv
  omega

theorem place_disjoint {n m : ℕ} (a b : ℕ)
    (ha : a + (n + 15) ≤ 193) (hb : b + (m + 15) ≤ 193)
    (hab : a + (n + 15) ≤ b) (r : TblR n) (s : TblR m) :
    place a ha r ≠ place b hb s := by
  intro he
  have hv := congrArg Fin.val he
  have := (code r).isLt
  simp only [place] at hv
  omega

def source : TblR 16 → Fin 193 := place 0 (by decide)
def gather : TblR 10 → Fin 193 := place 31 (by decide)
def convolution : TblR 10 → Fin 193 := place 56 (by decide)
def output : TblR 14 → Fin 193 := place 81 (by decide)
def coefficient : TblR 48 → Fin 193 := place 110 (by decide)
def multiplier : TblR 5 → Fin 193 := place 173 (by decide)

def consumers : List (ChirpBankTarget 16 193) :=
  chirpForwardConsumers gather convolution output coefficient multiplier

theorem source_injective : Function.Injective source := place_injective _ _

theorem consumers_injective : ∀ b ∈ consumers, Function.Injective b.rg := by
  intro b hb
  simp only [consumers, chirpForwardConsumers, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  all_goals exact place_injective _ (by decide)

theorem consumers_source : ∀ b ∈ consumers, ∀ r s, b.rg r ≠ source s := by
  intro b hb
  simp only [consumers, chirpForwardConsumers, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  all_goals
    intro r s
    exact (place_disjoint _ _ (by decide) (by decide) (by decide) s r).symm

theorem consumers_pairwise : consumers.Pairwise (fun b c => ∀ r s, b.rg r ≠ c.rg s) := by
  simp only [consumers, chirpForwardConsumers, List.pairwise_cons, List.mem_cons,
    List.not_mem_nil, or_false]
  simp only [List.Pairwise.nil, and_true]
  repeat' constructor
  all_goals
    intro b hb
    rcases hb with rfl | rfl | rfl | rfl
    all_goals exact place_disjoint _ _ (by decide) (by decide) (by decide)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.ForwardBankPlacement
