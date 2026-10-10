import IntegerMultBounds.Schoenhage.SSClean
import IntegerMultBounds.Schoenhage.Relabel

/-! The bank of the packed ring product: the multiplier's 64 tapes followed by
twenty tapes of its own. Programs on the multiplier's bank run on the first
64 tapes (`up`); an exact effect there is the same effect on the larger
bank, the other tapes untouched (`runs_up`). -/

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp

/-- The number of tapes of the ring product machine. -/
scoped notation "𝕌" => (84 : ℕ)

/-- The multiplier's tapes inside the larger bank. -/
def ι : Fin 𝕋 → Fin 𝕌 := Fin.castLE (by norm_num)

theorem ι_injective : Function.Injective ι := Fin.castLE_injective _

@[simp] theorem ι_val (i : Fin 𝕋) : (ι i).val = i.val := rfl

/-- A program of the multiplier's bank on the first tapes of the larger bank. -/
def up (c : Cmd 0 𝕋) : Cmd 0 𝕌 := c.map ι ι_injective

/-- Replace the first 64 tapes of `τ` by `σ`. -/
def ext (τ : Fin 𝕌 → WTape) (σ : Fin 𝕋 → WTape) : Fin 𝕌 → WTape :=
  fun x => if h : x.val < 64 then σ ⟨x.val, h⟩ else τ x

theorem ext_self (τ : Fin 𝕌 → WTape) : ext τ (τ ∘ ι) = τ := by
  funext x
  unfold ext
  split_ifs with h
  · rfl
  · rfl

theorem ext_update (τ : Fin 𝕌 → WTape) (σ : Fin 𝕋 → WTape) (i : Fin 𝕋) (v : WTape) :
    ext τ (Function.update σ i v) = Function.update (ext τ σ) (ι i) v := by
  funext x
  unfold ext
  by_cases hx : x = ι i
  · subst hx; simp
  · rw [Function.update_of_ne hx]
    split_ifs with h
    · have : (⟨x.val, h⟩ : Fin 𝕋) ≠ i := fun e => hx (by ext; simp [← e])
      rw [Function.update_of_ne this]
    · rfl

theorem comp_ι_update (τ : Fin 𝕌 → WTape) (i : Fin 𝕋) (v : WTape) :
    Function.update τ (ι i) v ∘ ι = Function.update (τ ∘ ι) i v := by
  funext x
  simp only [Function.comp_apply]
  by_cases hx : x = i
  · subst hx; simp
  · rw [Function.update_of_ne (fun e => hx (ι_injective e)), Function.update_of_ne hx]
    rfl

theorem runs_up {c : Cmd 0 𝕋} {τ : Fin 𝕌 → WTape} {σ' : Fin 𝕋 → WTape} {B : ℕ}
    (h : Runs c (τ ∘ ι) (· = σ') B) : Runs (up c) τ (· = ext τ σ') B := by
  refine (h.map ι ι_injective τ rfl).mono (fun τ' ⟨hq, ho⟩ => ?_) le_rfl
  funext x
  unfold ext
  split_ifs with hx
  · rw [← hq]; rfl
  · exact ho x (fun y e => hx (by rw [← e]; exact y.isLt))

theorem eq_ext {τ τ' : Fin 𝕌 → WTape} {σ : Fin 𝕋 → WTape} (h1 : ∀ i, τ' (ι i) = σ i)
    (h2 : ∀ x : Fin 𝕌, 64 ≤ x.val → τ' x = τ x) : τ' = ext τ σ := by
  funext x
  unfold ext
  split_ifs with hx
  · exact h1 ⟨x.val, hx⟩
  · exact h2 x (by omega)

/-- A lifted run whose result is stated on the larger bank. -/
theorem runs_up' {c : Cmd 0 𝕋} {τ τ' : Fin 𝕌 → WTape} {σ' : Fin 𝕋 → WTape} {B : ℕ}
    (h : Runs c (τ ∘ ι) (· = σ') B) (e : ext τ σ' = τ') : Runs (up c) τ (· = τ') B :=
  e ▸ runs_up h

/-! ### The ring product's own tapes -/

namespace Tp
abbrev rF : Fin 𝕌 := 64
abbrev rG : Fin 𝕌 := 65
abbrev rO : Fin 𝕌 := 66
abbrev kW : Fin 𝕌 := 67
abbrev kN : Fin 𝕌 := 68
abbrev kR : Fin 𝕌 := 69
abbrev kI : Fin 𝕌 := 70
abbrev kO : Fin 𝕌 := 71
abbrev kS : Fin 𝕌 := 72
abbrev kH : Fin 𝕌 := 73
abbrev kw : Fin 𝕌 := 74
abbrev kC : Fin 𝕌 := 75
abbrev xA : Fin 𝕌 := 76
abbrev xB : Fin 𝕌 := 77
abbrev xC : Fin 𝕌 := 78
abbrev xE : Fin 𝕌 := 79
abbrev xP : Fin 𝕌 := 80
abbrev xQ : Fin 𝕌 := 81
abbrev lR : Fin 𝕌 := 82
abbrev lI : Fin 𝕌 := 83
end Tp

end IntegerMultBounds.Schoenhage
