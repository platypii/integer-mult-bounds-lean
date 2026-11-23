module

public import IntegerMultBounds.MathlibTM2.Cover.LabelPermutation
public import IntegerMultBounds.MathlibTM2.Cover.LabelPass

/-! Lifting a pass on each contiguous label box to the caller's addresses. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelTransport
noncomputable section

open IntegerMultBounds.Machine
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (Descriptor index)
open LabelPermutation (Transport Moves)
open LabelAddress (address)
open Matrix
variable {m w B : ℕ} {v : Descriptor}
local instance : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

/-- Each label has this many consecutive payload symbols. -/
def payload (v : Descriptor) := prime^v.width*v.between*prime^v.width*v.afterD

/-- Transporting a contiguous box at every prefix suffices on the original descriptor. -/
theorem of_boxes {f : Matrix (Fin m) (Fin m) (ZMod (prime^w)) → Matrix (Fin m) (Fin m) (ZMod (prime^w))}
    {x y : ℕ → ZMod 2} (hv : v.beforeH = B*prime^(m*(w*m)))
    (hbox : ∀ p < v.beforeRows*v.rows*B, ∀ g j, j < payload v →
      y ((p*prime^(m*(w*m)) + (address (f g)).val)*payload v+j) =
        x ((p*prime^(m*(w*m)) + (address g).val)*payload v+j)) :
    Transport v B w f x y := by
  intro g a ha row hr b hb h hh mid hm d hd after he
  have pack {a A b B : ℕ} (ha : a < A) (hb : b < B) : a*B+b < A*B := by nlinarith
  have key := hbox ((a*v.rows+row)*B+b) (pack (pack ha hr) hb) g
    (((h*v.between+mid)*prime^v.width+d)*v.afterD+after) (pack (pack (pack hh hm) hd) he)
  convert key using 2 <;> unfold index payload <;> rw [hv] <;> ring

/-- The output of the compiled scalar schedule on each contiguous prefix block. -/
theorem triangular {E : Matrix (Fin m) (Fin m) ℚ}
    (hs : ∀ op ∈ LabelAddress.pass E, FlatCoordinateSchedule.Supported op)
    (hE : IntegerMultBounds.Swap.Shear.LowerTriangular E)
    (hu : IsUnit (IntegerMultBounds.Swap.Modular.reduce (prime^w) E))
    (hv : v.beforeH = B*prime^(m*(w*m))) (hW : 0 < payload v)
    {x y : ℕ → ZMod 2} (decode : Fin 4 → ZMod 2)
    (a : ℕ → FlatCoordinateStages.Array (m*m) w (payload v))
    (hin : ∀ p < v.beforeRows*v.rows*B, ∀ i, x (p*(prime^w)^(m*m)*payload v + i.val) = decode (a p i))
    (hout : ∀ p < v.beforeRows*v.rows*B, ∀ i, y (p*(prime^w)^(m*m)*payload v + i.val) =
      decode (FlatCoordinateInitializedSchedule.array
        (FlatCoordinateSchedule.ofList (LabelAddress.pass E) hs) w (payload v) hW (a p) i)) :
    Transport v B w (fun g => g * (IntegerMultBounds.Swap.Modular.reduce (prime^w) E)ᵀ) x y := by
  apply of_boxes hv
  intro p hp g j hj
  let pos (g : Matrix (Fin m) (Fin m) (ZMod (prime^w))) :=
    finProdFinEquiv (address g, (⟨j,hj⟩ : Fin (payload v)))
  have hi (g : Matrix (Fin m) (Fin m) (ZMod (prime^w))) :
      (p*prime^(m*(w*m))+(address g).val)*payload v+j =
        p*(prime^w)^(m*m)*payload v+(pos g).val := by
    have hex : m*(w*m) = w*(m*m) := by ring
    rw [hex, pow_mul]
    simp only [pos, finProdFinEquiv_apply_val]
    ring
  rw [hi, hi, hout p hp (pos (g * (IntegerMultBounds.Swap.Modular.reduce (prime^w) E)ᵀ)), hin p hp (pos g)]
  have hr := LabelPass.realizes E hs w (payload v) hW hE hu (a p)
  obtain ⟨_, _, _, _, _, _, hentries⟩ := hr _ rfl
  exact congrArg decode (hentries g ⟨j,hj⟩)

/-- For the transposed factorization, the second factor runs first on a label. -/
theorem route_rows {k : ℕ} {σ E₁ E₂ : Matrix (Fin m) (Fin m) (ZMod (prime^w))} {L : List (Fin m × Fin m)}
    (hL : L.Nodup) (π : Equiv.Perm (Fin m)) (hπ : ∀ j k, (j,k) ∈ L ↔ k = π j)
    (hσ : σᵀ = E₁ * IntegerMultBounds.Swap.Shear.pivotMatrix L * E₂)
    {x y z out : ℕ → ZMod 2}
    (h₂ : LabelPermutation.RowTransport v B w k (fun g => g * E₂ᵀ) x y) (hp : LabelPermutation.RowMoves v B w k π y z)
    (h₁ : LabelPermutation.RowTransport v B w k (fun g => g * E₁ᵀ) z out) :
    LabelPermutation.RowTransport v B w k (fun g => g * σ) x out := by
  intro g a ha row hr b hb h hh mid hm d hd after he
  let g₂ := g * E₂ᵀ
  have pivot : (fun i j => g₂ i (π j)) =
      g₂ * (IntegerMultBounds.Swap.Shear.pivotMatrix L : Matrix (Fin m) (Fin m) (ZMod (prime^w)))ᵀ := by
    funext i j
    simp [Matrix.mul_apply, IntegerMultBounds.Swap.PivotRank.pivotMatrix_apply L hL, hπ]
  have hdest : (show Matrix (Fin k) (Fin m) _ from fun i j => g₂ i (π j)) * E₁ᵀ = g * σ := by
    rw [pivot, ← transpose_transpose σ, hσ]
    simp [g₂, transpose_mul, Matrix.mul_assoc]
  dsimp only
  rw [← hdest]
  exact (h₁ _ a ha row hr b hb h hh mid hm d hd after he).trans
    ((hp g₂ a ha row hr b hb h hh mid hm d hd after he).trans (h₂ g a ha row hr b hb h hh mid hm d hd after he))

theorem route {σ E₁ E₂ : Matrix (Fin m) (Fin m) (ZMod (prime^w))} {L : List (Fin m × Fin m)}
    (hL : L.Nodup) (π : Equiv.Perm (Fin m)) (hπ : ∀ j k, (j,k) ∈ L ↔ k = π j)
    (hσ : σᵀ = E₁ * IntegerMultBounds.Swap.Shear.pivotMatrix L * E₂)
    {x y z out : ℕ → ZMod 2}
    (h₂ : Transport v B w (fun g => g * E₂ᵀ) x y) (hp : Moves v B w π y z)
    (h₁ : Transport v B w (fun g => g * E₁ᵀ) z out) :
    Transport v B w (fun g => g * σ) x out := route_rows hL π hπ hσ h₂ hp h₁

end
end IntegerMultBounds.MathlibTM2.Cover.LabelTransport
