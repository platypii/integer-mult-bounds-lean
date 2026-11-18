module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSign
public import IntegerMultBounds.MathlibTM2.Cover.ResiduePivots
public import IntegerMultBounds.MathlibTM2.Cover.LabelTraversal

/-! A physical stream of fallback signs, in label-record order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime prime_odd)
open Host LabelTraversal LabelCycle
local instance : Fact prime.Prime := ⟨prime_prime⟩
variable {m n T Q A : ℕ} {P U : Type}

/-- Choose one pivot itinerary per residue matrix. Singular padding has no pivot obligation. -/
def classPivots (M : Matrix (Fin n) (Fin n) (ZMod prime)) : Fin n → Fin n :=
  if M.det = 0 then id else (Itinerary.pivotStages M n).1

theorem classPivots_valid (M : Matrix (Fin n) (Fin n) (ZMod prime)) (h : IsUnit M.det) :
    Itinerary.Valid (classPivots M) M n := by
  simpa [classPivots,h.ne_zero] using (Itinerary.pivotStages_spec M h n le_rfl).1

def signStream (residualClass : Matrix (Fin m) (Fin m) (ZMod prime) →
    Matrix (Fin n) (Fin n) (ZMod prime)) (w N : ℕ) : List (Fin (A+4)) :=
  (List.range N).map fun j =>
    let M := residualClass (LabelStock.residue m w 1 j)
    bitSymbol (negativeAnchor (classPivots M) M)

theorem signStream_writes (body : P → Pr P T Q A U)
    (residualClass : Matrix (Fin m) (Fin m) (ZMod prime) → Matrix (Fin n) (Fin n) (ZMod prime))
    (rs : List (Pair T)) (hk : rs.length = m*m) (out count saved : Fin T)
    (hr : (count :: saved :: (slots rs ++ [out])).Nodup) :
    ∃ prog : Pr P T Q A U, ∀ (v : RecursiveInterchangeLayout.Descriptor) (w B : ℕ),
      0 < w → v.beforeH = B*prime^(m*(w*m)) →
      Writes body (fun R => ready (prime^(w-1)) R rs ∧ R saved = [] ∧
        (R count).length = v.beforeRows*v.rows*B) out prog
        (signStream residualClass w (LabelMask.records v))
        ((v.beforeRows*v.rows*B)*(time (prime^(w-1)) (m*m) 1+5)+4) := by
  simpa [signStream,List.map_map,Function.comp_def] using class_writes (body := body) m
    (fun g => negativeAnchor (classPivots (residualClass g)) (residualClass g)) rs hk out count saved hr

/-- The symbol at a live label is the required sign for its full-width residual. -/
theorem signStream_at (residualClass : Matrix (Fin m) (Fin m) (ZMod prime) →
    Matrix (Fin n) (Fin n) (ZMod prime)) {w : ℕ} (hw : 0 < w) (g : LabelPadding.Label m w)
    (G : Matrix (Fin n) (Fin n) (ZMod (prime^w))) (p N : ℕ)
    (hg : G.det = 1 ∨ G.det = -1)
    (lift : (LabelRing.res prime w hw).mapMatrix G = residualClass ((LabelRing.res prime w hw).mapMatrix g))
    (index : p*(prime^w)^(m*m)+(LabelAddress.address g).val < N) :
    let M := residualClass ((LabelRing.res prime w hw).mapMatrix g)
    let pivots := classPivots M
    let j := p*(prime^w)^(m*m)+(LabelAddress.address g).val
    ∃ negative, (signStream (A := A) residualClass w N)[j]? = some (bitSymbol negative) ∧
      Itinerary.Valid pivots G n ∧ (Itinerary.run pivots G n).det = if negative then -1 else 1 := by
  dsimp only
  let φ := LabelRing.res prime w hw
  let M := residualClass (φ.mapMatrix g)
  have det : φ G.det = M.det := by rw [RingHom.map_det]; exact congrArg Matrix.det lift
  have unit : IsUnit M.det := by rw [← det]; rcases hg with h | h <;> simp [h]
  have valid := classPivots_valid M unit
  have reduced : Itinerary.Valid (classPivots M) (φ.mapMatrix G) n := lift.symm ▸ valid
  have full := (Itinerary.valid_map_iff φ (fun a ha => (LabelRing.isUnit_iff_res prime w hw a).mpr ha.ne_zero)
    _ G n).mpr reduced
  have addr := LabelStock.residue_at hw p 1 0 (by decide) g
  simp only [Nat.mul_one,Nat.add_zero] at addr
  refine ⟨negativeAnchor (classPivots M) M,?_,?_,?_⟩
  · simp [signStream,index,addr,M,φ]
  · exact full
  · have h := anchor_of_itinerary prime_odd hw _ G full hg
    simpa only [lift] using h

end
end IntegerMultBounds.MathlibTM2.Cover.Fallback
