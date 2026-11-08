module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRoundAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBatchInputData

/-! Expose publication fits per output field, as required by packet batch execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem packedFinalRound_fields_fits {A s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (p q j w k E c n : ℕ) (hp : p ≤ q) (hw : 1 ≤ w) (hk : p+E+5 ≤ k)
    (active : Finset (ZMod s)) (hfit : c+n ≤ s)
    (hcover : ∀ i : ZMod s, c ≤ i.val → i.val < c+n → i ∈ active)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt)) (error : ℝ) (he : error ≤ 1)
    (hmag : ∀ z ∈ Zs, ∀ i ∈ active, ‖z i‖ ≤ 4*(2 : ℝ)^E) (oldTail : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
      (packedIntervalRead q w c (cstream A w (packedInterval c n D)++oldTail)) z error) Zs Ds) :
    ∀ G ∈ Ds.map (fun D i => finalRoundWord w q p j (D i)), ∀ x ∈ packedInterval c n G, Fits k x := by
  have hfits := packedFinalRoundBatch_fits hA p q j w k E c n hp hw hk active hfit hcover Zs Ds error he hmag oldTail hgood
  intro G hG x hx
  obtain ⟨D,hD,rfl⟩ := List.mem_map.mp hG
  rw [←packedInterval_map] at hx
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hx
  apply hfits
  exact List.mem_map.mpr ⟨z,List.mem_flatten.mpr ⟨packedInterval c n D,List.mem_map.mpr ⟨D,hD,rfl⟩,hz⟩,rfl⟩

theorem packedIntervalRead_value_of_fits {A s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (p w c n : ℕ) (hw : 1 ≤ w) (D : ZMod s → GaussianInt)
    (hfit : c+n ≤ s) (hfits : ∀ x ∈ packedInterval c n D, Fits w x)
    (tail : List (Fin (A+4))) (i : ZMod s) (hi : c ≤ i.val ∧ i.val < c+n) :
    packedIntervalRead p w c (cstream A w (packedInterval c n D)++tail) i = value p (D i) := by
  have hj : i.val-c < n := by omega
  have hlen : i.val-c < (packedInterval c n D).length := by rw [packedInterval_length D hfit]; exact hj
  have hm := List.getElem_mem (l := packedInterval c n D) hlen
  rw [packedInterval_get D hfit hj] at hm
  have hindex : ((c+(i.val-c) : ℕ) : ZMod s) = i := by
    rw [Nat.add_sub_of_le hi.1,ZMod.natCast_zmod_val]
  rw [hindex] at hm
  rw [packedIntervalRead_eq p w c n D tail [] hfit i hi.1 hi.2,
    pairedCellRead_encodedField hA hw _ [] i (hfits _ hm)]

theorem packedIntervalBatch_value_error {A s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (p w c n : ℕ) (hw : 1 ≤ w) (active : Finset (ZMod s)) (hfit : c+n ≤ s)
    (hactive : ∀ i ∈ active, c ≤ i.val ∧ i.val < c+n)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt)) (error : ℝ)
    (hfits : ∀ D ∈ Ds, ∀ x ∈ packedInterval c n D, Fits w x) (tail : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
      (packedIntervalRead p w c (cstream A w (packedInterval c n D)++tail)) z error) Zs Ds) :
    List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active (fun i => value p (D i)) z error) Zs Ds := by
  induction hgood with
  | nil => exact .nil
  | @cons z D zs ds hz hs ih =>
    refine .cons ?_ (ih (fun D hmem => hfits D (List.mem_cons_of_mem _ hmem)))
    intro i hi
    have hh := hz i hi
    rw [packedIntervalRead_value_of_fits hA p w c n hw D hfit (hfits D (by simp)) tail i (hactive i hi)] at hh
    exact hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
