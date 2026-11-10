module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedOutput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundedDiagonalAccuracy

/-! The signed values already encoded on an interval packet are bounded inputs
for the existing diagonal worker. No fit premise on hidden solver witnesses is
needed, and replacing witnesses performs no tape operation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {A s p W start rows : ℕ} [NeZero s]

omit [NeZero s] in
private theorem signed_interval_stream (D : ZMod s → GaussianInt) :
    cstream A W (packedInterval start rows (fun i => symZ W (D i))) =
      cstream A W (packedInterval start rows D) := by
  have hmap : packedInterval start rows (fun i => symZ W (D i)) =
      (packedInterval start rows D).map (symZ W) := by
    simp only [packedInterval,chirpLine,List.map_map,Function.comp_def,List.map_drop,List.map_take]
  rw [hmap,cstream_symZ]

theorem PackedIntervalOutput.signed_fields
    {targets : List (ZMod s → ℂ)} {error : ℝ} {word : List (Fin (A+4))}
    (h : PackedIntervalOutput p W start rows targets error word)
    (hA : 4 ≤ A) (hW : p+3 ≤ W) (hfit : start+rows ≤ s) (he : error ≤ 1/2)
    (hmag : ∀ z ∈ targets, ∀ i ∈ haloVertices s start (start+rows), ‖z i‖ ≤ (3/2 : ℝ)) :
    ∃ Ds : List (ZMod s → GaussianInt), Ds.length = targets.length ∧
      word = (Ds.map (fun D => cstream A W (packedInterval start rows D))).flatten ∧
      (∀ D ∈ Ds, ∀ x ∈ packedInterval start rows D, Fits W x) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s start (start+rows))
        (fun i => value p (D i)) z error ∧
        ∀ i ∈ haloVertices s start (start+rows), ‖value p (D i)‖ ≤ 2) targets Ds := by
  obtain ⟨Es,hlen,hword,hgood⟩ := h
  let Ds := Es.map (fun D i => symZ W (D i))
  have hrel : List.Forall₂ (fun z D =>
      (∀ x ∈ packedInterval start rows D, Fits W x) ∧
      PhaseCellInterface.ErrorOn (haloVertices s start (start+rows)) (fun i => value p (D i)) z error ∧
      ∀ i ∈ haloVertices s start (start+rows), ‖value p (D i)‖ ≤ 2) targets Ds := by
    apply List.forall₂_map_right_iff.mpr
    have hm := (List.forall₂_and_left targets Es).mpr ⟨hmag,hgood⟩
    apply List.Forall₂.imp _ hm
    intro z D hpair
    have hvalue : PhaseCellInterface.ErrorOn (haloVertices s start (start+rows))
        (fun i => value p (symZ W (D i))) z error := by
      intro i hi
      obtain ⟨ha,hb⟩ := (mem_haloVertices _ _ i).mp hi
      have hread := packedIntervalRead_decode (A := A) p W start rows D [] hfit i ha hb
      rw [decodeWord_csyms_symZ hA (by omega)] at hread
      have hh := hpair.2 i hi
      simp only [List.append_nil] at hread
      rw [hread] at hh
      exact hh
    have hnorm : ∀ i ∈ haloVertices s start (start+rows), ‖value p (symZ W (D i))‖ ≤ 2 := by
      intro i hi
      have hn := norm_le_norm_sub_add (value p (symZ W (D i))) (z i)
      have hh := hvalue i hi
      have hz := hpair.1 i hi
      linarith
    refine ⟨?_,hvalue,hnorm⟩
    apply packedInterval_fits_of_active _ (haloVertices s start (start+rows)) hfit
      (by intro i ha hb; exact (mem_haloVertices _ _ i).mpr ⟨ha,hb⟩)
    intro i hi
    apply fits_of_value_power (e := 1) (by omega)
    simpa only [pow_one] using hnorm i hi
  have hsplit := (List.forall₂_and_left Ds targets).mp hrel.flip
  refine ⟨Ds,by simpa only [Ds,List.length_map] using hlen,?_,hsplit.1,hsplit.2.flip⟩
  rw [hword]
  congr 1
  simp only [Ds,List.map_map,Function.comp_def,signed_interval_stream]

/-- The existing diagonal batch prepends each result, hence reverses replica
order. Its accuracy is expressed in exactly that physical order. -/
theorem PackedIntervalOutput.diagonal_fields {t α : ℕ} [NeZero t]
    {targets : List (ZMod s → ℂ)} {error : ℝ} {word : List (Fin (A+4))}
    (h : PackedIntervalOutput p W start rows targets error word)
    (hA : 4 ≤ A) (hp : 13 ≤ p) (hW : p+3 ≤ W)
    (hα : 1 ≤ α) (hαp : α^2 ≤ p) (hfit : start+rows ≤ s) (he : error ≤ 1/2)
    (hmag : ∀ z ∈ targets, ∀ i ∈ haloVertices s start (start+rows), ‖z i‖ ≤ (3/2 : ℝ)) :
    ∃ Ds : List (ZMod s → GaussianInt), Ds.length = targets.length ∧
      word = (Ds.map (fun D => cstream A W (packedInterval start rows D))).flatten ∧
      (∀ D ∈ Ds, ∀ x ∈ packedInterval start rows D, Fits W x) ∧
      PackedIntervalOutput p W start rows
        (targets.reverse.map (fun z i => (dPrime s t (α : ℝ) i : ℂ)*z i))
        (6/(2 : ℝ)^p+error)
        ((Ds.reverse.map (fun D => cstream A W
          (packedInterval start rows (diagonalProduct s t α p D)))).flatten) := by
  obtain ⟨Ds,hlen,hword,hfits,hgood⟩ := h.signed_fields hA hW hfit he hmag
  have hd := List.Forall₂.imp (fun z D hpair =>
    diagonalPacket_accuracy (A := A) (t := t) (α := α) hA hW hp hα hαp hfit
      (haloVertices s start (start+rows))
      (fun i hi => (mem_haloVertices _ _ i).mp hi) D z error [] hpair.2 hpair.1) hgood
  refine ⟨Ds,hlen,hword,hfits,Ds.reverse.map (diagonalProduct s t α p),?_,?_,?_⟩
  · simp only [List.length_map,List.length_reverse,hlen]
  · simp only [List.map_map,Function.comp_def]
  · apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    simpa only [List.append_nil] using List.forall₂_reverse_iff.mpr hd

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
