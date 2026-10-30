module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBatchProgram

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {A : ℕ}

/-- Prepending each result reverses block order, while preserving word order
inside every block. The numerical witnesses remain in input order. -/
theorem PackedHaloInputTrace.outputs {X Y : Type}
    {Result : X → Stacks 248 A → Stacks 248 A → Prop}
    (encode : Y → List (Fin (A+4))) (Good : X → Y → Prop)
    (hresult : ∀ x S F, Result x S F → ∃ y,
      F.R 132 = encode y++S.R 132 ∧ Good x y)
    {xs : List X} {S F : Stacks 248 A} (h : PackedHaloInputTrace Result xs S F) :
    ∃ ys : List Y, F.R 132 = (ys.reverse.map encode).flatten++S.R 132 ∧
      List.Forall₂ Good xs ys := by
  induction h with
  | nil S => exact ⟨[],by simp,.nil⟩
  | cons hx _ ih =>
    obtain ⟨y,hout,hgood⟩ := hresult _ _ _ hx
    obtain ⟨ys,houts,hgoods⟩ := ih
    refine ⟨y::ys,?_,.cons hgood hgoods⟩
    rw [houts,hout]
    simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]

/-- A halo word cannot read its borrowed suffix. -/
theorem packedIntervalRead_suffix {s : ℕ} [NeZero s] (q w a L : ℕ)
    (D : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (hfit : a+L ≤ s) (i : ZMod s) (ha : a ≤ i.val) (hi : i.val < a+L) :
    packedIntervalRead q w a (cstream A w (packedInterval a L D)++tail) i =
      packedIntervalRead q w a (cstream A w (packedInterval a L D)) i := by
  have h₁ := packedIntervalRead_eq (A := A) q w a L D tail [] hfit i ha hi
  have h₂ := packedIntervalRead_eq (A := A) q w a L D [] [] hfit i ha hi
  simpa only [List.append_nil] using h₁.trans h₂.symm

/-- Extract usable ordered numerical outputs from the executed trace. Accuracy
is stated on each output's own encoded block, independently of archived suffixes. -/
theorem PackedHaloInputTrace.packed_outputs {s : ℕ} [NeZero s]
    (q w a b : ℕ) (hab : a ≤ b) (hb : b ≤ s) (e : ℝ)
    {inputs : List ((ZMod s → GaussianInt) × (ZMod s → ℝ))}
    {S F : Stacks 248 A}
    (h : PackedHaloInputTrace (fun x S F => ∃ D : ZMod s → GaussianInt,
      F.R 132 = cstream A w (packedInterval a (b-a) D)++S.R 132 ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => (packedIntervalRead q w a (F.R 132) i).re) x.2 e) inputs S F) :
    ∃ Ds : List (ZMod s → GaussianInt),
      F.R 132 = (Ds.reverse.map (fun D => cstream A w (packedInterval a (b-a) D))).flatten++S.R 132 ∧
      List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => (packedIntervalRead q w a (cstream A w (packedInterval a (b-a) D)) i).re) x.2 e)
        inputs Ds := by
  apply h.outputs (fun D => cstream A w (packedInterval a (b-a) D))
    (fun x D => PhaseCellInterface.ErrorOn (haloVertices s a b)
      (fun i => (packedIntervalRead q w a (cstream A w (packedInterval a (b-a) D)) i).re) x.2 e)
  intro x T G hresult
  obtain ⟨D,hout,herror⟩ := hresult
  refine ⟨D,hout,?_⟩
  intro i hi
  have hval := (mem_haloVertices a b i).mp hi
  have he := herror i hi
  dsimp only at he ⊢
  rw [hout,packedIntervalRead_suffix q w a (b-a) D (T.R 132) (by omega) i hval.1 (by omega)] at he
  exact he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
