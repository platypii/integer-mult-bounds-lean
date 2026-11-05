module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSolverAllocation

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
variable {T A s : ℕ} [NeZero s]
noncomputable section

/-- Ordinary retained inputs and fresh storage shared by proper publication
and boundary completion. The output bank is deliberately outside this frame. -/
structure BoundaryCallerReady (src : Fin 11 → Fin T) (widthSource : Fin (T+solverRegisterCount))
    (p u l target t W D radius width : ℕ) (Fs : List (ZMod s → GaussianInt))
    (S : Stacks (MachineTapes (T+solverRegisterCount)) A) : Prop where
  raw : ∀ i, (S.R (unarySource _ (solverSource (src i)))).length =
    globalValues p u l target s t (inverseCallerWordWidth p u l target s t) W Fs.length radius width i
  zero : S.R (fullHeader _ .zero) = []
  blank : ∀ r : SolverRole, r ≠ .scratch 4 → S.R (solverRegister T r) = []
  left : ∀ r : SolverRole, S.L (solverRegister T r) = []
  input : S.R (solverRegister T (.scratch 4)) =
    cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten
  headers : ∀ i : Fin 6, S.R (fullHeader _ (.publication (Fin.castAdd 1 i))) = []
  privateBank : ∀ i : Fin tapeCount, S.R (Fin.natAdd (((T+solverRegisterCount)+headerCount)+175) i) = []
  arithmeticWidth : (S.R (unarySource _ widthSource)).length = D
  scalars : ∀ i, S.R (globals _ i) = binSyms D
    (globalValues p u l target s t (inverseCallerWordWidth p u l target s t) W Fs.length radius width i)

theorem BoundaryCallerReady.update_output {src : Fin 11 → Fin T} {widthSource : Fin (T+solverRegisterCount)}
    {p u l target t W D radius width : ℕ} {Fs : List (ZMod s → GaussianInt)}
    {S : Stacks (MachineTapes (T+solverRegisterCount)) A}
    (h : BoundaryCallerReady src widthSource p u l target t W D radius width Fs S)
    (xs : List (Fin (A+4))) :
    BoundaryCallerReady src widthSource p u l target t W D radius width Fs
      {S with R := Function.update S.R (fullHeader _ .output) xs} := by
  let M : Stacks (MachineTapes (T+solverRegisterCount)) A :=
    {S with R := Function.update S.R (fullHeader _ .output) xs}
  have hread (i : Fin (MachineTapes (T+solverRegisterCount))) (hi : i ≠ fullHeader _ .output) :
      M.R i = S.R i := by
    dsimp only [M]
    exact Function.update_of_ne hi _ _
  have hsource (i : Fin (T+solverRegisterCount)) : M.R (unarySource _ i) = S.R (unarySource _ i) :=
    hread _ (fullHeader_ne_bank id .output i).symm
  have hheader (r : Role) (hr : r ≠ .output) : M.R (fullHeader _ r) = S.R (fullHeader _ r) :=
    hread _ ((fullHeader_injective _).ne hr)
  refine ⟨?_,?_,?_,h.left,?_,?_,?_,?_,?_⟩
  · intro i; exact (congrArg List.length (hsource (solverSource (src i)))).trans (h.raw i)
  · exact (hheader .zero (by simp)).trans h.zero
  · intro r hr; exact (hread _ (solverRegister_ne_header T r .output)).trans (h.blank r hr)
  · exact (hread _ (solverRegister_ne_header T (.scratch 4) .output)).trans h.input
  · intro i; exact (hheader _ (by intro he; cases he)).trans (h.headers i)
  · intro i
    exact (hread _ (prefix_ne_routing (Fin.castAdd 175 (header (T+solverRegisterCount) .output)) i).symm).trans (h.privateBank i)
  · exact (congrArg List.length (hsource widthSource)).trans h.arithmeticWidth
  · intro i; exact (hheader _ (by intro he; cases he)).trans (h.scalars i)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
