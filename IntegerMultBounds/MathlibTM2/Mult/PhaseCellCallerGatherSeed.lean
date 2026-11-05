module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerInputPreparation

/-! Construct the fixed caller's gather seed from produced geometry and ordinary
retained stream/count data. No arbitrary source maps or initialized halo words
are supplied to this constructor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN.PhaseCellMatrix
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T Q K D p u l target s t B W N radius width Vg Vr L a : ℕ}

/-- Mathematical eligibility for a nonempty class, independent of machine data. -/
structure GatherBounds (Q Vg Vr s width radius L W a : ℕ)
    (Fs : List (ZMod s → GaussianInt)) : Prop where
  states : FixedStreamedBank.stateCount ≤ Q
  widthPositive : 0 < width
  exposeWide : s+width+2*radius < 2^Vg
  wordFits : W < 2^Vg
  volumeFits : s*W < 2^Vg
  exposePositive : 0 < Vg
  nonempty : 0 < (coreGatherIndices s width radius L).length
  routeWide : s+width+2*radius < 2^Vr
  routePositive : 0 < Vr
  packetPositive : 0 < L*W
  bitsFit : a+Nat.clog 2 (coreGatherIndices s width radius L).length < Vr
  packetFits : (L*W)*2^(a+Nat.clog 2 (coreGatherIndices s width radius L).length) < 2^Vr
  replicas : Fs.length = 2^a

/-- Ordinary retained controls and stream; geometry and width rulers are omitted
because they are supplied by the actual caller preparation endpoint. -/
structure GatherRetainedInput (T K s W : ℕ) (b : ComputedClassBank → Fin T)
    (Fs : List (ZMod s → GaussianInt)) (borrowed : List (Fin (prime+K+4)))
    (S : Stacks (MachineTapes T) (prime+K)) : Prop where
  wordLength : (S.R (fullHeader T .word)).length = W
  volumeLength : (S.R (fullHeader T .volume)).length = s*W
  replicaLength : (S.R (fullHeader T .replicas)).length = Fs.length
  source : S.R (fullHeader T .input) = Fs.flatMap (fun C => cstream (prime+K) W (chirpLine s C))++borrowed
  exposureBlank : ∀ i : Fin 175, S.R (Fin.castAdd tapeCount (Fin.natAdd (T+headerCount) i)) = []
  outputBlank : S.R (fullExposedClassBank (bank b) (.control .source)) = []
  routingLeft : ∀ i : Fin tapeCount, S.L (Fin.natAdd ((T+headerCount)+175) i) = []
  sourceLeft : S.L (control (fullExposedClassBank (bank b)) .source) = []

theorem exposurePrivate_ne_header (T : ℕ) (i : Fin 175) (r : Role) :
    Fin.castAdd tapeCount (Fin.natAdd (T+headerCount) i) ≠ fullHeader T r := by
  intro h
  have hv := congrArg (fun k : Fin (MachineTapes T) => k.val) h
  change T+headerCount+i.val = (header T r).val at hv
  have := (header T r).isLt
  omega

namespace GatherRetainedInput

/-- Caller preparation writes only scalar/ruler/geometry roles, so retained
stream/count inputs survive that actual preparation trace. -/
theorem reframe {Fs : List (ZMod s → GaussianInt)} {borrowed : List (Fin (prime+K+4))}
    {b : ComputedClassBank → Fin T} {S F : Stacks (MachineTapes T) (prime+K)}
    (retained : GatherRetainedInput T K s W b Fs borrowed S)
    (hL : F.L = S.L)
    (hframe : ∀ k, (∀ i, k ≠ globals T i) → (∀ f, k ≠ rulers T f) →
      (∀ f i, k ≠ fullHeader T (.geometry f i)) → F.R k = S.R k) :
    GatherRetainedInput T K s W b Fs borrowed F := by
  have hret (r : Role) (hr : r = .word ∨ r = .volume ∨ r = .replicas ∨ r = .input) :
      F.R (fullHeader T r) = S.R (fullHeader T r) := by
    rcases hr with rfl | rfl | rfl | rfl
    all_goals apply hframe
    all_goals intro i
    all_goals first
      | exact (fullHeader_injective T).ne (by intro h; cases h)
      | intro j; exact (fullHeader_injective T).ne (by intro h; cases h)
  refine {
    wordLength := (congrArg List.length (hret .word (Or.inl rfl))).trans retained.wordLength
    volumeLength := (congrArg List.length (hret .volume (Or.inr (Or.inl rfl)))).trans retained.volumeLength
    replicaLength := (congrArg List.length (hret .replicas (Or.inr (Or.inr (Or.inl rfl))))).trans retained.replicaLength
    source := (hret .input (Or.inr (Or.inr (Or.inr rfl)))).trans retained.source
    exposureBlank := ?_
    outputBlank := ?_
    routingLeft := ?_
    sourceLeft := ?_}
  · intro i
    rw [hframe]
    · exact retained.exposureBlank i
    · intro j; exact exposurePrivate_ne_header T i (.scalar j)
    · intro f; exact exposurePrivate_ne_header T i (.ruler f)
    · intro f j; exact exposurePrivate_ne_header T i (.geometry f j)
  · rw [hframe]
    · exact retained.outputBlank
    · intro i; exact (fullHeader_ne_numerical b (.scalar i) (.control .source)).symm
    · intro f; exact (fullHeader_ne_numerical b (.ruler f) (.control .source)).symm
    · intro f i; exact (fullHeader_ne_numerical b (.geometry f i) (.control .source)).symm
  · rw [hL]; exact retained.routingLeft
  · rw [hL]; exact retained.sourceLeft

end GatherRetainedInput

/-- The fixed source maps, separation and six binary geometry fields are derived.
Class length fit follows from the computed core/halo bound. -/
def makeGatherSeed {Fs : List (ZMod s → GaussianInt)} {borrowed : List (Fin (prime+K+4))}
    {S : Stacks (MachineTapes T) (prime+K)}
    (input : SetupInput T (prime+K) D p u l target s t B W N radius width Vg Vr S)
    (hwords : ∀ f i, S.R (fullHeader T (.geometry f i)) = binSyms (formatWidths B Vg Vr f) (![s,width,radius] i))
    (b : ComputedClassBank → Fin T)
    (retained : GatherRetainedInput T K s W b Fs borrowed S)
    (bounds : GatherBounds Q Vg Vr s width radius L W a Fs)
    (hL : L ≤ width+2*radius) (hA : 4 ≤ prime+K) :
    RestoringGatherSeed (Q := Q) (bank b) Vg s width radius L W Fs borrowed S := by
  refine {
    exposeSrc := exposure T
    input := header T .input
    routeSrc := routing T
    hstates := bounds.states
    D := Vr
    a := a
    hExposeOff := fun i k => header_ne_bank b (exposureRole i) k
    hInputOff := fun k => header_ne_bank b .input k
    hRouteOff := fun i k => header_ne_bank b (routingRole i) k
    hwidth := bounds.widthPositive
    hwide := bounds.exposeWide
    hLfit := lt_of_le_of_lt hL (by have := bounds.exposeWide; omega)
    hwV := bounds.wordFits
    hvol := bounds.volumeFits
    hA := hA
    hVpos := bounds.exposePositive
    hgroup := bounds.nonempty
    hs := ?_
    hw := ?_
    hr := ?_
    hV := ?_
    hword := retained.wordLength
    hcount := retained.volumeLength
    hreplicas := retained.replicaLength
    hsource := retained.source
    hblank := retained.exposureBlank
    houtput := retained.outputBlank
    hDwide := bounds.routeWide
    hDLfit := lt_of_le_of_lt hL (by have := bounds.routeWide; omega)
    hDpos := bounds.routePositive
    hpacket := bounds.packetPositive
    hbits := bounds.bitsFit
    hfit := bounds.packetFits
    hpower := bounds.replicas
    hRs := ?_
    hRw := ?_
    hRr := ?_
    hRV := ?_
    hRword := retained.wordLength
    hRrep := retained.replicaLength.trans bounds.replicas
    hRblank := input.routingBlank
    hRleft := retained.routingLeft
    hsourceLeft := retained.sourceLeft}
  · exact hwords 1 0
  · exact hwords 1 1
  · exact hwords 1 2
  · exact input.rulerLengths 1
  · exact hwords 2 0
  · exact hwords 2 1
  · exact hwords 2 2
  · exact input.rulerLengths 2

/-- The class setup consumes this constructed seed directly. No extra source-map
matching premises remain, and the class length comes from its computed geometry. -/
def makeGatherInput {Fs : List (ZMod s → GaussianInt)} {borrowed : List (Fin (prime+K+4))}
    {S : Stacks (MachineTapes T) (prime+K)}
    (input : SetupInput T (prime+K) D p u l target s t B W N radius width Vg Vr S)
    (hwords : ∀ f i, S.R (fullHeader T (.geometry f i)) = binSyms (formatWidths B Vg Vr f) (![s,width,radius] i))
    (b : ComputedClassBank → Fin T)
    (retained : GatherRetainedInput T K s W b Fs borrowed S)
    (clipped : Bool)
    (bounds : GatherBounds Q Vg Vr s width radius (haloRows clipped s width radius) W a Fs)
    (hgeometry : width+2*radius < 2^D)
    (hfit : ∀ i, globalValues p u l target s t B W N radius width i < 2^D)
    (hbits : ∀ f, formatWidths B Vg Vr f ≤ D) (hA : 4 ≤ prime+K) :
    let hL : haloRows clipped s width radius ≤ width+2*radius :=
      Nat.add_le_add_right (coreRows_le clipped s width bounds.widthPositive) _
    let g := makeGatherSeed input hwords b retained bounds hL hA
    (makeSetup input clipped bounds.widthPositive hgeometry hfit hbits).GatherInput g
      (numericTable T) (masterSources T) (geometrySources T 3) := by
  exact setupGatherInput input clipped bounds.widthPositive hgeometry hfit hbits b
    (makeGatherSeed input hwords b retained bounds (Nat.add_le_add_right (coreRows_le clipped s width bounds.widthPositive) _) hA)
    rfl rfl rfl

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
