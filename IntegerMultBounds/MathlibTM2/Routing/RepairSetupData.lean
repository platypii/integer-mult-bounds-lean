module

public import IntegerMultBounds.MathlibTM2.Routing.RepairSetupBank
public import IntegerMultBounds.MathlibTM2.Routing.RepairCore

/-! Raw configuration and fixed installation jobs for the full exact primitive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable {A Q K : ℕ} {P U : Type}

def repairSetupJob (wb wm wp wk keyedSize count payload keyWidth : ℕ) : RepairSetupKey → MetadataJob repairT
  | .inl key => setupJob repairHost repairRoutingConfig wb wm keyedSize count key
  | .inr .row => .zero (repairSetupSource (.inr .row)) (repairExtraTarget .row)
  | .inr .payload => .unary (repairSetupSource (.inr .payload)) (repairExtraTarget .payload) wp payload
  | .inr .keyLength => .unary (repairSetupSource (.inr .keyLength)) (repairExtraTarget .keyLength) wk keyWidth
  | .inr key => .copy (repairSetupSource (.inr key)) (repairExtraTarget key) false

def repairSetupJobs (wb wm wp wk keyedSize count payload keyWidth : ℕ) : List (MetadataJob repairT) :=
  repairSetupKeys.map (repairSetupJob wb wm wp wk keyedSize count payload keyWidth)

theorem repairSetupJob_src (wb wm wp wk keyedSize count payload keyWidth : ℕ) (key : RepairSetupKey) :
    (repairSetupJob wb wm wp wk keyedSize count payload keyWidth key).src = repairSetupSource key := by
  cases key with
  | inl key => exact setupJob_src _ _ _ _ _ _ key
  | inr key => cases key <;> rfl

theorem repairSetupJobsCost_le (R : Fin repairT → List (Fin (A + 4)))
    (wb wm wp wk keyedSize count payload keyWidth wordBound widthBound valueBound : ℕ)
    (hword : ∀ key, (R (repairSetupSource key)).length ≤ wordBound)
    (hwb : wb ≤ widthBound) (hwm : wm ≤ widthBound)
    (hwp : wp ≤ widthBound) (hwk : wk ≤ widthBound)
    (hsize : keyedSize ≤ valueBound) (hcount : count ≤ valueBound)
    (hpayload : payload ≤ valueBound) (hkey : keyWidth ≤ valueBound) :
    metadataInstallCost R (repairSetupJobs wb wm wp wk keyedSize count payload keyWidth) ≤
      34 * (6 * wordBound + 7 + widthBound * (4 * valueBound + 11) + 2 * valueBound + 6) + 1 := by
  have hc (key : RepairSetupKey) :
      (repairSetupJob wb wm wp wk keyedSize count payload keyWidth key).cost R ≤
        6 * wordBound + 7 + widthBound * (4 * valueBound + 11) + 2 * valueBound + 6 := by
    have hw : (R (repairSetupJob wb wm wp wk keyedSize count payload keyWidth key).src).length ≤
        wordBound := by
      rw [repairSetupJob_src]
      exact hword key
    refine MetadataJob.cost_le R _ wordBound widthBound valueBound hw ?_
    cases key with
    | inl key =>
      cases key <;> simp only [repairSetupJob, setupJob]
      all_goals trivial
    | inr key =>
      cases key <;> simp only [repairSetupJob]
      all_goals trivial
  have hlen : repairSetupKeys.length = 34 := by decide +kernel
  have hb := metadataInstallCost_le R
    (repairSetupJobs wb wm wp wk keyedSize count payload keyWidth) _ (by
      intro job hj
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
      exact hc key)
  simpa only [repairSetupJobs, List.length_map, hlen] using hb

theorem repairSetupJob_dst (wb wm wp wk keyedSize count payload keyWidth : ℕ) (key : RepairSetupKey) :
    (repairSetupJob wb wm wp wk keyedSize count payload keyWidth key).dst = repairSetupTarget key := by
  cases key with
  | inl key => exact setupJob_dst _ _ _ _ _ _ key
  | inr key => cases key <;> rfl

/-- The actual installer has no numerical or source-descriptor unrolling. -/
def repairSetup : Pr P repairT Q A U :=
  metadataInstall repairHost.out repairHost.tmp repairHost.ctmp (repairSetupJobs 0 0 0 0 0 0 0 0)

theorem repairSetup_eq (wb wm wp wk keyedSize count payload keyWidth : ℕ) :
    (repairSetup : Pr P repairT Q A U) = metadataInstall repairHost.out repairHost.tmp repairHost.ctmp
      (repairSetupJobs wb wm wp wk keyedSize count payload keyWidth) := by
  have he : ∀ keys : List RepairSetupKey,
      (metadataInstall repairHost.out repairHost.tmp repairHost.ctmp
        (keys.map (repairSetupJob 0 0 0 0 0 0 0 0)) : Pr P repairT Q A U) =
      metadataInstall repairHost.out repairHost.tmp repairHost.ctmp
        (keys.map (repairSetupJob wb wm wp wk keyedSize count payload keyWidth)) := by
    intro keys
    induction keys with
    | nil => rfl
    | cons key keys ih =>
      simp only [List.map_cons, metadataInstall]
      rw [ih]
      congr 1
      cases key with
      | inl key => cases key <;> rfl
      | inr key => cases key <;> rfl
  exact he repairSetupKeys

variable (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

def repairExtraPayload (B : ℕ) : RepairExtra → List (Fin (A + 4))
  | .row => binSyms rb 0
  | .keyDescriptor => (patternTable (selectiveKeyPattern p X active s)).flatten.map bitSymbol
  | .keyMask => binSyms p.wy (maskVal p.wy id)
  | .badMask => binSyms (p.wy + 1) (mAV p)
  | .badPhase => binSyms (p.wy + 1) (mkV p)
  | .payload => List.replicate B tick
  | .keyLength => List.replicate (fieldsLen (selectiveKeyLen p X rb)) tick

def repairSetupPayload (R B : ℕ) (headers : Fin 2 → Fin 5 → List Bool) : RepairSetupKey → List (Fin (A + 4))
  | .inl key => setupPayload p X hG hK active s
      (fieldsLen (selectiveKeyLen p X rb) + B) (R * 2 ^ fieldsLen (selectiveLen p X)) headers key
  | .inr key => repairExtraPayload p X rb active s B key

structure RepairSetupData (wb wm wp wk R B : ℕ) (headers : Fin 2 → Fin 5 → List Bool)
    (bank : Fin repairT → List (Fin (A + 4))) : Prop where
  routing : SetupData p X hG hK active s repairRoutingConfig wb wm
    (fieldsLen (selectiveKeyLen p X rb) + B) (R * 2 ^ fieldsLen (selectiveLen p X)) headers bank
  row : (bank (repairSetupSource (.inr .row))).length = rb
  descriptor : bank (repairSetupSource (.inr .keyDescriptor)) =
    (patternTable (selectiveKeyPattern p X active s)).flatten.map bitSymbol
  keyMask : bank (repairSetupSource (.inr .keyMask)) = binSyms p.wy (maskVal p.wy id)
  badMask : bank (repairSetupSource (.inr .badMask)) = binSyms (p.wy + 1) (mAV p)
  badPhase : bank (repairSetupSource (.inr .badPhase)) = binSyms (p.wy + 1) (mkV p)
  payload : bank (repairSetupSource (.inr .payload)) = binSyms wp B
  payload_lt : B < 2 ^ wp
  keyLength : bank (repairSetupSource (.inr .keyLength)) = binSyms wk (fieldsLen (selectiveKeyLen p X rb))
  keyLength_lt : fieldsLen (selectiveKeyLen p X rb) < 2 ^ wk

theorem RepairSetupData.contents {wb wm wp wk R B : ℕ} {headers : Fin 2 → Fin 5 → List Bool}
    {bank : Fin repairT → List (Fin (A + 4))}
    (data : RepairSetupData p X rb hG hK active s wb wm wp wk R B headers bank) (key : RepairSetupKey) :
    (repairSetupJob wb wm wp wk (fieldsLen (selectiveKeyLen p X rb) + B)
      (R * 2 ^ fieldsLen (selectiveLen p X)) B (fieldsLen (selectiveKeyLen p X rb)) key).contents bank =
      repairSetupPayload p X rb hG hK active s R B headers key := by
  cases key with
  | inl key => exact SetupData.contents p X hG hK active s repairHost data.routing key
  | inr key =>
    cases key with
    | row => simpa [repairSetupJob, MetadataJob.contents, repairSetupPayload, repairExtraPayload] using
        congrArg (fun w => (binSyms w 0 : List (Fin (A + 4)))) data.row
    | keyDescriptor => simpa [repairSetupJob, MetadataJob.contents, repairSetupPayload, repairExtraPayload] using data.descriptor
    | keyMask => simpa [repairSetupJob, MetadataJob.contents, repairSetupPayload, repairExtraPayload] using data.keyMask
    | badMask => simpa [repairSetupJob, MetadataJob.contents, repairSetupPayload, repairExtraPayload] using data.badMask
    | badPhase => simpa [repairSetupJob, MetadataJob.contents, repairSetupPayload, repairExtraPayload] using data.badPhase
    | payload => rfl
    | keyLength => rfl

theorem RepairSetupData.jobData {wb wm wp wk R B : ℕ} {headers : Fin 2 → Fin 5 → List Bool}
    {bank : Fin repairT → List (Fin (A + 4))}
    (data : RepairSetupData p X rb hG hK active s wb wm wp wk R B headers bank) (key : RepairSetupKey) :
    (repairSetupJob wb wm wp wk (fieldsLen (selectiveKeyLen p X rb) + B)
      (R * 2 ^ fieldsLen (selectiveLen p X)) B (fieldsLen (selectiveKeyLen p X rb)) key).Data bank := by
  cases key with
  | inl key => exact SetupData.jobData p X hG hK active s repairHost data.routing key
  | inr key =>
    cases key with
    | payload => exact ⟨data.payload_lt, data.payload⟩
    | keyLength => exact ⟨data.keyLength_lt, data.keyLength⟩
    | row | keyDescriptor | keyMask | badMask | badPhase => trivial

end
end IntegerMultBounds.MathlibTM2.Routing
