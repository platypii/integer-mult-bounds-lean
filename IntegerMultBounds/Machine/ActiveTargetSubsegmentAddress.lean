import IntegerMultBounds.Compact.ActiveTargetSubsegmentWords
import IntegerMultBounds.Machine.CompactActiveTargetLayout

/-! The guarded active kernel lifted onto the complete unchanged reservation
address: compact tails, active spectators, dirty back and payload retained. -/
namespace IntegerMultBounds.Machine.ActiveTargetSubsegmentAddress
noncomputable section
open CompactGadgetReservationShape
open CompactActiveTargetLayout

variable (s : Shape) (q b n before after rows : ℕ)
abbrev A := Address s (n*b) (n*q) before after rows

def earlyState (x : A s q b n before after rows) : BinaryPackedEarlyData.State q b n (A s q b n before after rows) :=
  (x.target,x.t,x)
def early (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (x : A s q b n before after rows) :=
  let y := BinaryPackedEarlyData.run q b n Z hb hbq (earlyState s q b n before after rows x)
  { x with target := y.1, t := y.2.1 }

theorem early_good (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n)
    (x : A s q b n before after rows) (ds : List Compact.DigitState)
    (hc : ds.map Compact.DigitState.z=Z.map Compact.PowerTwo.ctrl)
    (hv : (x.target.val : ℤ)=Compact.Radix.pack ((2 : ℤ)^q) (ds.map Compact.DigitState.v))
    (hw : (x.t.val : ℤ)=Compact.Radix.pack ((2 : ℤ)^b) (ds.map Compact.DigitState.w))
    (hg : ∀ d∈ds, d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) :
    ∃ v : Fin (2^(n*q)), (v.val : ℤ)=Compact.Radix.pack ((2 : ℤ)^q) (ds.map (fun d => Compact.toggle d.v d.z)) ∧
      early s q b n before after rows Z hb hbq x={x with target:=v} := by
  let y := BinaryPackedEarlyData.run q b n Z hb hbq (earlyState s q b n before after rows x)
  have ht := BinaryPackedEarlyData.good_temp q b n Z hb hbq hZ
    (earlyState s q b n before after rows x) ds hc hv hw hg
  have hv' := congrArg Prod.fst (BinaryPackedEarlyData.good_value q b n Z hb hbq hZ
    (earlyState s q b n before after rows x) ds hc hv hw hg)
  refine ⟨y.1,hv',?_⟩
  change {x with target:=y.1,t:=y.2.1}={x with target:=y.1}
  change y.2.1=x.t at ht
  rw [ht]

def lateState (x : A s q b n before after rows) : BinaryPackedLateData.State q b n (A s q b n before after rows) :=
  (x.target,x.t,x.u,x)
def late (X : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hX : X.length=n)
    (x : A s q b n before after rows) :=
  let y := BinaryPackedLateData.run q b n hb hbq X hX (lateState s q b n before after rows x)
  {x with target:=y.1,t:=y.2.1,u:=y.2.2.1}

theorem late_good (X : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hX : X.length=n)
    (x : A s q b n before after rows) (ds : List Compact.LateDigitState)
    (hc : ds.map Compact.LateDigitState.x=X.map Compact.PowerTwo.ctrl)
    (hv : (x.target.val : ℤ)=Compact.Radix.pack ((2 : ℤ)^q) (ds.map Compact.LateDigitState.v))
    (hw : (x.t.val : ℤ)=Compact.Radix.pack ((2 : ℤ)^b) (ds.map Compact.LateDigitState.w))
    (hu : (x.u.val : ℤ)=Compact.Radix.pack ((2 : ℤ)^b) (ds.map Compact.LateDigitState.u))
    (hg : ∀ d∈ds, d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) :
    ∃ v : Fin (2^(n*q)), (v.val : ℤ)=Compact.Radix.pack ((2 : ℤ)^q) (ds.map (fun d => Compact.toggle d.v d.x)) ∧
      late s q b n before after rows X hb hbq hX x={x with target:=v} := by
  let y := BinaryPackedLateData.run q b n hb hbq X hX (lateState s q b n before after rows x)
  have h := BinaryPackedLateData.good_value q b n hb hbq X hX
    (lateState s q b n before after rows x) ds hc hv hw hu hg
  have hv' := congrArg Prod.fst h
  have ht := congrArg (fun z => z.2.1) h
  dsimp only at ht
  have htt : y.2.1=x.t := by apply Fin.ext; exact_mod_cast ht
  have hu' := BinaryPackedLateData.restored_control q b n hb hbq X hX
    (lateState s q b n before after rows x)
  change y.2.2.1=x.u at hu'
  refine ⟨y.1,hv',?_⟩
  change {x with target:=y.1,t:=y.2.1,u:=y.2.2.1}={x with target:=y.1}
  rw [htt,hu']

end
end IntegerMultBounds.Machine.ActiveTargetSubsegmentAddress
