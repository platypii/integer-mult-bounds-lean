import IntegerMultBounds.Machine.ActivePrefixCompactConjugationRun
import IntegerMultBounds.Machine.ActivePrefixCompactSwapGeometry
import IntegerMultBounds.Machine.ActivePrefixCompactParityLoadLayout
import IntegerMultBounds.Machine.ActivePrefixCompactParityLoadLayoutAfter
import IntegerMultBounds.Machine.ActivePrefixCompactNegativeLoadLayout
import IntegerMultBounds.Machine.ActivePrefixCompactNegativeLoadLayoutAfter
import IntegerMultBounds.Machine.ActivePrefixLayoutAbsorption

/-! Both source orders in the unchanged layout for both physical load branches.
The original-record payload hypothesis pays prefix construction, with no
additional assumption that the wide target fits the compact reservation. -/
namespace IntegerMultBounds.Machine.ActivePrefixCompactConjugationLayout
noncomputable section
open ActivePrefixCompactConjugationData
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes
open CompactActiveTargetGeometry

inductive Side | before | after deriving DecidableEq

def sourceRoom (side : Side) (s : Shape) (p : Parameters s) :=
  match side with | .before => p.before | .after => p.after

def shape (side : Side) (s : Shape) (p : Parameters s) (offset : ℕ)
    (hfit : offset+p.f*p.q≤sourceRoom side s p) : ActivePrefixParityOnlyBank.Shape :=
  { W := ActivePrefixLayoutGeometry.backWidth s (p.n*p.q) p.before p.after
    startT := p.after
    startX := match side with | .before => p.n*p.q+p.after+offset | .after => offset
    q := p.q
    b := p.b
    n := p.n
    rho := p.rho
    f := p.f
    tempFits := by unfold ActivePrefixLayoutGeometry.backWidth; omega
    sourceFits := by
      cases side <;> dsimp only [sourceRoom] at hfit ⊢
      all_goals unfold ActivePrefixLayoutGeometry.backWidth ActivePrefixLayoutGeometry.targetWidth; omega
    hb := p.hb
    hbq := p.hbq
    hnf := p.hnf
    hr := p.hr }

def suffix (s : Shape) (p : Parameters s) := compactSuffix s (p.n*p.b)

theorem volume_eq (side : Side) (s : Shape) (p : Parameters s) (offset : ℕ)
    (hfit : offset+p.f*p.q≤sourceRoom side s p) (rows : ℕ) :
    ActivePrefixCompactParityLoadData.volume (shape side s p offset hfit) rows (suffix s p)=rows*s.recordWidth := by
  cases side with
  | before => exact ActivePrefixCompactParityLoadLayout.volume_eq s p offset hfit rows
  | after => exact ActivePrefixCompactParityLoadLayoutAfter.volume_eq s p offset hfit rows

theorem alignment (side : Side) (s : Shape) (p : Parameters s) (offset : ℕ)
    (hfit : offset+p.f*p.q≤sourceRoom side s p) (rows : ℕ) :
    ActivePrefixCompactSwapData.volume s rows (p.n*p.b)=
      ActivePrefixCompactParityLoadData.volume (shape side s p offset hfit) rows (suffix s p) :=
  (ActivePrefixCompactSwapData.volume_eq s rows (p.n*p.b) p.compactFits).trans
    (volume_eq side s p offset hfit rows).symm

def offsetValue (kind : Kind) (side : Side) (s : Shape) (p : Parameters s) (offset : ℕ)
    {rows : ℕ} (x : Address s p rows) : ℕ :=
  match kind,side with
  | .parity,.before => ActivePrefixCompactParityLoadLayout.parity s p offset x
  | .parity,.after => ActivePrefixCompactParityLoadLayoutAfter.parity s p offset x
  | .negative,.before => ActivePrefixCompactNegativeLoadLayout.negativeOffset s p offset x
  | .negative,.after => ActivePrefixCompactNegativeLoadLayoutAfter.negativeOffset s p offset x

def destination (kind : Kind) (side : Side) (s : Shape) (p : Parameters s) (offset : ℕ)
    {rows : ℕ} (x : Address s p rows) : Address s p rows :=
  { x with t := ⟨(x.t.val+offsetValue kind side s p offset x)%2^(p.n*p.b),Nat.mod_lt _ (by positivity)⟩ }

theorem absorbed (side : Side) (s : Shape) (p : Parameters s) (offset : ℕ)
    (hfit : offset+p.f*p.q≤sourceRoom side s p) (hrecord : s.bits+1≤s.payload) :
    (shape side s p offset hfit).W+1≤
      2^((shape side s p offset hfit).n*(shape side s p offset hfit).b)*suffix s p := by
  cases side with
  | before => exact ActivePrefixLayoutAbsorption.compact_before s p offset hfit hrecord
  | after => exact ActivePrefixLayoutAbsorption.compact_after s p offset hfit hrecord

/-- The full physical conjugation, from canonical original swap descriptors
and prepared load coordinates. All setup, copying, joins and cleanup are paid. -/
theorem runs (kind : Kind) (side : Side) (s : Shape) (p : Parameters s) (offset : ℕ)
    (hfit : offset+p.f*p.q≤sourceRoom side s p) (rows : ℕ) (hrows : 0<rows)
    (hK : 0<s.chunk) (hd : 0<s.axes) (hg : 0<s.guard) (hrecord : s.bits+1≤s.payload)
    (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (gv : ∀ i, Counter.value (gs i)=CompactGadgetReservationHeadersCarvedSchedule.originalValues s p.n rows i)
    (gc : ∀ i, GrowingCounterData.Canonical (gs i))
    (gb : Counter.value bw=p.b) (cb : GrowingCounterData.Canonical bw)
    (hv : ∀ i, Counter.value (hs i)=ActivePrefixParityOnlyBank.values (shape side s p offset hfit) i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs)
    (hb : Counter.value bs=suffix s p) (cs : GrowingCounterData.Canonical bs)
    (x : ActivePrefixCompactSwapData.Array s rows (p.n*p.b)) :
    HoareTime (ActivePrefixCompactConjugationRun.program kind)
      (fun v => v=ActivePrefixCompactConjugationMiddle.bank kind (base gs bw hs rs bs x))
      (fun v => v=ActivePrefixCompactConjugationMiddle.bank kind (base gs bw hs rs bs
        (ActivePrefixCompactConjugationRun.result kind s (shape side s p offset hfit) rows (p.n*p.b)
          (suffix s p) (alignment side s p offset hfit rows) x)))
      (ActivePrefixCompactConjugationRun.cost kind s rows (p.n*p.b)) := by
  have hp : 0<s.payload := by omega
  exact ActivePrefixCompactConjugationRun.runs kind s p.n rows p.b gs bw hs rs bs gv gc gb cb
    p.hb hrows hK hd hg hp p.compactFits (shape side s p offset hfit) (suffix s p)
    (by unfold suffix compactSuffix; positivity) (absorbed side s p offset hfit hrecord)
    (alignment side s p offset hfit rows) hv hc hr cr hb cs x

end
end IntegerMultBounds.Machine.ActivePrefixCompactConjugationLayout
