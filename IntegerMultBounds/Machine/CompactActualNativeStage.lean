import IntegerMultBounds.Machine.ActivePrefixStageNative
import IntegerMultBounds.Machine.CompactActualStageRuntimeBudget

/-! The multiplier's actual scalar choices discharge the native stage's
readiness and packed-cost premises. A concrete triple-aligned payload reserves
both signed coefficient fields and delimiters, satisfies the existing payload
allowance, and grows by only a fixed factor. One fixed native machine serves
all original node widths, slot orders and descendant row levels. -/
namespace IntegerMultBounds.Machine.CompactActualNativeStage
noncomputable section
open Sizes
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open CompactActualStageAllowance CompactActualStageGeometry CompactActualStageInputs
open CompactGlobalRowPadding CompactReservationCutoff
open ActivePrefixStageNative (bank cost)
open ActivePrefixStageFullSelected (Address)
open Networks.Shared50ModularControl (prime)

/-- Two signed coefficient fields plus their native separators per polynomial
coefficient; each native symbol occupies three Boolean payload cells. -/
def symbols (n : ℕ) := 2*(b n+1)*2^ℓ n
def payload (n : ℕ) := 3*symbols n

theorem payload_allowance (n : ℕ) : 6*b n*2^ℓ n≤payload n := by
  unfold payload symbols
  nlinarith [Nat.zero_le (2^ℓ n)]

theorem payload_constant (n : ℕ) (hb : 0<b n) : payload n≤12*b n*2^ℓ n := by
  unfold payload symbols
  nlinarith [Nat.zero_le (2^ℓ n)]

theorem triple_capacity (n c m D : ℕ) :
    (actualShape n c m D (payload n)).payload=symbols n*3+0 := by
  change 3*symbols n=symbols n*3+0
  omega

def BoundedSpec {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (C : ℝ) {s : Shape} (B : ℕ) (input : ActivePrefixStageFullData.Inputs s)
    (hcode : s.payload=B*3+0) : Prop :=
  ∃ hp : 1 < input.stage.f → ActivePrefixStageRuntimeData.Packed input 1,
    (cost (B:=B) 1 input hp : ℝ)≤C*(input.rows*s.recordWidth : ℕ)*
      ((max 1 ((input.stage.f-1)*s.guard) : ℕ) : ℝ)^Parameters.tau ∧
    ∀ (xs : Address input → Fin B → Fin 6) (_hn : ∀ i k,xs i k≠blank),
      HoareTime P (fun w => w=bank input hcode xs)
        (fun w => w=bank input hcode (xs ∘ ActivePrefixStageRuntimeSelected.destination input))
        (cost (B:=B) 1 input hp)

private theorem bounded {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (hP : ActivePrefixStageNative.Spec P) (C : ℝ)
    (hcost : ∀ (s : Shape) (B : ℕ) (input : ActivePrefixStageFullData.Inputs s)
      (_hcode : s.payload=B*3+0) (hp : 1 < input.stage.f → ActivePrefixStageRuntimeData.Packed input 1),
      (cost (B:=B) 1 input hp : ℝ)≤C*(input.rows*s.recordWidth : ℕ)*
        ((max 1 ((input.stage.f-1)*s.guard) : ℕ) : ℝ)^Parameters.tau)
    {s : Shape} (B : ℕ) (input : ActivePrefixStageFullData.Inputs s) (hcode : s.payload=B*3+0)
    (hp : 1 < input.stage.f → ActivePrefixStageRuntimeData.Packed input 1) :
    BoundedSpec P C B input hcode := by
  exact ⟨hp,hcost s B input hcode hp,fun xs hn => hP 1 s B input hcode xs hn hp⟩

/-- A real fixed machine and one uniform cost constant handle all actual
nonfallback stages eventually. No readiness, packed allowance, runtime branch
or source-order selection is supplied by the caller. -/
theorem eventually_correct (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime,
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D j : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n) (_hj : j≤depth m (d n))
      (v : Stage (actualShape n c m D (payload n))),
      ∃ h : Ready (actualShape n c m D (payload n)) v (rowsAt c m (d n) (K n) j),
        BoundedSpec P C (symbols n) (inputs v (rowsAt c m (d n) (K n) j) h)
          (triple_capacity n c m D) := by
  obtain ⟨q,P,hP⟩ := ActivePrefixStageNative.exists_program
  obtain ⟨C,hC,hcost⟩ := ActivePrefixStageNative.uniform_bound 1
  refine ⟨q,P,C,hC,?_⟩
  filter_upwards [CompactActualStageGeometry.eventually_ready c m hc hm,
    CompactActualStageRuntime.eventually_packed c m hc hm] with n hr hpacked
  intro D j hcut hD hj v
  let h := hr D (payload n) j hcut hD (payload_allowance n) hj v
  exact ⟨h,bounded P hP C hcost (symbols n) _ (triple_capacity n c m D)
    (fun _ => hpacked D (payload n) j hcut hD (payload_allowance n) v h)⟩

end
end IntegerMultBounds.Machine.CompactActualNativeStage
