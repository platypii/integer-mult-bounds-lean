import IntegerMultBounds.Machine.ActiveTargetHighestLaterClean
import IntegerMultBounds.Machine.Alphabet

/-! Exact alphabet simulation for the highest-bit machine inside the binary
interchange bank. Numerical codes and the real transition count are retained. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLaterAlphabet
noncomputable section
open Networks.Shared50ModularControl (prime)

def encoding : Alphabet.Encoding 2 prime where
  encode x := ⟨x.val, by have := x.isLt; have := Networks.Shared50ModularControl.prime_odd; omega⟩
  decode x := if h : x.val<6 then ⟨x.val,h⟩ else blank
  decode_encode := by intro x; simp [x.isLt]

@[simp] theorem encode_blank : encoding.encode blank=blank := rfl
@[simp] theorem encode_bit (b : Bool) : encoding.encode (bitSymbol b)=bitSymbol b := rfl
@[simp] theorem encode_separator : encoding.encode separator=separator := rfl

def program := Alphabet.program encoding ActiveTargetHighestRun.program

def input (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool)
    (x : ActiveTargetHighestRun.Array G L B) (bs qs ns : List Bool) :=
  Alphabet.mapTapes encoding (ActiveTargetHighestRun.input G L ws x bs qs ns)

theorem runs (G L B : ℕ) (hB : 0<B) (ws : Fin 3 → List Bool)
    (x : ActiveTargetHighestRun.Array G L B) (bs qs ns : List Bool)
    (hw : ∀ i, Counter.value (ws i)=ActiveTargetHighestRun.width G L i)
    (cw : ∀ i, GrowingCounterData.Canonical (ws i))
    (hb : Counter.value bs=B) (hq : Counter.value qs=2)
    (hn : Counter.value ns=ActiveTargetHighestRun.prefixSize G L)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) :
    HoareTime program (fun v => v=input G L ws x bs qs ns)
      (fun v => v=input G L ws (ActiveTargetHighestRun.array G L x) bs qs ns)
      (ActiveTargetHighestRun.constant*ActiveTargetHighestRun.volume G L B) := by
  have h := Alphabet.map_hoare encoding (ActiveTargetHighestRun.runs G L B hB ws x bs qs ns hw cw hb hq hn cb cq cn)
  apply h.consequence ?_ ?_ le_rfl
  · rintro v rfl
    exact ⟨_,rfl,rfl⟩
  · rintro v ⟨a,rfl,rfl⟩
    rw [ActiveTargetHighestLaterClean.output_eq_input]
    rfl

end
end IntegerMultBounds.Machine.ActiveTargetHighestLaterAlphabet
