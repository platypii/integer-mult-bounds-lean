module

public import IntegerMultBounds.MathlibTM2.Cover.LabelSwap
public import IntegerMultBounds.MathlibTM2.Cover.FallbackSwapView

/-! Run a packed coordinate swap on the selected role with its interchange headers installed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (Descriptor volume)
open M8.RevMachine
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos w).ne'⟩

theorem swapView_runs [M8.Machine.Net] {T d w W : ℕ} {v : Descriptor}
    (i j : Fin d) (h : i < j) (size : volume prime v = (prime^w)^d*W) (hp : v.Positive)
    (io : Fin T) (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2)
    (hh : roles.head io = 0) (hx : roles.tape io = sourceWord x)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime) :
    let u := swapView prime w W i j
    ∃ y : Fin (volume prime v) → ZMod 2,
      GraphContract.Runs (LeafCore.core io)
        (CommonBank.bank roles (Routines.hdr u) f p node scalar ctr st)
        (CommonBank.bank (SharedPlacementAlphabet.setTape roles io (sourceWord y) 0)
          (Routines.hdr u) f p node scalar ctr st)
        (LeafCore.coreCost (volume prime v) u.width) ∧
        ∀ (coords : Fin d → ZMod (prime^w)) (k : Fin W),
          ext y (FlatCoordinateLayout.index (coords ∘ Equiv.swap i j) k).val =
            ext x (FlatCoordinateLayout.index coords k).val := by
  obtain ⟨y,run,swap⟩ := LabelExchange.realizes_view ((swapView_volume i j h).trans size.symm)
    hp io roles x hh hx f p node scalar ctr st
  exact ⟨y,run,fun coords k => swapView_apply i j h swap coords k⟩

/-- The coordinate tuple occupies the whole prefix; each tuple carries one payload record. -/
def payloadView (q d w W : ℕ) : Descriptor := ⟨1,1,q^(d*w),0,1,W⟩

theorem swapPayload_runs [M8.Machine.Net] {T d w W : ℕ}
    (i j : Fin d) (h : i < j) (hw : 0 < w) (hW : 0 < W)
    (roles : Tapes T prime) (io : Fin T)
    (x : Fin (volume prime (payloadView prime d w W)) → ZMod 2)
    (hh : roles.head io = 0) (hx : roles.tape io = sourceWord x) :
    let v := payloadView prime d w W
    let headers := LabelPrepare.input v d i.val j.val w
    ∃ y : Fin (volume prime v) → ZMod 2,
      GraphContract.Runs (LabelSwap.program io) (LabelCall.bank roles v headers)
        (LabelCall.bank (SharedPlacementAlphabet.setTape roles io (sourceWord y) 0) v headers)
        (3808274 * volume prime v + LeafCore.coreCost (volume prime v) w) ∧
      ∀ (coords : Fin d → ZMod (prime^w)) (k : Fin W),
        ext y (FlatCoordinateLayout.index (coords ∘ Equiv.swap i j) k).val =
          ext x (FlatCoordinateLayout.index coords k).val := by
  let v := payloadView prime d w W
  have hv : v.beforeH = 1*prime^(d*w) := by simp [v,payloadView]
  have hp : v.Positive := by simp [v,payloadView,Descriptor.Positive,hW,prime_prime.pos]
  obtain ⟨y,swap,run⟩ := LabelSwap.runs h j.isLt hw (by decide : 0 < 1) hv hp roles io x hh hx
  have view : LabelView.colView prime w d i.val j.val 1 v = swapView prime w W i j := by
    simp [LabelView.colView,swapView,v,payloadView,FlatCoordinateLayout.suffixFields,
      ← pow_mul,Nat.mul_comm, Nat.sub_sub, Nat.add_comm]
  rw [view] at swap
  exact ⟨y,run,fun coords k => swapView_apply i j h swap coords k⟩

/-- Conjugate a lower shear on the prepared role by the two physical coordinate swaps. -/
theorem upperShear_runs [M8.Machine.Net] {T d w W cost : ℕ}
    (i j : Fin d) (h : i < j) (hw : 0 < w) (hW : 0 < W) (c : ZMod (prime^w))
    (roles : Tapes T prime) (io : Fin T) (shear : Graph.Block (T+24) prime) (leading : Blocks.Leading shear)
    (x : Fin (volume prime (payloadView prime d w W)) → ZMod 2)
    (hh : roles.head io = 0) (hx : roles.tape io = sourceWord x) :
    let v := payloadView prime d w W
    let headers := LabelPrepare.input v d i.val j.val w
    let bank := fun y => LabelCall.bank (SharedPlacementAlphabet.setTape roles io (sourceWord y) 0) v headers
    let swap := LabelSwap.program io
    let time := 3808274 * volume prime v + LeafCore.coreCost (volume prime v) w
    (∀ a : Fin (volume prime v) → ZMod 2, ∃ b : Fin (volume prime v) → ZMod 2,
      GraphContract.Runs shear (bank a) (bank b) cost ∧
      ∀ (z : Fin d → ZMod (prime^w)) (k : Fin W),
        ext b (FlatCoordinateLayout.index (Function.update z j (z j+c*z i)) k).val =
          ext a (FlatCoordinateLayout.index z k).val) →
    ∃ y : Fin (volume prime v) → ZMod 2,
      GraphContract.Runs (Blocks.seqB (Blocks.seqB swap shear) swap)
        (LabelCall.bank roles v headers) (bank y) (time+cost+1+time+1) ∧
      ∀ (z : Fin d → ZMod (prime^w)) (k : Fin W),
        ext y (FlatCoordinateLayout.index (Function.update z i (z i+c*z j)) k).val =
          ext x (FlatCoordinateLayout.index z k).val := by
  intro v headers bank swap time lower
  obtain ⟨a,first,exchange⟩ := swapPayload_runs i j h hw hW roles io x hh hx
  obtain ⟨b,middle,add⟩ := lower a
  obtain ⟨y,last,back⟩ := swapPayload_runs i j h hw hW
    (SharedPlacementAlphabet.setTape roles io (sourceWord b) 0) io b
    (by simp [SharedPlacementAlphabet.setTape]) (by simp [SharedPlacementAlphabet.setTape])
  simp only [SharedPlacementAlphabet.setTape_setTape] at last
  have hs : Blocks.Leading swap := Blocks.seq_leading _ _
  refine ⟨y,Blocks.seq_runs (Blocks.seq_leading _ _) hs (Blocks.seq_runs hs leading first middle) last,?_⟩
  intro z k
  let u := z ∘ Equiv.swap i j
  have coord : Function.update u j (u j+c*u i) ∘ Equiv.swap i j = Function.update z i (z i+c*z j) := by
    funext t
    by_cases hi : t = i
    · subst t; simp [u]
    by_cases hj : t = j
    · subst t; simp [u,h.ne,h.ne']
    simp [u,Function.comp_def,Equiv.swap_apply_of_ne_of_ne hi hj,hi,hj]
  rw [← coord,back,add,exchange]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
