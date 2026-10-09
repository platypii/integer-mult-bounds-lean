import IntegerMultBounds.Networks.ComplexRecursiveCallSchema
import IntegerMultBounds.Machine.FiniteReturnStackAt
import Mathlib.Data.Nat.Log

/-! Actual complex recursive call occurrences have distinct fixed-width return
addresses. A placed physical return stack saves and decodes those addresses,
retaining the full native bank when the stack slot is outside it. -/
namespace IntegerMultBounds.Machine.CompactComplexCallReturn
noncomputable section
open Networks.ComplexRecursiveCallSchema

def addressCount (siteCount base : ℕ) := siteCount*base
def addressWidth (siteCount base : ℕ) := Nat.clog 2 (addressCount siteCount base)

theorem roomFor (siteCount base : ℕ) : addressCount siteCount base ≤ 2^(addressWidth siteCount base) :=
  Nat.le_pow_clog (b := 2) (by decide) (addressCount siteCount base)

abbrev addresses := addressCount sites.length (25^3)
abbrev width := addressWidth sites.length (25^3)
abbrev room := roomFor sites.length (25^3)

private theorem pack_lt (base sites site coordinate : ℕ) (hs : site < sites)
    (hc : coordinate < base) : site*base+coordinate < sites*base := by
  have hm := Nat.mul_le_mul_right base (Nat.succ_le_of_lt hs)
  rw [Nat.succ_mul] at hm
  omega

private def packFin {base sites : ℕ} (site : Fin sites) (coordinate : Fin base) : Fin (sites*base) :=
  ⟨site.val*base+coordinate.val,pack_lt _ _ _ _ site.isLt coordinate.isLt⟩

def pc (call : Call) := packFin call.site call.slot

private theorem pack_injective (base : ℕ) (hp : 0 < base)
    (siteA coordinateA siteB coordinateB : ℕ) (ha : coordinateA < base) (hb : coordinateB < base)
    (he : siteA*base+coordinateA=siteB*base+coordinateB) :
    siteA=siteB ∧ coordinateA=coordinateB := by
  have hm := congrArg (fun n => n%base) he
  rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha] at hm
  rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb] at hm
  have hprod : siteA*base=siteB*base := by omega
  exact ⟨Nat.eq_of_mul_eq_mul_right hp hprod,hm⟩

private theorem call_ext {es : List Networks.ComplexPhaseRowSchedule.Edge}
    (a b : CallFor es) (hsite : a.site.val=b.site.val) (hcoordinate : a.coordinate.val=b.coordinate.val) : a=b := by
  cases a with | mk as ac =>
    cases b with | mk bs bc =>
      dsimp at hsite hcoordinate
      have hs : as=bs := Fin.ext hsite
      subst bs
      have hc : ac=bc := Fin.ext hcoordinate
      subst bc
      rfl

/-- The occurrence plus residual-coordinate address never merges calls merely
because their labels or physical role happen to coincide. -/
theorem pc_injective : Function.Injective pc := by
  intro a b he
  have h := pack_injective (25^3) (by decide) a.site.val a.coordinate.val b.site.val b.coordinate.val
    (by simpa only [slot_val] using a.slot.isLt)
    (by simpa only [slot_val] using b.slot.isLt) (by simpa only [pc,packFin,slot_val] using congrArg Fin.val he)
  exact call_ext a b h.1 h.2

def codeFor {siteCount base : ℕ} (site : Fin siteCount) (coordinate : Fin base) :=
  FiniteReturnStack.address (roomFor siteCount base) (packFin site coordinate)

def code (call : Call) := codeFor call.site call.slot

private theorem codeFor_injective {siteCount base : ℕ} (hp : 0 < base)
    (a b : Fin siteCount) (i j : Fin base) (he : codeFor a i=codeFor b j) : a=b ∧ i=j := by
  have hpc := FiniteReturnStack.address_injective (roomFor siteCount base) he
  have h := pack_injective base hp a.val i.val b.val j.val i.isLt j.isLt (congrArg Fin.val hpc)
  exact ⟨Fin.ext h.1,Fin.ext h.2⟩

theorem code_injective : Function.Injective code := by
  intro a b he
  have h := codeFor_injective (by decide : 0 < 25^3) a.site b.site a.slot b.slot he
  apply call_ext a b (congrArg Fin.val h.1)
  simpa only [slot_val] using congrArg Fin.val h.2

theorem retains_site {a b : Call} (h : code a=code b) : a.site=b.site :=
  congrArg CallFor.site (code_injective h)
theorem retains_role {a b : Call} (h : code a=code b) : a.role=b.role :=
  congrArg Call.role (code_injective h)
theorem retains_slot {a b : Call} (h : code a=code b) : a.slot=b.slot :=
  congrArg Call.slot (code_injective h)

variable {a t : ℕ}
def pushProgram (stack : Fin t) (call : Call) := FiniteReturnStackAt.pushProgram (a := a) (k := width) stack (code call)

theorem push (stack : Fin t) (call : Call) (v : Tapes t a) :
    HoareTime (pushProgram (a := a) stack call) (fun w => w=v)
      (fun w => w=FiniteReturnStackAt.pushed stack (code call) v) width :=
  FiniteReturnStackAt.push_hoare (k := width) stack (code call) v

def dispatcher {siteCount base : ℕ} (stack : Fin t) (states : Fin (addressCount siteCount base) → ℕ)
    (family : ∀ pc, Program t (states pc) a) : Σ n, Program t n a :=
  ⟨_,FiniteReturnStackAt.dispatchProgram (roomFor siteCount base) stack states family⟩

/-- Generic return decoding is proved before the huge actual site count is
specialized, retaining the exact saved occurrence/coordinate continuation. -/
theorem dispatch {siteCount base : ℕ} (stack : Fin t)
    (states : Fin (addressCount siteCount base) → ℕ) (family : ∀ pc, Program t (states pc) a)
    (site : Fin siteCount) (coordinate : Fin base) (v : Tapes t a)
    (f : ℤ → Fin (a+4)) (p : ℤ) (B : ℕ) (post : TapePred t a)
    (hs : v.tape stack=FiniteReturnStack.wordPart f p (codeFor site coordinate)
      (addressWidth siteCount base) le_rfl)
    (hh : v.head stack=p+addressWidth siteCount base)
    (hf : ∀ j < addressWidth siteCount base, f (p+j)=blank)
    (hc : HoareTime (family (packFin site coordinate))
      (fun w => w=SharedPlacementAlphabet.setTape v stack f p) post B) :
    HoareTime (dispatcher stack states family).2 (fun w => w=v) post (addressWidth siteCount base+2+B) :=
  FiniteReturnStackAt.dispatch_hoare (roomFor siteCount base) stack states family
    (packFin site coordinate) v f p B post hs hh hf hc


end
end IntegerMultBounds.Machine.CompactComplexCallReturn
