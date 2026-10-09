import IntegerMultBounds.Machine.CountedGuardGadget
import IntegerMultBounds.Compact.GuardValue

/-! The actual fixed-control runtime guard result decides exceptional address
membership. Literal constant words have certified widths and values; their
physical synthesis and the later rank-splitting repair program remain separate. -/
namespace IntegerMultBounds.Machine.CountedGuardGadgetValue
noncomputable section
variable {a : ℕ}
open IntegerMultBounds.Counter (value)
open IntegerMultBounds.Compact
open IntegerMultBounds.Compact.PowerTwo

theorem word_bound (X : List Bool) (n w : ℕ) (hX : X.length=n*w) :
    (value X : ℤ)<((2 : ℤ)^w)^n := by
  rw [← pow_mul,Nat.mul_comm w n,← hX]
  exact_mod_cast Counter.value_lt X

theorem first_bound (q n : ℕ) (V : List Bool) (hV : V.length=n*q) (hq : 1 ≤ q) :
    (value V : ℤ)<(2*(2 : ℤ)^(q-1))^n := by
  have h : (2 : ℤ)*2^(q-1)=2^q := by
    rw [← pow_succ']; congr 1; omega
  rw [h]
  exact word_bound V n q hV

def address (q b n : ℕ) (V W : List Bool) (hV : V.length=n*q) (hW : W.length=n*b) (hq : 1 ≤ q) : EarlyAddress ((2 : ℤ)^b) ((2 : ℤ)^(q-1)) n :=
  (⟨(value V : ℤ),by positivity,first_bound q n V hV hq⟩,
   ⟨(value W : ℤ),by positivity,word_bound W n b hW⟩)

/-- The physically written result cell is one exactly for exceptional
addresses, under the manuscript's three certified comparison constants. -/
theorem result_iff_bad (q b n : ℕ) (V W C1 C2 C3 : List Bool) (bs ns qs : List Bool)
    (hV : V.length=n*q) (hW : W.length=n*b) (hbq : b+3 ≤ q)
    (hc1 : C1.length=q-1) (hc2 : C2.length=q-1) (hc3 : C3.length=b)
    (hv1 : value C1=2^(b+1)) (hv2 : value C2+2^(b+1)+1=2^(q-1)) (hv3 : value C3+2=2^b) :
    ((CountedGuardGadget.output (a := a) q b n V W C1 C2 C3 bs ns qs).tape 14 0=bitSymbol true) ↔
      ¬ earlyGood ((2 : ℤ)^b) ((2 : ℤ)^(q-1)) n
        (address q b n V W hV hW (by omega)) := by
  rw [(CountedGuardGadget.result (a := a) q b n V W C1 C2 C3 bs ns qs).2]
  change bitSymbol ((CountedGuardGadget.flags q b n V W C1 C2 C3).any id)=bitSymbol true ↔ _
  have he (x : Bool) : (bitSymbol (a := a) x=bitSymbol true) ↔ x=true := by
    cases x <;> simp [bitSymbol]
  rw [he]
  exact flags_any q b n V W C1 C2 C3 hV hW hbq hc1 hc2 hc3 hv1 hv2 hv3
    (first_bound q n V hV (by omega)) (word_bound W n b hW)

/-- Full paid tape execution, with the actual exceptional-membership bit in
the postcondition. Original canonical descriptors are retained and all private
storage is restored as specified by CountedGuardGadget.output. -/
theorem runs_decides (q b n : ℕ) (V W C1 C2 C3 : List Bool) (bs ns qs : List Bool)
    (hq : Counter.value qs=q) (cq : GrowingCounterData.Canonical qs)
    (hb : Counter.value bs=b) (cb : GrowingCounterData.Canonical bs)
    (hn : Counter.value ns=n) (cn : GrowingCounterData.Canonical ns)
    (hV : V.length=n*q) (hW : W.length=n*b) (hbq : b+3 ≤ q)
    (hc1 : C1.length=q-1) (hc2 : C2.length=q-1) (hc3 : C3.length=b)
    (hv1 : value C1=2^(b+1)) (hv2 : value C2+2^(b+1)+1=2^(q-1)) (hv3 : value C3+2=2^b) :
    HoareTime (CountedGuardGadget.program (a := a))
      (fun v => v=CountedGuardGadget.input V W C1 C2 C3 bs ns qs)
      (fun v => v=CountedGuardGadget.output q b n V W C1 C2 C3 bs ns qs ∧
        ((v.tape 14 0=bitSymbol true) ↔ ¬ earlyGood ((2 : ℤ)^b) ((2 : ℤ)^(q-1)) n
          (address q b n V W hV hW (by omega))))
      (350*(n+1)*(q+b+1)) := by
  have h := CountedGuardGadget.runs (a := a) q b n V W C1 C2 C3 bs ns qs
    (by omega) hq cq hb cb hn cn hV hW hc1 hc2 hc3
  refine h.consequence (fun _ h => h) ?_ (CountedGuardGadget.cost_volume q b n)
  rintro v rfl
  exact ⟨rfl,result_iff_bad q b n V W C1 C2 C3 bs ns qs hV hW hbq hc1 hc2 hc3 hv1 hv2 hv3⟩

end
end IntegerMultBounds.Machine.CountedGuardGadgetValue
