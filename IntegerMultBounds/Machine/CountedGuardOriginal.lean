import IntegerMultBounds.Machine.CountedGuardOriginalSetup
import IntegerMultBounds.Machine.CountedGuardOriginalCleanup
import IntegerMultBounds.Machine.CountedGuardGadgetValue

/-! The complete original-input fixed-control exceptional-address guard.
Only V/W and canonical q/b/n are supplied. Comparison constants, derived
counts and flags are physically constructed and erased; the sole retained
private output is the actual exceptional-membership bit. -/
namespace IntegerMultBounds.Machine.CountedGuardOriginal
noncomputable section
variable {a : ℕ}
open CountedGuardConstantsData
open CountedGuardGadgetRecord (word)
open IntegerMultBounds.Compact

def input := CountedGuardOriginalSetup.input (a := a)
def output (q b n : ℕ) (V W : List Bool) (bs ns qs : List Bool) : Tapes 15 a :=
  CountedGuardOriginalCleanup.output
    (CountedGuardGadget.output q b n V W (c1 q b) (c2 q b) (c3 b) bs ns qs)
def program := seq (seq (CountedGuardOriginalSetup.program (a := a)) CountedGuardGadget.program) CountedGuardOriginalCleanup.program

theorem cleanup_hoare (q b n : ℕ) (V W : List Bool) (bs ns qs : List Bool)
    (hb : 1 ≤ b) (hbq : b+3 ≤ q) :
    HoareTime (CountedGuardOriginalCleanup.program (a := a))
      (fun v => v=CountedGuardGadget.output q b n V W (c1 q b) (c2 q b) (c3 b) bs ns qs)
      (fun v => v=output q b n V W bs ns qs) (4*q+2*b+11) := by
  obtain ⟨h1p,h1t,h2p,h2t,h3p,h3t⟩ := CountedGuardGadget.constants (a := a) q b n V W (c1 q b) (c2 q b) (c3 b) bs ns qs
  have h := CountedGuardOriginalCleanup.runs
    (CountedGuardGadget.output (a := a) q b n V W (c1 q b) (c2 q b) (c3 b) bs ns qs)
    (c1 q b) (c2 q b) (c3 b) h1t h1p h2t h2p h3t h3p
  obtain ⟨l1,l2,l3⟩ := lengths q b hb hbq
  exact h.consequence (fun _ h => h) (fun _ h => h) (by rw [l1,l2,l3]; omega)

/-- Full actual execution, including constant synthesis and all cleanup.
The same fifteen tapes and finite control work for every admissible width
and record count, including the empty address. -/
theorem runs (q b n : ℕ) (V W : List Bool) (bs ns qs : List Bool)
    (hq : Counter.value qs=q) (cq : GrowingCounterData.Canonical qs)
    (hvb : Counter.value bs=b) (cb : GrowingCounterData.Canonical bs)
    (hn : Counter.value ns=n) (cn : GrowingCounterData.Canonical ns)
    (hb : 1 ≤ b) (hbq : b+3 ≤ q) (hV : V.length=n*q) (hW : W.length=n*b) :
    HoareTime (program (a := a)) (fun v => v=input V W bs ns qs)
      (fun v => v=output q b n V W bs ns qs)
      (n*(45*q+16*b+174)+52*q+82*b+433) := by
  have h1 := CountedGuardOriginalSetup.runs (a := a) q b V W bs ns qs hq cq hvb cb hb hbq
  obtain ⟨l1,l2,l3⟩ := lengths q b hb hbq
  have h2 := CountedGuardGadget.runs (a := a) q b n V W (c1 q b) (c2 q b) (c3 b) bs ns qs
    (by omega) hq cq hvb cb hn cn hV hW l1 l2 l3
  have h3 := cleanup_hoare (a := a) q b n V W bs ns qs hb hbq
  exact ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem cost_volume (q b n : ℕ) :
    n*(45*q+16*b+174)+52*q+82*b+433 ≤ 1000*(n+1)*(q+b+1) := by
  ring_nf
  omega

/-- The actual retained result bit is one precisely for exceptional addresses;
constant widths and values are derived internally from synthesized patterns. -/
theorem result_iff_bad (q b n : ℕ) (V W : List Bool) (bs ns qs : List Bool)
    (hb : 1 ≤ b) (hbq : b+3 ≤ q) (hV : V.length=n*q) (hW : W.length=n*b) :
    ((output (a := a) q b n V W bs ns qs).tape 14 0=bitSymbol true) ↔
      ¬ earlyGood ((2 : ℤ)^b) ((2 : ℤ)^(q-1)) n
        (CountedGuardGadgetValue.address q b n V W hV hW (by omega)) := by
  obtain ⟨l1,l2,l3⟩ := lengths q b hb hbq
  obtain ⟨v1,v2,v3⟩ := values q b hb hbq
  change ((CountedGuardGadget.output (a := a) q b n V W (c1 q b) (c2 q b) (c3 b) bs ns qs).tape 14 0=bitSymbol true) ↔ _
  exact CountedGuardGadgetValue.result_iff_bad q b n V W (c1 q b) (c2 q b) (c3 b) bs ns qs
    hV hW hbq l1 l2 l3 v1 v2 v3

theorem runs_decides (q b n : ℕ) (V W : List Bool) (bs ns qs : List Bool)
    (hq : Counter.value qs=q) (cq : GrowingCounterData.Canonical qs)
    (hvb : Counter.value bs=b) (cb : GrowingCounterData.Canonical bs)
    (hn : Counter.value ns=n) (cn : GrowingCounterData.Canonical ns)
    (hb : 1 ≤ b) (hbq : b+3 ≤ q) (hV : V.length=n*q) (hW : W.length=n*b) :
    HoareTime (program (a := a)) (fun v => v=input V W bs ns qs)
      (fun v => v=output q b n V W bs ns qs ∧
        ((v.tape 14 0=bitSymbol true) ↔ ¬ earlyGood ((2 : ℤ)^b) ((2 : ℤ)^(q-1)) n
          (CountedGuardGadgetValue.address q b n V W hV hW (by omega))))
      (1000*(n+1)*(q+b+1)) := by
  have h := runs (a := a) q b n V W bs ns qs hq cq hvb cb hn cn hb hbq hV hW
  refine h.consequence (fun _ h => h) ?_ (cost_volume q b n)
  rintro v rfl
  exact ⟨rfl,result_iff_bad q b n V W bs ns qs hb hbq hV hW⟩

theorem sources (q b n : ℕ) (V W : List Bool) (bs ns qs : List Bool) :
    (output (a := a) q b n V W bs ns qs).tape 0=word V ∧ (output (a := a) q b n V W bs ns qs).head 0=0 ∧
    (output (a := a) q b n V W bs ns qs).tape 1=word W ∧ (output (a := a) q b n V W bs ns qs).head 1=0 :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem private_clean (q b n : ℕ) (V W : List Bool) (bs ns qs : List Bool) (i : Fin 15)
    (hi : i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=10 ∨ i=11) :
    (output (a := a) q b n V W bs ns qs).tape i=(fun _ => blank) ∧
    (output (a := a) q b n V W bs ns qs).head i=0 := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl,rfl⟩

theorem headers (q b n : ℕ) (V W : List Bool) (bs ns qs : List Bool) :
    (output (a := a) q b n V W bs ns qs).head 9=1 ∧
    (output (a := a) q b n V W bs ns qs).tape 9=CountedLoopReuseAlphabet.binary bs ∧
    (output (a := a) q b n V W bs ns qs).head 12=1 ∧
    (output (a := a) q b n V W bs ns qs).tape 12=CountedLoopReuseAlphabet.binary ns ∧
    (output (a := a) q b n V W bs ns qs).head 13=1 ∧
    (output (a := a) q b n V W bs ns qs).tape 13=CountedLoopReuseAlphabet.binary qs :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem result (q b n : ℕ) (V W : List Bool) (bs ns qs : List Bool) :
    (output (a := a) q b n V W bs ns qs).head 14=1 ∧
    (output (a := a) q b n V W bs ns qs).tape 14=
      CountedGuardGadgetFinish.key (CountedGuardGadget.flags q b n V W (c1 q b) (c2 q b) (c3 b)) :=
  ⟨rfl,rfl⟩

end
end IntegerMultBounds.Machine.CountedGuardOriginal
