import IntegerMultBounds.Machine.CountedGuardGadgetOriginal
import IntegerMultBounds.Machine.CountedGuardGadgetFinish

/-! The complete fixed-control guard gadget from sole original q/b/n headers.
The exact legacy flag word is physically generated and reduced by AnyFlag;
all private tapes are restored, with both source heads at their origins. -/
namespace IntegerMultBounds.Machine.CountedGuardGadget
noncomputable section
variable {a : ℕ}
open SharedPlacementAlphabet
open CountedGuardGadgetRecord (word)

def flags (q b n : ℕ) (V W C1 C2 C3 : List Bool) := GuardGadget.flagWordW q b n V W C1 C2 C3 n
def input := CountedGuardGadgetOriginal.input (a := a)
def output (q b n : ℕ) (V W C1 C2 C3 : List Bool) (bs ns qs : List Bool) : Tapes 15 a :=
  CountedGuardGadgetFinish.output (CountedGuardGadgetOriginal.output q b n V W C1 C2 C3 bs ns qs)
    V W (flags q b n V W C1 C2 C3)
def program := seq (CountedGuardGadgetOriginal.program (a := a)) CountedGuardGadgetFinish.program

theorem finishes (q b n : ℕ) (V W C1 C2 C3 : List Bool) (bs ns qs : List Bool)
    (hV : V.length=n*q) (hW : W.length=n*b) :
    HoareTime (CountedGuardGadgetFinish.program (a := a))
      (fun v => v=CountedGuardGadgetOriginal.output q b n V W C1 C2 C3 bs ns qs)
      (fun v => v=output q b n V W C1 C2 C3 bs ns qs)
      (n*(q+b+9)+13) := by
  have hl : (flags q b n V W C1 C2 C3).length=3*n := by
    rw [flags,GuardGadget.flagWordW_length]; omega
  have h := CountedGuardGadgetFinish.runs
    (CountedGuardGadgetOriginal.output (a := a) q b n V W C1 C2 C3 bs ns qs)
    V W (flags q b n V W C1 C2 C3) rfl
    (by change ((n*q : ℕ) : ℤ)=((V.length : ℕ) : ℤ); rw [hV]) rfl
    (by change ((n*b : ℕ) : ℤ)=((W.length : ℕ) : ℤ); rw [hW]) rfl
    (by change ((2*n+n : ℕ) : ℤ)=(((flags q b n V W C1 C2 C3).length : ℕ) : ℤ); rw [hl]; push_cast; ring)
    rfl rfl
  exact h.consequence (fun _ h => h) (fun _ h => h) (by rw [hV,hW,hl]; ring_nf; omega)

/-- Original canonical q/b/n inputs suffice. No derived count, flags,
comparison order or countdown is supplied. All setup and erasure are paid,
including q=1 and n=0. -/
theorem runs (q b n : ℕ) (V W C1 C2 C3 : List Bool) (bs ns qs : List Bool)
    (hp : 1 ≤ q) (hq : Counter.value qs=q) (cq : GrowingCounterData.Canonical qs)
    (hb : Counter.value bs=b) (cb : GrowingCounterData.Canonical bs)
    (hn : Counter.value ns=n) (cn : GrowingCounterData.Canonical ns)
    (hV : V.length=n*q) (hW : W.length=n*b)
    (hc1 : C1.length=q-1) (hc2 : C2.length=q-1) (hc3 : C3.length=b) :
    HoareTime (program (a := a)) (fun v => v=input V W C1 C2 C3 bs ns qs)
      (fun v => v=output q b n V W C1 C2 C3 bs ns qs)
      (n*(45*q+16*b+174)+8*q+120) := by
  have h1 := CountedGuardGadgetOriginal.runs (a := a) q b n V W C1 C2 C3 bs ns qs hp hq cq hb cb hn cn hV hW hc1 hc2 hc3
  have h2 := finishes (a := a) q b n V W C1 C2 C3 bs ns qs hV hW
  exact (h1.seq h2).consequence (fun _ h => h) (fun _ h => h) (by ring_nf; omega)

theorem cost_volume (q b n : ℕ) :
    n*(45*q+16*b+174)+8*q+120 ≤ 350*(n+1)*(q+b+1) := by
  ring_nf
  omega

theorem input_private (V W C1 C2 C3 : List Bool) (bs ns qs : List Bool)
    (i : Fin 15) (hi : i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=10 ∨ i=11 ∨ i=14) :
    (input (a := a) V W C1 C2 C3 bs ns qs).head i=0 ∧
    (input (a := a) V W C1 C2 C3 bs ns qs).tape i=fun _ => blank := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl,rfl⟩

theorem constants (q b n : ℕ) (V W C1 C2 C3 : List Bool) (bs ns qs : List Bool) :
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).head 2=0 ∧
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).tape 2=word C1 ∧
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).head 3=0 ∧
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).tape 3=word C2 ∧
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).head 4=0 ∧
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).tape 4=word C3 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem result (q b n : ℕ) (V W C1 C2 C3 : List Bool) (bs ns qs : List Bool) :
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).head 14=1 ∧
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).tape 14=
      CountedGuardGadgetFinish.key (flags q b n V W C1 C2 C3) := by
  constructor <;> rfl

theorem sources (q b n : ℕ) (V W C1 C2 C3 : List Bool) (bs ns qs : List Bool) :
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).head 0=0 ∧
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).head 1=0 ∧
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).tape 0=word V ∧
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).tape 1=word W := ⟨rfl,rfl,rfl,rfl⟩

theorem private_clean (q b n : ℕ) (V W C1 C2 C3 : List Bool) (bs ns qs : List Bool)
    (i : Fin 15) (hi : i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=10 ∨ i=11) :
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).head i=0 ∧
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).tape i=fun _ => blank := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl,rfl⟩

theorem headers (q b n : ℕ) (V W C1 C2 C3 : List Bool) (bs ns qs : List Bool) :
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).head 9=1 ∧
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).tape 9=CountedLoopReuseAlphabet.binary bs ∧
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).head 12=1 ∧
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).tape 12=CountedLoopReuseAlphabet.binary ns ∧
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).head 13=1 ∧
    (output (a := a) q b n V W C1 C2 C3 bs ns qs).tape 13=CountedLoopReuseAlphabet.binary qs :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end IntegerMultBounds.Machine.CountedGuardGadget
