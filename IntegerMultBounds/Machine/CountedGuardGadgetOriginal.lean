import IntegerMultBounds.Machine.CountedGuardGadgetArray
import IntegerMultBounds.Machine.CountedGuardGadgetHeaders

/-! Whole original-header guard-word construction: q−1 is physically derived,
all records execute under fixed counted control, and the derived header is
physically erased. Only original q/b/n descriptors and literal words are input. -/
namespace IntegerMultBounds.Machine.CountedGuardGadgetOriginal
noncomputable section
variable {a : ℕ}
open SharedPlacementAlphabet
open CountedGuardGadgetRecord (bank word)

def extended (v : Tapes 13 a) (qs : List Bool) : Tapes 15 a :=
  v.append (⟨![1,0],![CountedLoopReuseAlphabet.binary qs,fun _ => blank]⟩ : Tapes 2 a)

def prepared (V W C1 C2 C3 : List Bool) (ds bs ns qs : List Bool) : Tapes 15 a :=
  extended (CountedGuardGadgetArray.input
    (bank V W C1 C2 C3 (fun _ => blank) 0 0 0 0 0 0 ds bs) ns) qs

def input (V W C1 C2 C3 : List Bool) (bs ns qs : List Bool) : Tapes 15 a :=
  setTape (prepared V W C1 C2 C3 [] bs ns qs) 8 (fun _ => blank) 0

def loopOutput (q b n : ℕ) (V W C1 C2 C3 : List Bool) (ds bs ns qs : List Bool) : Tapes 15 a :=
  extended (CountedGuardGadgetArray.input
    (CountedGuardGadgetArray.stateW q b n V W C1 C2 C3 ds bs n) ns) qs

def output (q b n : ℕ) (V W C1 C2 C3 : List Bool) (bs ns qs : List Bool) : Tapes 15 a :=
  setTape (loopOutput q b n V W C1 C2 C3 (RecursiveChildQuotientsConstant.bits (q-1)) bs ns qs) 8 (fun _ => blank) 0

def headerPlace : Fin (3+12) ≃ Fin 15 where
  toFun := ![13,14,8,0,1,2,3,4,5,6,7,9,10,11,12]
  invFun := ![3,4,5,6,7,8,9,10,2,11,12,13,14,0,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def setup := Placement.placed (CountedGuardGadgetHeaders.program (a := a)) headerPlace
def loops := extend (CountedGuardGadgetArray.program (a := a)) 2
def cleanup := BinaryDescriptorCleanupList.oneProgram (a := a) (8 : Fin 15)
def program := seq (seq (setup (a := a)) loops) cleanup

theorem setsUp (V W C1 C2 C3 : List Bool) (bs ns qs : List Bool) (q : ℕ)
    (hq : Counter.value qs=q) (cq : GrowingCounterData.Canonical qs) (hp : 1 ≤ q) :
    HoareTime (setup (a := a)) (fun v => v=input V W C1 C2 C3 bs ns qs)
      (fun v => v=prepared V W C1 C2 C3 (RecursiveChildQuotientsConstant.bits (q-1)) bs ns qs) (6*q+44) := by
  have h := Placement.hoare_at (CountedGuardGadgetHeaders.constructs (a := a) qs q hq cq hp)
    headerPlace (input (a := a) V W C1 C2 C3 bs ns qs) (by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | (change BinaryDescriptorStack.descriptor _=CountedLoopReuseAlphabet.binary _; rw [CountedGuardGadgetHeaders.binary_eq,BinaryDescriptorStackRoundtrip.descriptor_encoded])

theorem stateV_zero (q : ℕ) (V W C1 C2 C3 : List Bool) (ds bs : List Bool) :
    CountedGuardGadgetArray.stateV (a := a) q V W C1 C2 C3 ds bs 0=
      bank V W C1 C2 C3 (fun _ => blank) 0 0 0 0 0 0 ds bs := by
  simp only [CountedGuardGadgetArray.stateV,Nat.zero_mul,Nat.mul_zero,Nat.cast_zero,
    GuardGadget.flagWordV,word,List.map_nil,putWord]

theorem runs (q b n : ℕ) (V W C1 C2 C3 : List Bool) (bs ns qs : List Bool)
    (hp : 1 ≤ q) (hq : Counter.value qs=q) (cq : GrowingCounterData.Canonical qs)
    (hb : Counter.value bs=b) (cb : GrowingCounterData.Canonical bs)
    (hn : Counter.value ns=n) (cn : GrowingCounterData.Canonical ns)
    (hV : V.length=n*q) (hW : W.length=n*b)
    (hc1 : C1.length=q-1) (hc2 : C2.length=q-1) (hc3 : C3.length=b) :
    HoareTime (program (a := a)) (fun v => v=input V W C1 C2 C3 bs ns qs)
      (fun v => v=output q b n V W C1 C2 C3 bs ns qs)
      (n*(44*q+15*b+165)+8*q+106) := by
  let ds := RecursiveChildQuotientsConstant.bits (q-1)
  have hs := setsUp (a := a) V W C1 C2 C3 bs ns qs q hq cq hp
  have hl := CountedGuardGadgetArray.runs_linear (a := a) q b n V W C1 C2 C3 ds bs ns hp
    (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_canonical _)
    hb cb hn cn hV hW hc1 hc2 hc3
  have he := hoare_extend_eq hl (⟨![1,0],![CountedLoopReuseAlphabet.binary qs,fun _ => blank]⟩ : Tapes 2 a)
  have e := stateV_zero (a := a) q V W C1 C2 C3 ds bs
  rw [e] at he
  have hc := BinaryDescriptorCleanupList.one_hoare (8 : Fin 15)
    (loopOutput (a := a) q b n V W C1 C2 C3 ds bs ns qs) ds
    (by change CountedLoopReuseAlphabet.binary ds=BinaryDescriptorStack.descriptor ds
        rw [CountedGuardGadgetHeaders.binary_eq,BinaryDescriptorStackRoundtrip.descriptor_encoded]) rfl
  have ec : setTape (loopOutput (a := a) q b n V W C1 C2 C3 ds bs ns qs) 8 (fun _ => blank) 0=
      output q b n V W C1 C2 C3 bs ns qs := rfl
  rw [ec] at hc
  have hd := GrowingCounterData.canonical_width ds (RecursiveChildQuotientsConstant.bits_canonical _)
  rw [RecursiveChildQuotientsConstant.bits_value] at hd
  have hnq := Nat.log2_le_self (q-1)
  exact ((hs.seq he).seq hc).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CountedGuardGadgetOriginal
