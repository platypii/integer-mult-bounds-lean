import IntegerMultBounds.Machine.ActivePrefixOffsetHeadersBudget
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Paid post-use erasure of all five derived active-prefix descriptors.
Every original/spectator tape is preserved and each output returns blank at zero. -/
namespace IntegerMultBounds.Machine.ActivePrefixOffsetHeadersCleanup
noncomputable section
open SharedPlacementAlphabet (setTape)
open ActivePrefixOffsetHeadersData
variable {t a : ℕ}

def cleared (caller : Tapes t a) (focus : Fin 5 → Fin t) :=
  setTape (setTape (setTape (setTape (setTape caller (focus 0) (fun _ => blank) 0)
    (focus 1) (fun _ => blank) 0) (focus 2) (fun _ => blank) 0) (focus 3) (fun _ => blank) 0)
    (focus 4) (fun _ => blank) 0

def program (focus : Fin 5 → Fin t) := seq (seq (seq (seq
  (BinaryDescriptorCleanupList.oneProgram (a := a) (focus 0))
  (BinaryDescriptorCleanupList.oneProgram (a := a) (focus 1)))
  (BinaryDescriptorCleanupList.oneProgram (a := a) (focus 2)))
  (BinaryDescriptorCleanupList.oneProgram (a := a) (focus 3)))
  (BinaryDescriptorCleanupList.oneProgram (a := a) (focus 4))

def cost (hs : Fin 5 → List Bool) :=
  2*((hs 0).length+(hs 1).length+(hs 2).length+(hs 3).length+(hs 4).length)+24

theorem cleans (caller : Tapes t a) (focus : Fin 5 → Fin t) (hf : Function.Injective focus)
    (hs : Fin 5 → List Bool)
    (ht : ∀ i, caller.tape (focus i)=RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (focus i)=1) :
    HoareTime (program (a := a) focus) (fun v => v=caller)
      (fun v => v=cleared caller focus) (cost hs) := by
  have hdesc (i : Fin 5) : caller.tape (focus i)=BinaryDescriptorStack.descriptor (hs i) := by
    rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]
    exact ht i
  have h0 := BinaryDescriptorCleanupList.one_hoare (focus 0) caller (hs 0) (hdesc 0) (hh 0)
  have h1 := BinaryDescriptorCleanupList.one_hoare (focus 1)
    (setTape caller (focus 0) (fun _ => blank) 0) (hs 1)
    (by simpa [setTape,hf.eq_iff] using hdesc 1) (by simp [setTape,hf.eq_iff,hh])
  have h2 := BinaryDescriptorCleanupList.one_hoare (focus 2)
    (setTape (setTape caller (focus 0) (fun _ => blank) 0) (focus 1) (fun _ => blank) 0) (hs 2)
    (by simpa [setTape,hf.eq_iff] using hdesc 2) (by simp [setTape,hf.eq_iff,hh])
  have h3 := BinaryDescriptorCleanupList.one_hoare (focus 3)
    (setTape (setTape (setTape caller (focus 0) (fun _ => blank) 0)
      (focus 1) (fun _ => blank) 0) (focus 2) (fun _ => blank) 0) (hs 3)
    (by simpa [setTape,hf.eq_iff] using hdesc 3) (by simp [setTape,hf.eq_iff,hh])
  have h4 := BinaryDescriptorCleanupList.one_hoare (focus 4)
    (setTape (setTape (setTape (setTape caller (focus 0) (fun _ => blank) 0)
      (focus 1) (fun _ => blank) 0) (focus 2) (fun _ => blank) 0) (focus 3) (fun _ => blank) 0) (hs 4)
    (by simpa [setTape,hf.eq_iff] using hdesc 4) (by simp [setTape,hf.eq_iff,hh])
  exact ((((h0.seq h1).seq h2).seq h3).seq h4).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem cleared_outputs (caller : Tapes t a) (focus : Fin 5 → Fin t) (hf : Function.Injective focus) :
    ∀ i, (cleared caller focus).tape (focus i)=(fun _ => blank) ∧
      (cleared caller focus).head (focus i)=0 := by
  intro i
  fin_cases i <;> simp [cleared,setTape,hf.eq_iff]

theorem frame (caller : Tapes t a) (focus : Fin 5 → Fin t) (i : Fin t)
    (hi : ∀ j, i≠focus j) :
    (cleared caller focus).tape i=caller.tape i ∧ (cleared caller focus).head i=caller.head i := by
  simp [cleared,setTape,hi]

theorem cost_bound (hs : Fin 5 → List Bool) (V : ℕ) (hV : 0<V)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hv : ∀ i, Counter.value (hs i)≤V) : cost hs≤44*V := by
  have hlen (i : Fin 5) : (hs i).length≤2*V := by
    have h := GrowingCounterData.canonical_width (hs i) (hc i)
    have hl := Nat.log2_le_self (Counter.value (hs i))
    have hh := hv i
    omega
  have h0 := hlen 0
  have h1 := hlen 1
  have h2 := hlen 2
  have h3 := hlen 3
  have h4 := hlen 4
  unfold cost
  omega

theorem derived_cost (W q b n f : ℕ) (hq : 1≤q) (hnf : n+1=f)
    (hsource : f*q≤W) (htemp : n*b≤W) :
    cost (words W q b n f)≤44*ActivePrefixOffsetHeadersBudget.volume W :=
  cost_bound _ _ (ActivePrefixOffsetHeadersBudget.volume_pos W) (words_canonical W q b n f)
    (by intro i; rw [words_values]; exact ActivePrefixOffsetHeadersBudget.values_le W q b n f hq hnf hsource htemp i)

theorem cleans_result (caller : Tapes t a) (focus : Fin 10 → Fin t) (hf : Function.Injective focus)
    (W q b n f : ℕ) :
    HoareTime (program (a := a) (outputFocus focus))
      (fun v => v=result caller focus W q b n f)
      (fun v => v=cleared (result caller focus W q b n f) (outputFocus focus))
      (cost (words W q b n f)) :=
  cleans _ _ (output_injective focus hf) _ (result_headers caller focus hf W q b n f).1
    (result_headers caller focus hf W q b n f).2

end
end IntegerMultBounds.Machine.ActivePrefixOffsetHeadersCleanup
