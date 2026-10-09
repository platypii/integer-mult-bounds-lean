import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatLoop

/-! Complete fixed-control offset expansion. All four countdown sentinels
start blank and are erased; the base table is consumed and erased, output is
rewound, and all original W/L/N/K descriptors remain intact. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetRepeat
open SharedPlacementAlphabet (setTape)
open CountedCopyReuse (empty binary)
open BinaryAddressOffsetRepeatData
noncomputable section

def raw (f g : ℤ → Fin 4) (p q : ℤ) (hs : Fin 4 → List Bool) : Tapes 11 0 :=
  ⟨![p,q,0,0,1,0,1,0,1,0,1],![f,g,(fun _ => blank),(fun _ => blank),binary (hs 0),
    (fun _ => blank),binary (hs 1),(fun _ => blank),binary (hs 2),(fun _ => blank),binary (hs 3)]⟩
def bank (f g : ℤ → Fin 4) (p q : ℤ) (hs : Fin 4 → List Bool) :=
  BinaryAddressOffsetRepeatLoop.bank f g p q (hs 0) (hs 1) (hs 2) (hs 3)

def oneInit (slot : Fin 11) := Placement.placed (RecursiveChildQuotientsConstant.program (a := 0) 0)
  (FiniteReturnStackAt.placement slot)
def setup := seq (seq (seq (oneInit 3) (oneInit 5)) (oneInit 7)) (oneInit 9)
def clocks : List (Fin 11) := [3,5,7,9]
def clearClocks := BinaryDescriptorCleanupList.program (a := 0) (by decide : 0<11) clocks
def rewind := Placement.placed (ReturnOrigin.program (a := 0)) (FiniteReturnStackAt.placement (1 : Fin 11))
def eraseSource := WordBankCleanup.clearProgram (0 : Fin 11) (by decide) 0
def program := seq (seq (seq (seq setup BinaryAddressOffsetRepeatLoop.program) clearClocks) rewind) eraseSource

theorem init_hoare (slot : Fin 11) (v : Tapes 11 0) (ht : v.tape slot=fun _ => blank) (hh : v.head slot=0) :
    HoareTime (oneInit slot) (fun z => z=v) (fun z => z=setTape v slot empty 1) 6 := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := 0) 0)
    (FiniteReturnStackAt.placement slot) v (by rw [FiniteReturnStackAt.active_bank,ht,hh])
  apply h.consequence (fun _ h => h) _ (by decide)
  rintro z ⟨small,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

theorem setup_hoare (f g : ℤ → Fin 4) (p q : ℤ) (hs : Fin 4 → List Bool) :
    HoareTime setup (fun z => z=raw f g p q hs) (fun z => z=bank f g p q hs) 27 := by
  let v1 := setTape (raw f g p q hs) 3 empty 1
  let v2 := setTape v1 5 empty 1
  let v3 := setTape v2 7 empty 1
  have h0 := init_hoare 3 (raw f g p q hs) rfl rfl
  have h1 := init_hoare 5 v1 rfl rfl
  have h2 := init_hoare 7 v2 rfl rfl
  have h3 := init_hoare 9 v3 rfl rfl
  have he : setTape v3 9 empty 1=bank f g p q hs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h3
  exact ((h0.seq h1).seq h2).seq h3

theorem clear_clocks (f g : ℤ → Fin 4) (p q : ℤ) (hs : Fin 4 → List Bool) :
    HoareTime clearClocks (fun z => z=bank f g p q hs) (fun z => z=raw f g p q hs) 20 := by
  have hh := BinaryDescriptorCleanupList.cleanup_hoare (by decide : 0<11) clocks (by decide)
    (fun _ => []) (bank f g p q hs) (by
      intro i hi
      simp only [clocks,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> exact ⟨rfl,rfl⟩)
  have he : BinaryDescriptorCleanupList.cleared clocks (bank f g p q hs)=raw f g p q hs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  simpa only [he,clearClocks,show BinaryDescriptorCleanupList.cost clocks (fun _ => [])=20 by decide] using hh

theorem rewinds (xs : List Bool) (f : ℤ → Fin 4) (hs : Fin 4 → List Bool) :
    HoareTime rewind (fun z => z=raw f (putWord (fun _ => blank) 0 (xs.map bitSymbol)) 0 xs.length hs)
      (fun z => z=raw f (putWord (fun _ => blank) 0 (xs.map bitSymbol)) 0 0 hs) (xs.length+2) := by
  have hr := ReturnOrigin.return_hoare_at (fun _ => (blank : Fin 4)) 0 (xs.map bitSymbol)
    (ReturnOrigin.bits_nonblank xs) rfl
  simp only [List.length_map,zero_add] at hr
  have ha : Placement.active (FiniteReturnStackAt.placement (1 : Fin 11))
      (raw f (putWord (fun _ => blank) 0 (xs.map bitSymbol)) 0 xs.length hs)=
      (ReturnOrigin.cfg (putWord (fun _ => blank) 0 (xs.map bitSymbol)) xs.length 0).tapes := by
    rw [FiniteReturnStackAt.active_bank]; rfl
  apply (Placement.hoare_at hr (FiniteReturnStackAt.placement (1 : Fin 11)) _ ha).consequence
    (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (putWord (fun _ => blank) 0 (xs.map bitSymbol)) 0)=_
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem erases (xs : List Bool) (g : ℤ → Fin 4) (hs : Fin 4 → List Bool) :
    HoareTime eraseSource (fun z => z=raw (putWord (fun _ => blank) 0 (xs.map bitSymbol)) g 0 0 hs)
      (fun z => z=raw (fun _ => blank) g 0 0 hs) (2*xs.length+3) := by
  have hh := WordBankCleanup.clear_hoare (raw (putWord (fun _ => blank) 0 (xs.map bitSymbol)) g 0 0 hs)
    (0 : Fin 11) (by decide) (xs.map bitSymbol) (ReturnOrigin.bits_nonblank xs) rfl
  have he : WordBankCleanup.write (raw (putWord (fun _ => blank) 0 (xs.map bitSymbol)) g 0 0 hs)
      0 (fun _ => blank)=raw (fun _ => blank) g 0 0 hs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  simpa only [he,eraseSource,List.length_map] using hh

def cost (W L N K : ℕ) (hs : Fin 4 → List Bool) :=
  BinaryAddressOffsetRepeatLoop.cost W L N K (hs 0) (hs 1) (hs 2) (hs 3)+K*(N*(L*W))+2*(N*W)+56

theorem runs (blocks : List (List Bool)) (W L K : ℕ) (hu : BlockRotationData.Uniform W blocks)
    (hs : Fin 4 → List Bool) (hw : Counter.value (hs 0)=W) (hl : Counter.value (hs 1)=L)
    (hn : Counter.value (hs 2)=blocks.length) (hk : Counter.value (hs 3)=K) :
    HoareTime program
      (fun z => z=raw (putWord (fun _ => blank) 0 (blocks.flatten.map bitSymbol)) (fun _ => blank) 0 0 hs)
      (fun z => z=raw (fun _ => blank)
        (putWord (fun _ => blank) 0 ((copies (expanded blocks L) K).map bitSymbol)) 0 0 hs)
      (cost W L blocks.length K hs) := by
  let src := putWord (fun _ => (blank : Fin 4)) 0 (blocks.flatten.map bitSymbol)
  let ys := copies (expanded blocks L) K
  have h0 := setup_hoare src (fun _ => blank) 0 0 hs
  have h1 := BinaryAddressOffsetRepeatLoop.runs blocks W L K hu (fun _ => blank) (fun _ => blank) 0 0
    (hs 0) (hs 1) (hs 2) (hs 3) hw hl hn hk rfl
  simp only [zero_add] at h1
  have h2 := clear_clocks src (putWord (fun _ => blank) 0 (ys.map bitSymbol)) 0 (K*(expanded blocks L).length : ℕ) hs
  have h3 := rewinds ys src hs
  have h4 := erases blocks.flatten (putWord (fun _ => blank) 0 (ys.map bitSymbol)) hs
  simp only [ys,copies_length] at h3
  have hh := (((h0.seq h1).seq h2).seq h3).seq h4
  apply hh.consequence (fun _ h => h) (fun _ h => h) _
  simp only [expanded_length blocks W L hu,BlockRotationData.uniform_volume W blocks hu,cost]
  omega

end
end IntegerMultBounds.Machine.BinaryAddressOffsetRepeat
