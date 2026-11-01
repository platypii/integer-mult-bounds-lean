module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedHeaderCopies
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseCellRuntime
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingReady

/-! Coupling's ordinary headers are reloaded from retained gather masters into
the released numerical bank. Every other native tape keeps its released value. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

def replicaCouplingHeaderCopies : List (Fin 126 × Fin 117) :=
  [(114,114),(112,112),(99,99),(97,97),(98,98),(100,100),(111,101),(113,103),(94,94)]

def replicaCouplingMasterValue (P q w s t u band a b : ℕ) (k : Fin 126) : ℕ :=
  if k = 114 then P else if k = 112 then q else if k = 99 then u else
  if k = 97 then s else if k = 98 then t else if k = 100 then band else
  if k = 111 then a else if k = 113 then b else if k = 94 then w else 0

def replicaCouplingUnaryBank (A P q w s t u band a b : ℕ)
    (borrowed output : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A :=
  let S := releasedCellBank [] borrowed output inp out
  {S with R := unaryCopiesR (replicaCouplingMasterValue P q w s t u band a b) S.R replicaCouplingHeaderCopies}

def replicaCouplingHeaderCost (P q w s t u band a b : ℕ) :=
  4*(P+q+s+t+u+band+a+b+w)+37

theorem replicaCouplingHeaderCopies_cost (P q w s t u band a b : ℕ) :
    (replicaCouplingHeaderCopies.map (fun r => 4*replicaCouplingMasterValue P q w s t u band a b r.1+4)).sum+1 =
      replicaCouplingHeaderCost P q w s t u band a b := by
  simp [replicaCouplingHeaderCopies,replicaCouplingMasterValue,replicaCouplingHeaderCost]
  ring

private theorem replicaCouplingUnaryBank_off (A P q w s t u band a b : ℕ)
    (borrowed output : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) (k : Fin 117)
    (hk : k ∉ ([93,94,97,98,99,100,101,103,110,112,114] : List (Fin 117))) :
    (replicaCouplingUnaryBank A P q w s t u band a b borrowed output inp out).R k = [] := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
  rcases hk with ⟨h93,h94,h97,h98,h99,h100,h101,h103,h110,h112,h114⟩
  have hv93 : k.val ≠ 93 := fun he => h93 (Fin.ext he)
  have hv110 : k.val ≠ 110 := fun he => h110 (Fin.ext he)
  simp [replicaCouplingUnaryBank,replicaCouplingHeaderCopies,unaryCopiesR,releasedCellBank,
    h94,h97,h98,h99,h100,h101,h103,h112,h114,hv93,hv110]

theorem replicaCouplingUnaryBank_ready (A P q w s t u band a b : ℕ)
    (borrowed output : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    CouplingReady P q w s t u band a b borrowed
      (replicaCouplingUnaryBank A P q w s t u band a b borrowed output inp out) := by
  have hoff := replicaCouplingUnaryBank_off A P q w s t u band a b borrowed output inp out
  constructor
  all_goals first
    | (simp [replicaCouplingUnaryBank,replicaCouplingHeaderCopies,replicaCouplingMasterValue,
        unaryCopiesR,releasedCellBank]; done)
    | skip
  · intro i
    refine ⟨rfl,hoff _ ?_⟩
    have hi := i.isLt
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or,Fin.ext_iff,mul]
    omega
  · intro r
    apply hoff
    have hr := cr_range r
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or,Fin.ext_iff]
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
