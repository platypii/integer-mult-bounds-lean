import IntegerMultBounds.Machine.RecursiveCallProtocol
import IntegerMultBounds.Machine.RecursiveRowsNode
import IntegerMultBounds.Machine.Shared50NodeSegments
import IntegerMultBounds.Machine.Shared50NodeGates

/-! One permanent bank for calls, node frames and scalar views. Adapters rename
fixed physical tape indices in transition tables; they do not move any data. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveBank
noncomputable section
open Networks
open Shared50ModularControl (prime)
open SharedBankStageInput (raw)
open SharedBankSkeleton (Skeleton)
variable {a b c d q k t u : ℕ}

/-- Blockwise fixed renaming. -/
def join (e : Fin a ≃ Fin b) (f : Fin c ≃ Fin d) : Fin (a+c) ≃ Fin (b+d) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e f).trans finSumFinEquiv)

@[simp] theorem join_left (e : Fin a ≃ Fin b) (f : Fin c ≃ Fin d) (i : Fin a) :
    join e f (Fin.castAdd c i) = Fin.castAdd d (e i) := by simp [join]
@[simp] theorem join_right (e : Fin a ≃ Fin b) (f : Fin c ≃ Fin d) (i : Fin c) :
    join e f (Fin.natAdd a i) = Fin.natAdd b (f i) := by simp [join]

theorem append_reindex (x : Tapes a q) (y : Tapes c q)
    (e : Fin a ≃ Fin b) (f : Fin c ≃ Fin d) :
    (x.append y).reindex (join e f) = (x.reindex e).append (y.reindex f) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
  | left i => simp [Tapes.reindex,Tapes.append,join]
  | right i => simp [Tapes.reindex,Tapes.append,join]

theorem raw_eq_append (x : Tapes k q) (n : ℕ) :
    raw x (k+n) = x.append (SharedBank.empty n q) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
  | left i => simp [i.isLt]
  | right i => simp [SharedBank.empty]

theorem raw_rename (x : Tapes k q) (e : Fin k ≃ Fin t) (n : ℕ) :
    (raw x (k+n)).reindex (join e (Equiv.refl (Fin n))) = raw (x.reindex e) (t+n) := by
  simp only [raw_eq_append,append_reindex]
  rfl

/-- Pad by stationary private tapes, then rename the common prefix. -/
def adapt (s : Skeleton k q) (e : Fin k ≃ Fin t) : Skeleton t q :=
  SharedBankFamily.ofProgram (reindex
    (SharedBankFamily.padProgram s.program (Nat.le_add_left s.tapes k))
    (join e (Equiv.refl (Fin s.tapes))))

theorem adapt_realizes (s : Skeleton k q) (e : Fin k ≃ Fin t)
    (x y : Tapes k q) (B : ℕ)
    (h : HoareTime s.program (fun w => w = raw x s.tapes) (fun w => w = raw y s.tapes) B) :
    HoareTime (adapt s e).program
      (fun w => w = raw (x.reindex e) (adapt s e).tapes)
      (fun w => w = raw (y.reindex e) (adapt s e).tapes) B := by
  have hp := SharedBankFamily.pad_realizes (Nat.le_add_left s.tapes k)
    (SharedBankFamily.common_le s) x y B h
  have hr := hoare_reindex_eq hp (join e (Equiv.refl (Fin s.tapes)))
  simp only [raw_rename] at hr
  exact hr

abbrev AuxCount (u : ℕ) := (3+(1+(1+u)))+2
abbrev Count (t u : ℕ) := RecursiveCallBank.TapeCount t (1+(1+u))

def auxiliary (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (aux : Tapes u prime) (st : Tapes 2 prime) : Tapes (AuxCount u) prime :=
  ((RecursiveCallBank.work f p).append (node.append (scalar.append aux))).append st

def bank (roles : Tapes t prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (aux : Tapes u prime) (st : Tapes 2 prime) : Tapes (Count t u) prime :=
  RecursiveCallBank.bank roles hs f p (node.append (scalar.append aux)) st

/-- Clock, count, payload stack, node-view stack, scalar-view stack occupy
five distinct auxiliary slots; descriptor and PC stacks follow the spectators. -/
def nodeSlot : Fin (AuxCount u) := Fin.castAdd 2 (Fin.natAdd 3 (Fin.castAdd (1+u) 0))
def scalarSlot : Fin (AuxCount u) := Fin.castAdd 2 (Fin.natAdd 3 (Fin.natAdd 1 (Fin.castAdd u 0)))

def front (i : Fin (AuxCount u)) : Fin (1+(AuxCount u-1)) ≃ Fin (AuxCount u) :=
  (finCongr (by unfold AuxCount; omega)).trans (Equiv.swap 0 i)

@[simp] theorem front_zero (i : Fin (AuxCount u)) : front i 0 = i := by
  simp [front]

def rest (i : Fin (AuxCount u)) (v : Tapes (AuxCount u) prime) : Tapes (AuxCount u-1) prime :=
  ⟨fun j => v.head (front i (Fin.natAdd 1 j)),fun j => v.tape (front i (Fin.natAdd 1 j))⟩

def one (i : Fin (AuxCount u)) (v : Tapes (AuxCount u) prime) : Tapes 1 prime :=
  ⟨fun _ => v.head i,fun _ => v.tape i⟩

theorem front_exact (i : Fin (AuxCount u)) (v : Tapes (AuxCount u) prime) :
    ((one i v).append (rest i v)).reindex (front i) = v := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals
    obtain ⟨j,rfl⟩ := (front i).surjective j
    simp only [Equiv.symm_apply_apply]
    induction j using Fin.addCases with
    | left j =>
      fin_cases j
      have hz (z : Fin 1) : Fin.castAdd (AuxCount u-1) z = (0 : Fin (1+(AuxCount u-1))) := by
        apply Fin.ext
        have := z.isLt
        simp only [Fin.val_castAdd,Fin.val_zero]
        omega
      simp only [hz,front_zero,Tapes.append,one]
      rfl
    | right j => simp [Tapes.append,rest]

/-- Rows use the node-view stack; scalar segments use the separate blank view. -/
def commonRename (i : Fin (AuxCount u)) :
    Fin (RecursiveViewFrameRoleBank.count t (AuxCount u-1)) ≃ Fin (Count t u) :=
  join (Equiv.refl _) (join (Equiv.refl (Fin 7)) (front i))

theorem common_exact (i : Fin (AuxCount u)) (roles : Tapes t prime) (hs : Fin 6 → List Bool)
    (v : Tapes (AuxCount u) prime) :
    (RecursiveViewFrameRoleBank.bank roles hs (one i v) (rest i v)).reindex (commonRename i) =
      RecursiveShiftRoleBank.common roles hs v := by
  simp only [RecursiveViewFrameRoleBank.bank,RecursiveShiftRoleBank.common,
    commonRename,append_reindex,front_exact]
  rfl


@[simp] theorem one_node (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (aux : Tapes u prime) (st : Tapes 2 prime) :
    one nodeSlot (auxiliary f p node scalar aux st) = node := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals
    simp only [auxiliary,nodeSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right]
    rfl

@[simp] theorem one_scalar (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (aux : Tapes u prime) (st : Tapes 2 prime) :
    one scalarSlot (auxiliary f p node scalar aux st) = scalar := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals
    simp only [auxiliary,scalarSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right]
    rfl

theorem rest_congr (i : Fin (AuxCount u)) (v w : Tapes (AuxCount u) prime)
    (h : ∀ j, j ≠ i → v.head j = w.head j ∧ v.tape j = w.tape j) : rest i v = rest i w := by
  have hn (j : Fin (AuxCount u-1)) : front i (Fin.natAdd 1 j) ≠ i := by
    intro he
    rw [← front_zero i] at he
    have he' := (front i).injective he
    have hv := congrArg Fin.val he'
    simp only [Fin.val_natAdd,Fin.val_zero] at hv
    omega
  apply congrArg₂ Tapes.mk
  · funext j; exact (h _ (hn j)).1
  · funext j; exact (h _ (hn j)).2

theorem rest_node (f : ℤ → Fin (prime+4)) (p : ℤ) (node node' scalar : Tapes 1 prime)
    (aux : Tapes u prime) (st : Tapes 2 prime) :
    rest nodeSlot (auxiliary f p node scalar aux st) = rest nodeSlot (auxiliary f p node' scalar aux st) := by
  apply rest_congr
  intro j hj
  induction j using Fin.addCases with
  | right j => simp only [auxiliary,Tapes.append,Fin.addCases_right]; trivial
  | left j =>
    induction j using Fin.addCases with
    | left j => simp only [auxiliary,Tapes.append,Fin.addCases_left]; trivial
    | right j =>
      induction j using Fin.addCases with
      | right j => simp only [auxiliary,Tapes.append,Fin.addCases_left,Fin.addCases_right]; trivial
      | left j => fin_cases j; exact False.elim (hj rfl)

theorem node_endpoint (roles : Tapes t prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (aux : Tapes u prime) (st : Tapes 2 prime) :
    (RecursiveViewFrameRoleBank.bank roles hs node
      (rest nodeSlot (auxiliary f p node scalar aux st))).reindex (commonRename nodeSlot) =
      bank roles hs f p node scalar aux st := by
  have h := common_exact nodeSlot roles hs (auxiliary f p node scalar aux st)
  rw [one_node] at h
  exact h

theorem scalar_endpoint (roles : Tapes t prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (aux : Tapes u prime) (st : Tapes 2 prime) :
    (RecursiveViewFrameRoleBank.bank roles hs scalar
      (rest scalarSlot (auxiliary f p node scalar aux st))).reindex (commonRename scalarSlot) =
      bank roles hs f p node scalar aux st := by
  have h := common_exact scalarSlot roles hs (auxiliary f p node scalar aux st)
  rw [one_scalar] at h
  exact h


/-- The descriptor and PC stacks are the final two permanent tapes. -/
def returnSlot (i : Fin 2) : Fin (Count t u) :=
  Fin.natAdd t (Fin.natAdd 7 (Fin.natAdd (3+(1+(1+u))) i))

/-- Clock, count, payload, node-view, scalar-view, descriptor, PC, in that order. -/
def auxiliarySlot (i : Fin 7) : Fin (AuxCount u) :=
  ⟨if i.val < 5 then i.val else u+i.val,by have := i.isLt; unfold AuxCount; split_ifs <;> omega⟩

def slot (i : Fin 7) : Fin (Count t u) :=
  Fin.natAdd t (Fin.natAdd 7 (auxiliarySlot i))

theorem auxiliarySlot_injective : Function.Injective (auxiliarySlot (u := u)) := by
  intro i j h
  have he := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  simp only [auxiliarySlot] at he
  apply Fin.ext
  split_ifs at he <;> omega

theorem slot_injective : Function.Injective (slot (t := t) (u := u)) :=
by
  intro i j h
  apply auxiliarySlot_injective
  apply Fin.ext
  have he := congrArg Fin.val h
  simp only [slot,Fin.val_natAdd] at he
  omega

theorem slot_control (i : Fin 3) :
    slot (t := t) (u := u) (Fin.castAdd 4 i) = RecursiveCallBank.controlSlot (u := 1+(1+u)) i := by
  apply Fin.ext
  have hi := i.isLt
  simp only [slot,auxiliarySlot,Fin.val_castAdd,Fin.val_natAdd,RecursiveCallBank.controlSlot]
  split_ifs <;> omega

theorem slot_return (i : Fin 2) : slot (t := t) (u := u) (Fin.natAdd 5 i) = returnSlot i := by
  apply Fin.ext
  simp only [slot,auxiliarySlot,returnSlot,Fin.val_natAdd]
  split_ifs <;> omega

theorem returnSlot_pc :
    Fin.castAdd 40 (returnSlot (t := t) (u := u) 1) =
      RecursiveChildReturnRoleBank.pcSlot (t := t) (u := 3+(1+(1+u))) := rfl

end
end IntegerMultBounds.Machine.Shared50RecursiveBank
