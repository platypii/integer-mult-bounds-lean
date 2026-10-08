import IntegerMultBounds.Machine.RecursiveRowsResetCount
import IntegerMultBounds.Machine.CountedBankResetHeader

/-! Destructive recursive cyclic transfers. After copying, the common source
is physically erased and reset; after merging, all role sources are physically
erased and reset. Derived erase lengths are produced by actual products. -/
namespace IntegerMultBounds.Machine.RecursiveRowsMove
open RecursiveInterchangeLayout (Descriptor volume role)
open RecursiveRowsResetCount (Target)
open RecursiveRowsInstall (LocalTapes TotalTapes)
variable {q c : ℕ} (hq : 2 ≤ q)
noncomputable section

abbrev TapeCount (c : ℕ) := TotalTapes c+2

def payloadMask (target : Target) : Fin (1+c) → Bool :=
  Fin.addCases (fun _ => match target with | .common => true | .roles => false)
    (fun _ => match target with | .common => false | .roles => true)

def selected (target : Target) : Fin (TotalTapes c) → Bool :=
  Fin.addCases (fun _ => false)
    (Fin.addCases (Fin.addCases (payloadMask target) (fun _ => false)) (fun _ => false))

def counted (target : Target) (hs : Fin 6 → List Bool) (v : Descriptor) (rs : List Bool)
    (payload : Tapes (1+c) q) :=
  (RecursiveRowsResetCount.output hq c hs v rs target).append
    (RecursiveRowsInstall.prepared payload (RecursiveRowsDimensions.words (q := q) c v))

def output (target : Target) (hs : Fin 6 → List Bool) (v : Descriptor) (rs : List Bool)
    (payload : Tapes (1+c) q) := CountedBankReset.bank (counted hq target hs v rs payload)
      (RecursiveRowsResetCount.bits (q := q) c v target)

def input (hs : Fin 6 → List Bool) (payload : Tapes (1+c) q) :=
  (RecursiveRowsConstruct.input hs payload).append (SharedBank.empty 2 q)

def resetProgram (target : Target) := seq
  (extend (extend (RecursiveRowsResetCount.program (q := q) target) (LocalTapes c)) 2)
  (CountedBankResetHeader.program (a := q) (by unfold TotalTapes; omega : 0 < TotalTapes c)
    (selected target) (Fin.castAdd (LocalTapes c) (20 : Fin 38)))

private theorem restored_counted (target : Target) (dim : Tapes 38 q) (payload : Tapes (1+c) q)
    (ws : Fin 2 → List Bool) (n : ℕ) :
    CountedBankReset.restored (selected target) (dim.append (RecursiveRowsInstall.prepared payload ws)) n =
      dim.append (RecursiveRowsInstall.prepared (CountedBankReset.restored (payloadMask target) payload n) ws) := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    induction i using Fin.addCases with
    | left i => simp [CountedBankReset.restored,CountedBankReset.after,selected,Tapes.append]
    | right i =>
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i => simp [CountedBankReset.restored,CountedBankReset.after,selected,RecursiveRowsInstall.prepared,
            CountedLoopReuseAlphabet.bank,Tapes.append]
        | right i => simp [CountedBankReset.restored,CountedBankReset.after,selected,RecursiveRowsInstall.prepared,
            CountedLoopReuseAlphabet.bank,Tapes.append]
      | right i => simp [CountedBankReset.restored,CountedBankReset.after,selected,RecursiveRowsInstall.prepared,
          CountedLoopReuseAlphabet.bank,Tapes.append]

theorem resets_hoare (target : Target) (hs : Fin 6 → List Bool) (v : Descriptor) (rs : List Bool)
    (hp : v.Positive) (payload : Tapes (1+c) q) :
    HoareTime (resetProgram (q := q) (c := c) target)
      (fun w => w = (RecursiveRowsConstruct.prepared hq hs v rs payload).append (SharedBank.empty 2 q))
      (fun w => w = output hq target hs v rs
        (CountedBankReset.restored (payloadMask target) payload (RecursiveRowsResetCount.count (q := q) c v target)))
      (83*volume q v+86) := by
  have hprod := hoare_extend_eq (hoare_extend_eq
    (RecursiveRowsResetCount.constructs_hoare hq c hs v rs hp target)
    (RecursiveRowsInstall.prepared payload (RecursiveRowsDimensions.words (q := q) c v))) (SharedBank.empty 2 q)
  have hreset := CountedBankResetHeader.resets_hoare
    (by unfold TotalTapes; omega : 0 < TotalTapes c) (selected target)
    (Fin.castAdd (LocalTapes c) (20 : Fin 38)) (counted hq target hs v rs payload)
    (RecursiveRowsResetCount.bits (q := q) c v target) (RecursiveRowsResetCount.count (q := q) c v target)
    (by simpa only [counted,Tapes.append,Fin.addCases_left] using RecursiveRowsResetCount.ready hq c hs v rs target)
    (RecursiveRowsResetCount.bits_value c v target) (DimensionProductDescriptor.bits_canonical _ _)
  have hh := hprod.seq hreset
  have hn := RecursiveRowsResetCount.count_le (q := q) c v target
  apply hh.consequence (fun _ h => h) _ (by omega)
  intro w hw
  simpa only [counted,restored_counted,output] using hw

def splitProgram := seq (extend (RecursiveRowsConstruct.splitProgram hq c) 2) (resetProgram .common)
def mergeProgram (rho : Equiv.Perm (Fin c)) :=
  seq (extend (RecursiveRowsConstruct.mergeProgram hq rho) 2) (resetProgram .roles)

def bound (c V : ℕ) := RecursiveRowsConstruct.bound c V+83*V+87

def rolePayload {v : Descriptor} (hd : c ∣ v.rows) (x : Fin (volume q v) → Fin (q+4)) : Tapes (1+c) q :=
  CyclicRowCopy.payload (fun _ => blank)
    (fun j => RecursiveRowsConstruct.word (RecursiveInterchangeRows.roleArray q c v hd x j)) 0 (fun _ => 0)

private theorem reset_split {v : Descriptor} (hd : c ∣ v.rows) (x : Fin (volume q v) → Fin (q+4)) :
    CountedBankReset.restored (payloadMask .common) (RecursiveRowsConstruct.splitPayload hd x) (volume q v) =
      rolePayload hd x := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    induction i using Fin.addCases with
    | left i =>
      fin_cases i
      simp only [CountedBankReset.restored,CountedBankReset.after,payloadMask,Fin.addCases_left,
        RecursiveRowsConstruct.splitPayload,rolePayload,CyclicRowCopy.payload,Tapes.append,ite_true]
      simpa only [List.length_ofFn] using (show CountedBankReset.erased (RecursiveRowsConstruct.word x) 0 (List.ofFn x).length =
        fun _ => blank from CountedBankReset.erased_word _ _)
    | right i => simp [CountedBankReset.restored,CountedBankReset.after,payloadMask,
        RecursiveRowsConstruct.splitPayload,rolePayload,CyclicRowCopy.payload,Tapes.append]

private theorem reset_merge {v : Descriptor} (rho : Equiv.Perm (Fin c)) (hd : c ∣ v.rows)
    (x : Fin (volume q v) → Fin (q+4)) :
    CountedBankReset.restored (payloadMask .roles) (RecursiveRowsConstruct.mergePayload rho hd x (RecursiveRowsConstruct.word x))
      (volume q (role v c)) = RecursiveRowsConstruct.sourcePayload (c := c) x := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    induction i using Fin.addCases with
    | left i => simp [CountedBankReset.restored,CountedBankReset.after,payloadMask,
        RecursiveRowsConstruct.mergePayload,RecursiveRowsConstruct.sourcePayload,CyclicRowCopy.payload,Tapes.append]
    | right i =>
      simp only [CountedBankReset.restored,CountedBankReset.after,payloadMask,Fin.addCases_right,
        RecursiveRowsConstruct.mergePayload,RecursiveRowsConstruct.sourcePayload,CyclicRowCopy.payload,Tapes.append,ite_true]
      simpa only [List.length_ofFn] using (show CountedBankReset.erased
        (RecursiveRowsConstruct.word (RecursiveInterchangeRows.roleArray q c v hd x (rho.symm i))) 0
        (List.ofFn (RecursiveInterchangeRows.roleArray q c v hd x (rho.symm i))).length = fun _ => blank from
        CountedBankReset.erased_word _ _)

theorem split_hoare (hc : 0 < c) (hs : Fin 6 → List Bool) (v : Descriptor)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (hd : c ∣ v.rows)
    (x : Fin (volume q v) → Fin (q+4)) :
    ∃ rs : List Bool, HoareTime (splitProgram hq (c := c))
      (fun w => w = input hs (RecursiveRowsConstruct.sourcePayload (c := c) x))
      (fun w => w = output hq .common hs v rs (rolePayload hd x)) (bound c (volume q v)) := by
  obtain ⟨rs,_,_,hsplit⟩ := RecursiveRowsConstruct.split_hoare hq hc hs v hv hp hd x
  have hh := (hoare_extend_eq hsplit (SharedBank.empty 2 q)).seq
    (resets_hoare hq .common hs v rs hp (RecursiveRowsConstruct.splitPayload hd x))
  refine ⟨rs,hh.consequence (fun _ h => h) ?_ (by unfold bound; omega)⟩
  intro w hw
  simpa only [RecursiveRowsResetCount.count,reset_split] using hw

theorem merge_hoare (rho : Equiv.Perm (Fin c)) (hc : 0 < c) (hs : Fin 6 → List Bool) (v : Descriptor)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (hd : c ∣ v.rows)
    (x : Fin (volume q v) → Fin (q+4)) :
    ∃ rs : List Bool, HoareTime (mergeProgram hq rho)
      (fun w => w = input hs (RecursiveRowsConstruct.mergePayload rho hd x (fun _ => blank)))
      (fun w => w = output hq .roles hs v rs (RecursiveRowsConstruct.sourcePayload (c := c) x)) (bound c (volume q v)) := by
  obtain ⟨rs,_,_,hmerge⟩ := RecursiveRowsConstruct.merge_hoare hq rho hc hs v hv hp hd x
  have hh := (hoare_extend_eq hmerge (SharedBank.empty 2 q)).seq
    (resets_hoare hq .roles hs v rs hp (RecursiveRowsConstruct.mergePayload rho hd x (RecursiveRowsConstruct.word x)))
  refine ⟨rs,hh.consequence (fun _ h => h) ?_ (by unfold bound; omega)⟩
  intro w hw
  simpa only [RecursiveRowsResetCount.count,reset_merge] using hw

end
end IntegerMultBounds.Machine.RecursiveRowsMove
