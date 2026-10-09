import IntegerMultBounds.Machine.CompactRowSplit

/-! Clean whole-row native-alphabet reassembly from the retained row/role/width
words. Every role source and all derived counters are physically erased. -/
namespace IntegerMultBounds.Machine.CompactNativeRowMerge
noncomputable section
variable {a c : ℕ}
open RecursiveInterchangeLayout (volume)
open CompactRowHeaders (descriptor)
open CompactRowSplit hiding program splitProgram

def mergeProgram (ha : 2≤a) (rho : Equiv.Perm (Fin c)) := Placement.placed
  (RecursiveRowsClean.mergeProgram ha rho)
  (CleanSubbank.placement RecursiveRowsRoleBank.ports commonPorts commonPorts_injective)

def program (ha : 2≤a) (rho : Equiv.Perm (Fin c)) :=
  seq (seq (extend (CompactRowHeaders.program (source (c := c))) (LocalTapes c))
    (mergeProgram ha rho))
    (extend (CompactRowHeaders.cleanup (a := a) (t := CallerTapes c)) (LocalTapes c))

theorem merges (rho : Equiv.Perm (Fin c)) (ha : 2 ≤ a) (hc : 0 < c) (r l : ℕ)
    (hr : 0 < r) (hl : 0 < l) (hd : c ∣ r) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CompactRowHeaders.originalValues r c l i)
    (hcan : ∀ i, GrowingCounterData.Canonical (hs i))
    (x : Fin (volume a (descriptor r l)) → Fin (a+4)) :
    HoareTime (program ha rho)
      (fun w => w = bank (RecursiveRowsConstruct.mergePayload rho hd x (fun _ => blank)) hs)
      (fun w => w = bank (RecursiveRowsConstruct.sourcePayload (c := c) x) hs)
      (RecursiveRowsClean.bound c (volume a (descriptor r l))+146*(r+c+l+1)+2) := by
  have hh := CompactRowHeaders.headers r c l hs hv hcan
  have hp : (descriptor r l).Positive := by simp [descriptor,RecursiveInterchangeLayout.Descriptor.Positive,hr,hl]
  have h0 := hoare_extend_eq (CompactRowHeaders.constructs (source (c := c))
    (caller (RecursiveRowsConstruct.mergePayload rho hd x (fun _ => blank)) hs) r c l hs hv hcan
    (by intro i; simp [caller,source,Tapes.append]) (by intro i; simp [caller,source,Tapes.append])) (SharedBank.empty (LocalTapes c) a)
  have h1 : HoareTime (mergeProgram ha rho)
      (fun w => w = CleanSubbank.bank (s := LocalTapes c)
        (prepared (RecursiveRowsConstruct.mergePayload rho hd x (fun _ => blank)) hs))
      (fun w => w = CleanSubbank.bank (s := LocalTapes c)
        (prepared (RecursiveRowsConstruct.sourcePayload (c := c) x) hs))
      (RecursiveRowsClean.bound c (volume a (descriptor r l))) := by
    apply CleanSubbank.realizes _ RecursiveRowsRoleBank.ports commonPorts
      RecursiveRowsRoleBank.ports_injective commonPorts_injective _ _
      (RecursiveRowsClean.bank (CompactRowHeaders.words hs) (RecursiveRowsConstruct.mergePayload rho hd x (fun _ => blank)))
      (RecursiveRowsClean.bank (CompactRowHeaders.words hs) (RecursiveRowsConstruct.sourcePayload (c := c) x)) _
    · rw [RecursiveRowsRoleBank.local_payload,prepared_payload]
    · rw [RecursiveRowsRoleBank.local_payload,prepared_payload]
    · exact RecursiveRowsRoleBank.local_clean _ _
    · exact RecursiveRowsRoleBank.local_clean _ _
    · exact prepared_frame _ _ hs
    · exact RecursiveRowsClean.merge_hoare ha rho hc _ _ hh hp hd x
  have h2 := hoare_extend_eq (CompactRowHeaders.cleans
    (caller (RecursiveRowsConstruct.sourcePayload (c := c) x) hs) r c l hs hv hcan)
    (SharedBank.empty (LocalTapes c) a)
  apply ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h)
  omega

end
end IntegerMultBounds.Machine.CompactNativeRowMerge
