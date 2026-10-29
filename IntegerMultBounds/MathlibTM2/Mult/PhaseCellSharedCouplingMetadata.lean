module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryHeaderBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingIntervalMetadata

/-! Generate shared geometry once outside the local interval traversal. Dynamic
origin and row count remain descriptor fields, avoiding repeated unary origins. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def sharedCouplingAssignments : List (Fin 168 × Fin 168) :=
  [(97,145),(98,146),(100,147),(101,149),(103,151)]

def sharedCouplingValue (s t band a b : ℕ) (k : Fin 168) : ℕ :=
  if k = 97 then s else if k = 98 then t else if k = 100 then band else
  if k = 101 then a else if k = 103 then b else 0

def prepareSharedCouplingMetadata : Pr P 168 Q A U :=
  binaryHeaderBank 163 0 1 2 sharedCouplingAssignments

def sharedCouplingMetadataR (R : Fin 168 → List (Fin (A+4))) (V s t band a b : ℕ) :=
  binaryHeaderBankR V (sharedCouplingValue s t band a b) R sharedCouplingAssignments

theorem sharedCouplingMetadataR_off (R : Fin 168 → List (Fin (A+4))) (V s t band a b : ℕ)
    (k : Fin 168) (hk : k ∉ [(145 : Fin 168),146,147,149,151]) :
    sharedCouplingMetadataR R V s t band a b k = R k := by
  apply binaryHeaderBankR_off
  intro p hp he
  apply hk
  rw [he]
  simpa [sharedCouplingAssignments] using List.mem_map.mpr ⟨p,hp,rfl⟩

theorem prepareSharedCouplingMetadata_exec {V s t band a b : ℕ}
    (v : HS 168 Q A U) (S : Stacks 168 A) (hV : (S.R 163).length = V)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hband : (S.R 100).length = band) (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (hblank : ∀ k ∈ [(0 : Fin 168),1,145,146,147,149,151], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (s+t+band+a+b)*(4*V+10)+20*V+41 ∧
      Exec body prepareSharedCouplingMetadata (mk v S) n
        (mk v' {S with R := sharedCouplingMetadataR S.R V s t band a b}) ∧
      ∀ origin N k, k ∈ [(145 : Fin 168),146,147,149,151] →
        sharedCouplingMetadataR S.R V s t band a b k =
          binSyms V (couplingIntervalValue s t band a b origin N k) := by
  have hreg : ∀ p ∈ sharedCouplingAssignments, [(p.1 : Fin 168),163,p.2,0,1].Nodup := by
    intro p hp
    simp only [sharedCouplingAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
  have hsource : ∀ p ∈ sharedCouplingAssignments, ∀ q ∈ sharedCouplingAssignments, p.2 ≠ q.1 := by
    intro p hp q hq he
    have hpv : 145 ≤ p.2.val := by
      simp only [sharedCouplingAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
    have hqv : q.1.val ≤ 103 := by
      simp only [sharedCouplingAssignments,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
    have hv := congrArg (fun k : Fin 168 => k.val) he
    omega
  have hvalue : ∀ p ∈ sharedCouplingAssignments,
      (S.R p.1).length = sharedCouplingValue s t band a b p.1 := by
    intro p hp
    simp only [sharedCouplingAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      simpa [sharedCouplingValue] using (by assumption)
  obtain ⟨v',n,hu,hn,he⟩ := binaryHeaderBank_exec (body := body) 163 0 1 2
    sharedCouplingAssignments (by decide) hreg hsource V (sharedCouplingValue s t band a b) v S hV hvalue
    (by intro p hp
        apply hblank
        simp [sharedCouplingAssignments] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp)
    (hblank 0 (by simp)) (hblank 1 (by simp))
  refine ⟨v',n,hu,?_,he,?_⟩
  · have hc : binaryHeaderBankCost V (sharedCouplingValue s t band a b) sharedCouplingAssignments =
        (s+t+band+a+b)*(4*V+10)+20*V+41 := by
      simp [binaryHeaderBankCost,sharedCouplingAssignments,sharedCouplingValue]
      ring
    rw [hc] at hn
    exact hn
  · intro origin N k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      simp [sharedCouplingMetadataR,binaryHeaderBankR,sharedCouplingAssignments,
        sharedCouplingValue,couplingIntervalValue]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
