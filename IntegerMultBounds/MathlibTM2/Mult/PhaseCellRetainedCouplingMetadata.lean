module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryHeaderBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingIntervalMetadata

/-! Generate shared geometry directly from retained master and endpoint headers.
The released native bank and all masters are preserved. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def retainedCouplingAssignments : List (Fin 168 × Fin 168) :=
  [(121,145),(122,146),(124,147),(141,149),(142,151)]

def retainedCouplingValue (s t band a b : ℕ) (k : Fin 168) : ℕ :=
  if k = 121 then s else if k = 122 then t else if k = 124 then band else
  if k = 141 then a else if k = 142 then b else 0

def prepareRetainedCouplingMetadata : Pr P 168 Q A U :=
  binaryHeaderBank 163 0 1 2 retainedCouplingAssignments

def retainedCouplingMetadataR (R : Fin 168 → List (Fin (A+4))) (V s t band a b : ℕ) :=
  binaryHeaderBankR V (retainedCouplingValue s t band a b) R retainedCouplingAssignments

theorem retainedCouplingMetadataR_off (R : Fin 168 → List (Fin (A+4))) (V s t band a b : ℕ)
    (k : Fin 168) (hk : k ∉ [(145 : Fin 168),146,147,149,151]) :
    retainedCouplingMetadataR R V s t band a b k = R k := by
  apply binaryHeaderBankR_off
  intro p hp he
  apply hk
  rw [he]
  simpa [retainedCouplingAssignments] using List.mem_map.mpr ⟨p,hp,rfl⟩

theorem prepareRetainedCouplingMetadata_exec {V s t band a b : ℕ}
    (v : HS 168 Q A U) (S : Stacks 168 A) (hV : (S.R 163).length = V)
    (hs : (S.R 121).length = s) (ht : (S.R 122).length = t)
    (hband : (S.R 124).length = band) (ha : (S.R 141).length = a) (hb : (S.R 142).length = b)
    (hblank : ∀ k ∈ [(0 : Fin 168),1,145,146,147,149,151], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (s+t+band+a+b)*(4*V+10)+20*V+41 ∧
      Exec body prepareRetainedCouplingMetadata (mk v S) n
        (mk v' {S with R := retainedCouplingMetadataR S.R V s t band a b}) ∧
      ∀ origin N k, k ∈ [(145 : Fin 168),146,147,149,151] →
        retainedCouplingMetadataR S.R V s t band a b k =
          binSyms V (couplingIntervalValue s t band a b origin N k) := by
  have hreg : ∀ p ∈ retainedCouplingAssignments, [(p.1 : Fin 168),163,p.2,0,1].Nodup := by
    intro p hp
    simp only [retainedCouplingAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
  have hsource : ∀ p ∈ retainedCouplingAssignments, ∀ q ∈ retainedCouplingAssignments, p.2 ≠ q.1 := by
    intro p hp q hq he
    have hpv : 145 ≤ p.2.val := by
      simp only [retainedCouplingAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
    have hqv : q.1.val ≤ 142 := by
      simp only [retainedCouplingAssignments,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
    have hv := congrArg (fun k : Fin 168 => k.val) he
    omega
  have hvalue : ∀ p ∈ retainedCouplingAssignments,
      (S.R p.1).length = retainedCouplingValue s t band a b p.1 := by
    intro p hp
    simp only [retainedCouplingAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      simpa [retainedCouplingValue] using (by assumption)
  obtain ⟨v',n,hu,hn,he⟩ := binaryHeaderBank_exec (body := body) 163 0 1 2
    retainedCouplingAssignments (by decide) hreg hsource V (retainedCouplingValue s t band a b) v S hV hvalue
    (by intro p hp
        apply hblank
        simp [retainedCouplingAssignments] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp)
    (hblank 0 (by simp)) (hblank 1 (by simp))
  refine ⟨v',n,hu,?_,he,?_⟩
  · have hc : binaryHeaderBankCost V (retainedCouplingValue s t band a b) retainedCouplingAssignments =
        (s+t+band+a+b)*(4*V+10)+20*V+41 := by
      simp [binaryHeaderBankCost,retainedCouplingAssignments,retainedCouplingValue]
      ring
    rw [hc] at hn
    exact hn
  · intro origin N k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      simp [retainedCouplingMetadataR,binaryHeaderBankR,retainedCouplingAssignments,
        retainedCouplingValue,couplingIntervalValue]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
