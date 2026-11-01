module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryHeaderBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompleteCouplingIntervalMetadata

/-! Generate shared interval geometry from ordinary coupling headers. The local
length is computed from the endpoints; every native tape is restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def couplingGeometryAssignments : List (Fin 168 × Fin 168) :=
  [(97,145),(98,146),(100,147),(101,149),(103,151),(101,155),(103,157)]

def couplingGeometryHeaderValue (s t band a b : ℕ) (k : Fin 168) :=
  if k = 97 then s else if k = 98 then t else if k = 100 then band else
  if k = 101 then a else if k = 103 then b else 0

def generateCouplingGeometry : Pr P 168 Q A U :=
  .seq (binaryHeaderBank 163 0 1 2 couplingGeometryAssignments)
    (.seq (bsub 157 155 165 0 1 2 4)
      (.seq (uclear 157) completeCouplingIntervalMetadata))

def generateCouplingGeometryCost (V s t band a b : ℕ) :=
  (s+t+band+2*a+2*b)*(4*V+10)+74*V+103

theorem generateCouplingGeometry_exec (V s t band a b : ℕ) (hab : a ≤ b)
    (hbV : b < 2^V) (hfitV : a+((b-a)+2*band)+s < 2^V)
    (v : HS 168 Q A U) (S : Stacks 168 A) (hV : (S.R 163).length = V)
    (hheaders : ∀ p ∈ couplingGeometryAssignments,
      (S.R p.1).length = couplingGeometryHeaderValue s t band a b p.1)
    (hblank : ∀ k ∈ ([(0 : Fin 168),1,2,3,145,146,147,148,149,151,154,155,156,157,164,165]), S.R k = []) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ generateCouplingGeometryCost V s t band a b ∧
      Exec body generateCouplingGeometry (mk v S) n (mk v' F) ∧
      CouplingIntervalMetadata V s t band a b a (b-a) F ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, k ∉ ([(145 : Fin 168),146,147,148,149,151,154,155,156,164,165]) → F.R k = S.R k) := by
  let value := couplingGeometryHeaderValue s t band a b
  let B : Stacks 168 A := {S with R := binaryHeaderBankR V value S.R couplingGeometryAssignments}
  have hoff (k : Fin 168) (hk : k ∉ ([(145 : Fin 168),146,147,149,151,155,157])) : B.R k = S.R k := by
    apply binaryHeaderBankR_off
    intro p hp he
    apply hk
    rw [he]
    simpa [couplingGeometryAssignments] using List.mem_map.mpr ⟨p,hp,rfl⟩
  have hat (p : Fin 168 × Fin 168) (hp : p ∈ couplingGeometryAssignments) :
      B.R p.2 = binSyms V (value p.1) :=
    binaryHeaderBankR_at V value S.R couplingGeometryAssignments (by decide) p hp
  have hreg : ∀ p ∈ couplingGeometryAssignments, [p.1,(163 : Fin 168),p.2,0,1].Nodup := by
    intro p hp
    simp only [couplingGeometryAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hsource : ∀ p ∈ couplingGeometryAssignments, ∀ q ∈ couplingGeometryAssignments, p.2 ≠ q.1 := by
    intro p hp q hq he
    have hpv : 145 ≤ p.2.val := by
      simp only [couplingGeometryAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hqv : q.1.val ≤ 103 := by
      simp only [couplingGeometryAssignments,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hv := congrArg Fin.val he
    omega
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := binaryHeaderBank_exec (body := body) 163 0 1 2
    couplingGeometryAssignments (by decide) hreg hsource V value v S hV hheaders
    (by intro p hp; apply hblank; simp [couplingGeometryAssignments] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    (hblank 0 (by simp)) (hblank 1 (by simp))
  have h155 : B.R 155 = binSyms V a := by simpa [value,couplingGeometryHeaderValue] using hat (101,155) (by simp [couplingGeometryAssignments])
  have h157 : B.R 157 = binSyms V b := by simpa [value,couplingGeometryHeaderValue] using hat (103,157) (by simp [couplingGeometryAssignments])
  obtain ⟨v₂,hu₂,_,_,he₂⟩ := bsub_exec (body := body) (a := 157) (b := 155) (c := 165)
    (tx := 0) (ty := 1) (tz := 2) (cy := 4) (by decide) (by decide) (by decide)
    hbV (hab.trans_lt hbV) v₁ B h157 h155
    (by rw [hoff 0 (by decide)]; exact hblank 0 (by simp))
    (by rw [hoff 1 (by decide)]; exact hblank 1 (by simp))
    (by rw [hoff 2 (by decide)]; exact hblank 2 (by simp))
  let C : Stacks 168 A := {B with R := Function.update B.R 165 (binSyms V (b-a))}
  have hmod : (b+2^V-a)%2^V = b-a := by
    have heq : b+2^V-a = (b-a)+2^V := by omega
    rw [heq,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega : b-a < 2^V)]
  have he₂' : Exec body (bsub 157 155 165 0 1 2 4) (mk v₁ B) (8*V+8) (mk v₂ C) := by
    simpa [C,hmod,hoff 165 (by decide),hblank 165 (by simp)] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 157 v₂ C
  let D : Stacks 168 A := {C with R := Function.update C.R 157 []}
  have hlen : (C.R 157).length = V := by simp [C,h157,binSyms]
  have he₃' : Exec body (uclear 157) (mk v₂ C) (2*V+2) (mk v₃ D) := by simpa only [hlen] using he₃
  have hd (k : Fin 168) (h165 : k ≠ 165) (h157 : k ≠ 157) : D.R k = B.R k := by simp [D,C,h165,h157]
  obtain ⟨v₄,hu₄,he₄,hmeta⟩ := completeCouplingIntervalMetadata_exec (body := body) hfitV v₃ D
    (by rw [hd 163 (by decide) (by decide),hoff 163 (by decide)]; exact hV)
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hd 145 (by decide) (by decide)]
          simpa [value,couplingGeometryHeaderValue,couplingIntervalValue] using hat (97,145) (by simp [couplingGeometryAssignments])
        · rw [hd 146 (by decide) (by decide)]
          simpa [value,couplingGeometryHeaderValue,couplingIntervalValue] using hat (98,146) (by simp [couplingGeometryAssignments])
        · rw [hd 147 (by decide) (by decide)]
          simpa [value,couplingGeometryHeaderValue,couplingIntervalValue] using hat (100,147) (by simp [couplingGeometryAssignments])
        · rw [hd 149 (by decide) (by decide)]
          simpa [value,couplingGeometryHeaderValue,couplingIntervalValue] using hat (101,149) (by simp [couplingGeometryAssignments])
        · rw [hd 151 (by decide) (by decide)]
          simpa [value,couplingGeometryHeaderValue,couplingIntervalValue] using hat (103,151) (by simp [couplingGeometryAssignments])
        · rw [hd 155 (by decide) (by decide)]
          simpa [value,couplingGeometryHeaderValue,couplingIntervalValue] using hat (101,155) (by simp [couplingGeometryAssignments])
        · simp [D,C,couplingIntervalValue])
    (by intro k hk
        have hn : k ≠ 165 ∧ k ≠ 157 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        rw [hd k hn.1 hn.2,hoff k (by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
        apply hblank
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  refine ⟨v₄,_,n₁+((8*V+8)+((2*V+2)+(36*V+36))),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    .seq he₁ (.seq he₂' (.seq he₃' he₄)),hmeta,rfl,rfl,rfl,?_⟩
  · have hc : binaryHeaderBankCost V value couplingGeometryAssignments =
        (s+t+band+2*a+2*b)*(4*V+10)+28*V+57 := by
      simp [binaryHeaderBankCost,value,couplingGeometryHeaderValue,couplingGeometryAssignments]
      ring
    rw [hc] at hn₁
    unfold generateCouplingGeometryCost
    omega
  · intro k hk
    have hn : k ≠ 154 ∧ k ≠ 148 ∧ k ≠ 156 ∧ k ≠ 164 ∧ k ≠ 165 := by
      exact ⟨(fun he => hk (by simp [he])),(fun he => hk (by simp [he])),
        (fun he => hk (by simp [he])),(fun he => hk (by simp [he])),(fun he => hk (by simp [he]))⟩
    simp only [completedCouplingIntervalR,Function.update_of_ne hn.1,
      Function.update_of_ne hn.2.1,Function.update_of_ne hn.2.2.1,Function.update_of_ne hn.2.2.2.1]
    by_cases h157 : k = 157
    · subst k; simp [D,hblank 157 (by simp)]
    · rw [hd k hn.2.2.2.2 h157]
      apply hoff
      intro hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | he
      · exact hk (by simp)
      · exact hk (by simp)
      · exact hk (by simp)
      · exact hk (by simp)
      · exact hk (by simp)
      · exact hk (by simp)
      · exact h157 he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
