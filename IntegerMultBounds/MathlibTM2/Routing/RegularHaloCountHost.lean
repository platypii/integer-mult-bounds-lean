module

public import IntegerMultBounds.MathlibTM2.Routing.RegularHaloCountLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTablePacketHost

/-! Compile regular halo count arithmetic to actual binary metadata, restoring
and releasing the existing table workspace through the shared packet host. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.RegularHaloCountHost
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz RegularHaloCountCode RegularHaloCountRow
  RegularHaloCountLayout HaloIntervalLayout RegularHaloLayout
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

theorem countValues_length (L B N : ℕ) : (countValues L B N).length = 2*paddedCount N := by
  have hl (j : ℕ) : (values L B N j).length = 2 := by unfold values; split_ifs <;> rfl
  simp [countValues,List.length_flatMap,hl,Nat.mul_comm]

theorem countValues_fit (L B N V : ℕ) (hfit : L+B < 2^V) :
    ∀ x ∈ countValues L B N, x < 2^V := by
  intro x hx
  obtain ⟨j,_,hx⟩ := List.mem_flatMap.mp hx
  unfold values at hx
  split_ifs at hx <;> simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  all_goals rcases hx with rfl | rfl <;> omega

def generateCounts : Pr P 117 Q A U := tablePacketHost generate

theorem generateCounts_exec {V L H N : ℕ} (st : TblSt 16 A)
    (hN : st.val 0 = N) (hL : st.val 1 = L) (hB : st.val 2 = 2*H)
    (hgap : 2*H ≤ L) (hwide : N+2 < 2^V) (hsize : L+2*H < 2^V)
    (hbound : ∀ i, st.val i < 2^V) (hacc : st.acc = []) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ vf n, vf.user = v.user ∧
      n ≤ (10*paddedCount N+13)*tblC V V+(4*paddedCount N+64)*V+65 ∧
      Exec body generateCounts (mk v S) n
        (mk vf {S with R := fun i => if i.val < 31 then [] else if i = 109 then
          (binSyms V (pairs L H 0 N).length++HaloIntervalLayout.metadata V 0 (pairs L H 0 N)++S.R 109) else S.R i}) := by
  have hc := (generate_do (A := A) (W := V) (w := V) st hN hL hB hgap hwide hsize).mono
    (fun st' he => by simpa only [List.flatMap_cons,hacc,List.append_nil] using he) le_rfl
  obtain ⟨vf,n,hu,hn,he⟩ := tablePacketHost_list_exec (body := body) ((paddedCount N/2)::countValues L (2*H) N) generate st
    hc hbound (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · have hh : paddedCount N < 2^V := by unfold paddedCount; omega
        exact (Nat.div_le_self _ _).trans_lt hh
      · exact countValues_fit L (2*H) N V hsize x hx) hA v S hS
  refine ⟨vf,n,hu,?_,?_⟩
  · rw [List.length_cons,countValues_length] at hn
    nlinarith only [hn]
  · have hclock : paddedCount N/2 = (pairs L H 0 N).length := by
      have hh := pairs_count L H 0 N
      omega
    simpa only [generateCounts,List.flatMap_cons,hclock,←metadata_eq_countValues V L H N hgap,List.append_assoc] using he

end IntegerMultBounds.MathlibTM2.Routing.RegularHaloCountHost
