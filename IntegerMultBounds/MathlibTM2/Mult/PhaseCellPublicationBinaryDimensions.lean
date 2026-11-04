module

public import IntegerMultBounds.MathlibTM2.Host.Embed
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedHeaderList
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! Generate the three binary transpose dimensions from the existing unary
masters and packet counter. One restored scratch set serves all three words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PublicationBinaryDimensions
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T T' Q A : ℕ} {P U : Type}

def assignments : List (Fin 117 × Fin 117) := [(61,82),(62,83),(52,84)]

def copies (e : Fin 117 → Fin T) : List (Fin T × Fin T) :=
  assignments.map fun r => (e r.1,e r.2)

def program (e : Fin 117 → Fin T) : Pr P T Q A U :=
  paddedHeaderList (e 35) (e 55) (e 56) (e 57) (e 58) (e 65) (e 66) (copies e)

def timeCost (a b packet V : ℕ) := 21*(a+b+packet)+36*V+85

def loaded (e : Fin 117 → Fin T) (a b packet V : ℕ) (S : Stacks T A) :=
  {S with R := (Function.update (Function.update (Function.update S.R
    (e 82) (binSyms V a)) (e 83) (binSyms V b)) (e 84) (binSyms V packet))}

theorem fits_of_rectangle (a b packet V : ℕ) (hbits : a+b < V)
    (hfit : packet*2^(a+b) < 2^V) : a < 2^V ∧ b < 2^V ∧ packet < 2^V := by
  have ha : a < 2^V := (show a < V by omega).trans Nat.lt_two_pow_self
  have hb : b < 2^V := (show b < V by omega).trans Nat.lt_two_pow_self
  have hpow : 1 ≤ 2^(a+b) := Nat.one_le_two_pow
  have hp : packet ≤ packet*2^(a+b) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left packet hpow
  exact ⟨ha,hb,hp.trans_lt hfit⟩

theorem loaded_inputs (e : Fin 117 → Fin T) (he : Function.Injective e)
    (a b packet V : ℕ) (S : Stacks T A) (i : Fin 3) :
    (loaded e a b packet V S).R (e ⟨82+i.val,by have := i.isLt; omega⟩) = binSyms V (![a,b,packet] i) := by
  fin_cases i <;> simp [loaded,he.eq_iff]

theorem loaded_off (e : Fin 117 → Fin T) (a b packet V : ℕ) (S : Stacks T A)
    (k : Fin T) (h82 : k ≠ e 82) (h83 : k ≠ e 83) (h84 : k ≠ e 84) :
    (loaded e a b packet V S).R k = S.R k := by
  simp only [loaded,Function.update_of_ne h82,Function.update_of_ne h83,Function.update_of_ne h84]

theorem loaded_project (placement : Fin T → Fin T') (hinj : Function.Injective placement)
    (e : Fin 117 → Fin T) (a b packet V : ℕ) (S : Stacks T' A) :
    embStk placement (loaded (placement ∘ e) a b packet V S) =
      loaded e a b packet V (embStk placement S) := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  simp [loaded,embStk,Function.comp_apply,Function.update_apply,hinj.eq_iff]

theorem loaded_update_off (e : Fin 117 → Fin T) (a b packet V : ℕ) (S : Stacks T A)
    (k : Fin T) (xs : List (Fin (A+4))) (h82 : e 82 ≠ k) (h83 : e 83 ≠ k) (h84 : e 84 ≠ k) :
    loaded e a b packet V {S with R := Function.update S.R k xs} =
      {loaded e a b packet V S with R := (Function.update (loaded e a b packet V S).R k xs)} := by
  refine Stacks.ext rfl rfl rfl ?_
  simp only [loaded]
  rw [Function.update_comm h82.symm,Function.update_comm h83.symm,Function.update_comm h84.symm]

theorem exec_within (body : P → Pr P T Q A U) (e : Fin 117 → Fin T)
    (he : Function.Injective e) (a b packet V : ℕ)
    (hfits : a < 2^V ∧ b < 2^V ∧ packet < 2^V)
    (v : HS T Q A U) (S : Stacks T A)
    (ha : (S.R (e 61)).length = a) (hb : (S.R (e 62)).length = b)
    (hpacket : (S.R (e 52)).length = packet) (hV : (S.R (e 35)).length = V)
    (hfresh : ∀ i ∈ [(82 : Fin 117),83,84,55,56,57,58,65,66], S.R (e i) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ timeCost a b packet V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*timeCost a b packet V) depth
        (program e) (mk v S) n (mk v' (loaded e a b packet V S)) := by
  let value (i : Fin T) := if i = e 61 then a else if i = e 62 then b else packet
  have hvalues : value (e 61) = a ∧ value (e 62) = b ∧ value (e 52) = packet := by
    simp [value,he.eq_iff]
  have hfit : ∀ r ∈ copies e, Nat.size (value r.1) ≤ V := by
    intro r hr
    simp only [copies,assignments,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hvalues.1]; exact Nat.size_le.mpr hfits.1
    · rw [hvalues.2.1]; exact Nat.size_le.mpr hfits.2.1
    · rw [hvalues.2.2]; exact Nat.size_le.mpr hfits.2.2
  have hreg : ∀ r ∈ copies e, [r.1,e 35,r.2,e 55,e 56,e 57,e 58,e 65,e 66].Nodup := by
    intro r hr
    simp only [copies,assignments,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [List.nodup_cons,he.eq_iff]
  have hnd : ((copies e).map Prod.snd).Nodup := by
    simp [copies,assignments,List.nodup_cons,he.eq_iff]
  have hsep : ∀ r ∈ copies e, ∀ q ∈ copies e, r.2 ≠ q.1 := by
    intro r hr q hq
    simp only [copies,assignments,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hr hq
    rcases hr with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> exact he.ne (by decide +kernel)
  obtain ⟨v',n,hu,hn,hx⟩ := paddedHeaderList_exec (body := body) (e 35) (e 55) (e 56) (e 57) (e 58) (e 65) (e 66)
    V value (copies e) hfit hreg hnd hsep
    (by intro r hr; simp only [copies,assignments,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl | rfl <;> exact he.ne (by decide +kernel))
    v S hV
    (by
      intro r hr
      simp only [copies,assignments,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hvalues.1]; exact ha
      · rw [hvalues.2.1]; exact hb
      · rw [hvalues.2.2]; exact hpacket)
    (by intro r hr; simp only [copies,assignments,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl | rfl <;> exact hfresh _ (by simp))
    (by intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp))
  have hcost : ((copies e).map (fun r => 21*value r.1+12*V+28)).sum+1 = timeCost a b packet V := by
    simp [copies,assignments,hvalues,timeCost]
    omega
  rw [hcost] at hn
  have hend : {S with R := paddedHeaderListR V value (copies e) S.R} = loaded e a b packet V S := by
    simp only [copies,assignments,List.map_cons,List.map_nil,paddedHeaderListR,hvalues.1,hvalues.2.1,hvalues.2.2,loaded]
  rw [hend] at hx
  exact ⟨v',n,hu,hn,mn_native_exec_within hx 2 (paddedHeaderList_native _ _ _ _ _ _ _ _) depth _ (by omega)⟩

theorem retire_exec_within (body : P → Pr P T Q A U) (e : Fin 117 → Fin T)
    (he : Function.Injective e) (a b packet V : ℕ) (output : Fin T)
    (hoff : ∀ i ∈ [(82 : Fin 117),83,84], e i ≠ output)
    (ys : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hfresh : ∀ i ∈ [(82 : Fin 117),83,84], S.R (e i) = []) (depth : ℕ) :
    let M := loaded e a b packet V S
    let F : Stacks T A := {M with R := Function.update M.R output ys}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+0) depth
        (clearWords [e 82,e 83,e 84]) (mk v F) (6*V+7)
        (mk v' {S with R := Function.update S.R output ys}) := by
  dsimp only
  let M := loaded e a b packet V S
  let F : Stacks T A := {M with R := Function.update M.R output ys}
  obtain ⟨v',hu,hx⟩ := clearWords_exec (body := body) [e 82,e 83,e 84] (by simp [List.nodup_cons,he.eq_iff]) v F
  have hcost : 2*(([e 82,e 83,e 84].map fun r => (F.R r).length).sum)+2*[e 82,e 83,e 84].length+1 = 6*V+7 := by
    simp [F,M,loaded,hoff 82 (by simp),hoff 83 (by simp),hoff 84 (by simp),he.eq_iff,binSyms]
    omega
  rw [hcost] at hx
  have hend : {F with R := fun k => if k ∈ [e 82,e 83,e 84] then [] else F.R k} =
      {S with R := Function.update S.R output ys} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k ∈ [e 82,e 83,e 84]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl
      · simp [hoff 82 (by simp),hfresh 82 (by simp)]
      · simp [hoff 83 (by simp),hfresh 83 (by simp)]
      · simp [hoff 84 (by simp),hfresh 84 (by simp)]
    · have hne := hk
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hne
      simp [hk,F,M,loaded,Function.update_apply,hne.1,hne.2.1,hne.2.2]
  rw [hend] at hx
  exact ⟨v',hu,mn_native_exec_within hx 0 (clearWords_native _) depth _ (by simp only [F,M,Nat.zero_mul,Nat.add_zero]; exact le_rfl)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PublicationBinaryDimensions
