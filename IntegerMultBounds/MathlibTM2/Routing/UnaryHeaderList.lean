module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReadUnaryDimension

/-! A fixed list of destination ports reads ordinary unary masters from binary
metadata. Values affect only the data, never the generated program. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.UnaryHeaderList
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {J U : Type} {body : J → Pr J T Q A U}

def load (r : Fin 8 → Fin T) : List (Fin T) → Pr J T Q A U
  | [] => .act .done
  | dst :: ports => .seq (readUnaryDimension (r 0) (r 1) (r 2) (r 3) dst (r 4) (r 5) (r 6) (r 7)) (load r ports)

def install (entries : List (Fin T × ℕ)) (R : Regs T A) : Regs T A :=
  match entries with
  | [] => R
  | (dst,x) :: entries => install entries (Function.update R dst (List.replicate x tick))

def packet (V : ℕ) (entries : List (Fin T × ℕ)) : List (Fin (A+4)) := entries.flatMap fun e => binSyms V e.2

def cost (V : ℕ) (entries : List (Fin T × ℕ)) := (entries.map fun e => readUnaryDimensionCost V e.2).sum+1

theorem install_off (entries : List (Fin T × ℕ)) (R : Regs T A) (j : Fin T)
    (hj : j ∉ entries.map Prod.fst) : install entries R j = R j := by
  induction entries generalizing R with
  | nil => rfl
  | cons e entries ih =>
    simp only [List.map_cons,List.mem_cons,not_or] at hj
    rw [install,ih _ hj.2,Function.update_of_ne hj.1]

theorem install_update (entries : List (Fin T × ℕ)) (R : Regs T A) (j : Fin T)
    (hj : j ∉ entries.map Prod.fst) (xs : List (Fin (A+4))) :
    install entries (Function.update R j xs) = Function.update (install entries R) j xs := by
  induction entries generalizing R with
  | nil => rfl
  | cons e entries ih =>
    simp only [List.map_cons,List.mem_cons,not_or] at hj
    simp only [install]
    rw [Function.update_comm hj.1,ih _ hj.2]

theorem load_native (r : Fin 8 → Fin T) (ports : List (Fin T)) :
    mnNativePushBound 3 (load (J := J) (Q := Q) (A := A) (U := U) r ports) := by
  induction ports with
  | nil => simp [load,mnNativePushBound,mnActPush]
  | cons dst ports ih => exact ⟨readUnaryDimension_native _ _ _ _ _ _ _ _ _,ih⟩

theorem load_exec (r : Fin 8 → Fin T) (hr : Function.Injective r) (V : ℕ)
    (entries : List (Fin T × ℕ)) (hn : (entries.map Prod.fst).Nodup)
    (hsep : ∀ dst ∈ entries.map Prod.fst, ∀ j, dst ≠ r j)
    (hfit : ∀ e ∈ entries, e.2 < 2^V) (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hV : (S.R (r 0)).length = V) (hz : S.R (r 1) = [])
    (hq : S.R (r 2) = packet V entries++tail)
    (hb : ∀ dst ∈ entries.map Prod.fst, S.R dst = [])
    (hf : ∀ j ∈ [(3 : Fin 8),4,5,6,7], S.R (r j) = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ cost V entries ∧
      Exec body (load r (entries.map Prod.fst)) (mk v S) n
        (mk vf {S with R := Function.update (install entries S.R) (r 2) tail}) := by
  induction entries generalizing v S with
  | nil =>
    have he : tail = S.R (r 2) := by simpa [packet] using hq.symm
    refine ⟨v,1,rfl,by simp [cost],?_⟩
    simpa [load,install,he] using (Exec.act (body := body) (.done : Act T Q A U) (mk v S))
  | cons e entries ih =>
    rcases e with ⟨dst,x⟩
    have htail := (List.nodup_cons.mp hn).2
    have hhead := (List.nodup_cons.mp hn).1
    have hd (j : Fin 8) : dst ≠ r j := hsep dst (by simp) j
    have hqoff : r 2 ∉ entries.map Prod.fst := by
      intro h; exact hsep _ (List.mem_cons_of_mem _ h) 2 rfl
    have hreg : [r 0,r 1,r 2,r 3,dst,r 4,r 5,r 6,r 7].Nodup := by
      simp [List.nodup_cons,hr.eq_iff,hd,ne_comm]
    obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := readUnaryDimension_exec (body := body)
      (r 0) (r 1) (r 2) (r 3) dst (r 4) (r 5) (r 6) (r 7) hreg V x (hfit (dst,x) (by simp))
      (packet V entries++tail) v S hV hz (by simpa [packet,List.append_assoc] using hq) (by
        intro j hj
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hf _ (by simp)
        · exact hb _ (by simp)
        all_goals exact hf _ (by simp))
    let F : Stacks T A := {S with R := (Function.update (Function.update S.R (r 2) (packet V entries++tail))
      dst (List.replicate x tick))}
    obtain ⟨vf,n₂,hu₂,hn₂,he₂⟩ := ih htail
      (fun d h j => hsep d (List.mem_cons_of_mem _ h) j) (fun e h => hfit e (List.mem_cons_of_mem _ h))
      v₁ F (by simp [F,(hd 0).symm,hr.eq_iff,hV]) (by simp [F,(hd 1).symm,hr.eq_iff,hz])
      (by simp [F,(hd 2).symm]) (by
        intro d h
        have hdd : d ≠ dst := fun he => hhead (he ▸ h)
        have hdq : d ≠ r 2 := hsep d (List.mem_cons_of_mem _ h) 2
        simpa [F,hdd,hdq] using hb d (List.mem_cons_of_mem _ h)) (by
        intro j hj
        have hj2 : j ≠ 2 := by intro he; subst j; simp at hj
        simpa [F,(hd j).symm,hr.ne hj2] using hf j hj)
    have hfinal : {F with R := Function.update (install entries F.R) (r 2) tail} =
        {S with R := Function.update (install ((dst,x)::entries) S.R) (r 2) tail} := by
      refine Stacks.ext rfl rfl rfl ?_
      change Function.update (install entries (Function.update (Function.update S.R (r 2)
        (packet V entries++tail)) dst (List.replicate x tick))) (r 2) tail = _
      rw [Function.update_comm (hd 2).symm,install_update entries _ _ hqoff]
      simp only [install,Function.update_idem]
    refine ⟨vf,n₁+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl (congrArg (mk vf) hfinal)⟩
    simp only [cost,List.map_cons,List.sum_cons] at *
    omega

end IntegerMultBounds.MathlibTM2.Routing.UnaryHeaderList
