module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReadUnaryDimension
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Read a fixed row of reusable unary masters from binary schedule data.
The program depends only on the destination ports, never the dimension values. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def readDimensionRow (width zero queue binary duplicate work saved tmp : Fin T) :
    List (Fin T) → Pr P T Q A U
  | [] => .act .done
  | dst::ds => .seq (readUnaryDimension width zero queue binary dst duplicate work saved tmp)
      (readDimensionRow width zero queue binary duplicate work saved tmp ds)

def dimensionRowR (xs : List (ℕ × Fin T)) (R : Regs T A) : Regs T A :=
  match xs with
  | [] => R
  | (x,dst)::xs => dimensionRowR xs (Function.update R dst (List.replicate x tick))

theorem dimensionRowR_off (xs : List (ℕ × Fin T)) (R : Regs T A) (k : Fin T)
    (hoff : ∀ p ∈ xs, p.2 ≠ k) : dimensionRowR xs R k = R k := by
  induction xs generalizing R with
  | nil => rfl
  | cons p xs ih =>
    rw [dimensionRowR,ih _ (by intro q hq; exact hoff q (by simp [hq]))]
    exact Function.update_of_ne (Ne.symm (hoff p (by simp))) _ _

theorem dimensionRowR_update_off (xs : List (ℕ × Fin T)) (R : Regs T A) (k : Fin T)
    (word : List (Fin (A+4))) (hoff : ∀ p ∈ xs, p.2 ≠ k) :
    dimensionRowR xs (Function.update R k word) = Function.update (dimensionRowR xs R) k word := by
  induction xs generalizing R with
  | nil => rfl
  | cons p xs ih =>
    simp only [dimensionRowR]
    rw [Function.update_comm (hoff p (by simp)).symm]
    exact ih _ (by intro q hq; exact hoff q (by simp [hq]))

theorem dimensionRowR_at (xs : List (ℕ × Fin T)) (R : Regs T A)
    (hds : (xs.map Prod.snd).Nodup) (p : ℕ × Fin T) (hp : p ∈ xs) :
    dimensionRowR xs R p.2 = List.replicate p.1 tick := by
  induction xs generalizing R with
  | nil => simp at hp
  | cons q xs ih =>
    rcases List.mem_cons.mp hp with he | hp
    · subst p
      rw [dimensionRowR,dimensionRowR_off]
      · exact Function.update_self ..
      · intro p hp he
        exact (List.nodup_cons.mp hds).1 (List.mem_map.mpr ⟨p,hp,he⟩)
    · exact ih _ (List.nodup_cons.mp hds).2 hp

def readDimensionRowCost (V : ℕ) (xs : List (ℕ × Fin T)) : ℕ :=
  (xs.map (fun p => readUnaryDimensionCost V p.1)).sum+1

theorem readDimensionRowCost_le (V N : ℕ) (xs : List (ℕ × Fin T))
    (hV : V ≤ N) (hN : 1 ≤ N) (hxs : ∀ p ∈ xs, p.1 ≤ N) :
    readDimensionRowCost V xs ≤ 55*xs.length*N+1 := by
  induction xs with
  | nil => simp [readDimensionRowCost]
  | cons p xs ih =>
    have hh := ih (by intro q hq; exact hxs q (by simp [hq]))
    have hp := hxs p (by simp)
    simp only [readDimensionRowCost,List.map_cons,List.sum_cons,List.length_cons,
      readUnaryDimensionCost] at hh ⊢
    nlinarith only [hh,hp,hV,hN]

theorem readDimensionRow_native (width zero queue binary duplicate work saved tmp : Fin T)
    (ds : List (Fin T)) :
    mnNativePushBound 3 (readDimensionRow (P := P) (Q := Q) (A := A) (U := U)
      width zero queue binary duplicate work saved tmp ds) := by
  induction ds with
  | nil => simp [readDimensionRow,mnNativePushBound,mnActPush]
  | cons dst ds ih => exact ⟨readUnaryDimension_native _ _ _ _ _ _ _ _ _,ih⟩

theorem readDimensionRow_exec (width zero queue binary duplicate work saved tmp : Fin T)
    (V : ℕ) (xs : List (ℕ × Fin T))
    (hreg : ∀ p ∈ xs, [width,zero,queue,binary,p.2,duplicate,work,saved,tmp].Nodup)
    (hds : (xs.map Prod.snd).Nodup) (hfit : ∀ p ∈ xs, p.1 < 2^V)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R width).length = V) (hzero : S.R zero = [])
    (hqueue : S.R queue = (xs.flatMap fun p => binSyms V p.1)++tail)
    (hblank : ∀ k ∈ [binary,duplicate,work,saved,tmp]++xs.map Prod.snd, S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ readDimensionRowCost V xs ∧
      Exec body (readDimensionRow width zero queue binary duplicate work saved tmp (xs.map Prod.snd))
        (Host.mk v S) n (Host.mk v' {S with R := dimensionRowR xs (Function.update S.R queue tail)}) := by
  induction xs generalizing v S with
  | nil =>
    refine ⟨v,1,rfl,by simp [readDimensionRowCost],?_⟩
    have he := Exec.act (body := body) .done (Host.mk v S)
    have hq : S.R queue = tail := by simpa using hqueue
    have hR : Function.update S.R queue tail = S.R := by rw [←hq]; simp
    simpa [readDimensionRow,dimensionRowR,hR,Action.run] using he
  | cons p xs ih =>
    rcases p with ⟨x,dst⟩
    have hr := hreg (x,dst) (by simp)
    regs_ne hr
    have hd : ∀ p ∈ xs, p.2 ≠ dst := by
      intro p hp he
      have hh := (List.nodup_cons.mp hds).1
      exact hh (List.mem_map.mpr ⟨p,hp,he⟩)
    have hcontrols : ∀ i ∈ [binary,duplicate,work,saved,tmp], i ≠ dst ∧ i ≠ queue := by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> constructor <;> first | assumption | exact Ne.symm (by assumption)
    obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := readUnaryDimension_exec width zero queue binary dst duplicate work saved tmp
      (hreg (x,dst) (by simp)) V x (hfit (x,dst) (by simp)) ((xs.flatMap fun p => binSyms V p.1)++tail) v S hwidth hzero
      (by simpa only [List.flatMap_cons,List.append_assoc] using hqueue)
      (by
        intro i hi
        apply hblank
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    let M : Stacks T A := {S with R := (Function.update
      (Function.update S.R queue ((xs.flatMap fun p => binSyms V p.1)++tail)) dst (List.replicate x tick))}
    have hoff (i : Fin T) (hd : i ≠ dst) (hq : i ≠ queue) : M.R i = S.R i := by
      simp only [M,Function.update_of_ne hd,Function.update_of_ne hq]
    obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := ih
      (by intro p hp; exact hreg p (by simp [hp])) (List.nodup_cons.mp hds).2
      (by intro p hp; exact hfit p (by simp [hp])) v₁ M
      (by rw [hoff width ‹width ≠ dst› ‹width ≠ queue›]; exact hwidth)
      (by rw [hoff zero ‹zero ≠ dst› ‹zero ≠ queue›]; exact hzero)
      (by simp only [M,Function.update_of_ne ‹queue ≠ dst›,Function.update_self])
      (by
        intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · rw [hoff i (hcontrols i hi).1 (hcontrols i hi).2]
          exact hblank i (List.mem_append_left _ hi)
        · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hi
          have hpreg := hreg p (by simp [hp])
          have hq : p.2 ≠ queue := by regs_ne hpreg; exact Ne.symm (by assumption)
          rw [hoff _ (hd p hp) hq]
          exact hblank _ (List.mem_append_right _ (List.mem_map.mpr ⟨p,List.mem_cons_of_mem (x,dst) hp,rfl⟩)))
    have hR : Function.update M.R queue tail =
        Function.update (Function.update S.R queue tail) dst (List.replicate x tick) := by
      funext i
      by_cases hq : i = queue
      · subst i
        simp only [Function.update_self,Function.update_of_ne ‹queue ≠ dst›]
      · by_cases hd : i = dst
        · subst i
          simp only [M,Function.update_of_ne hq,Function.update_self]
        · simp only [M,Function.update_of_ne hq,Function.update_of_ne hd]

    refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,?_⟩
    · simp only [readDimensionRowCost,List.map_cons,List.sum_cons] at hn₂ ⊢
      omega
    · have he := Exec.seq he₁ he₂
      simpa only [List.map_cons,readDimensionRow,dimensionRowR,hR,M] using he

theorem releaseDimensionRow_exec (xs : List (ℕ × Fin T))
    (hds : (xs.map Prod.snd).Nodup) (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ k ∈ xs.map Prod.snd, S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (ShortConv.clearWords (xs.map Prod.snd))
        (Host.mk v {S with R := dimensionRowR xs S.R})
        (2*(xs.map Prod.fst).sum+2*xs.length+1) (Host.mk v' S) := by
  obtain ⟨v',hu,he⟩ := ShortConv.clearWords_exec (body := body) (xs.map Prod.snd) hds
    v {S with R := dimensionRowR xs S.R}
  have hvol : ((xs.map Prod.snd).map (fun k => (dimensionRowR xs S.R k).length)).sum =
      (xs.map Prod.fst).sum := by
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp_def,dimensionRowR_at xs S.R hds p hp,List.length_replicate]
  simp only [hvol,List.length_map] at he
  refine ⟨v',hu,he.cast rfl ?_⟩
  apply congrArg (Host.mk v')
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk : k ∈ xs.map Prod.snd
  · simp only [hk,ite_true]; exact (hblank k hk).symm
  · simp only [hk,ite_false]
    exact dimensionRowR_off xs S.R k (by
      intro p hp he
      exact hk (List.mem_map.mpr ⟨p,hp,he⟩))

theorem readDimensionRow_exec_within (width zero queue binary duplicate work saved tmp : Fin T)
    (V : ℕ) (xs : List (ℕ × Fin T))
    (hreg : ∀ p ∈ xs, [width,zero,queue,binary,p.2,duplicate,work,saved,tmp].Nodup)
    (hds : (xs.map Prod.snd).Nodup) (hfit : ∀ p ∈ xs, p.1 < 2^V)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R width).length = V) (hzero : S.R zero = [])
    (hqueue : S.R queue = (xs.flatMap fun p => binSyms V p.1)++tail)
    (hblank : ∀ k ∈ [binary,duplicate,work,saved,tmp]++xs.map Prod.snd, S.R k = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ readDimensionRowCost V xs ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        3*readDimensionRowCost V xs) depth
        (readDimensionRow width zero queue binary duplicate work saved tmp (xs.map Prod.snd))
        (Host.mk v S) n (Host.mk v' {S with R := dimensionRowR xs (Function.update S.R queue tail)}) := by
  obtain ⟨v',n,hu,hn,he⟩ := readDimensionRow_exec width zero queue binary duplicate work saved tmp
    V xs hreg hds hfit tail v S hwidth hzero hqueue hblank
  exact ⟨v',n,hu,hn,mn_native_exec_within he 3
    (readDimensionRow_native _ _ _ _ _ _ _ _ _) depth _ (by omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
