module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedClassBanks
public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopiesStock

/-! One retained binary dimension table supplies every unary class input.
The export list is structural and may read the same dimension more than once. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
namespace ComputedClassBanks

/-- Dimension order: p,u,l,target,s,t,B,W,N,radius,core rows,halo rows. -/
def inputAssignments : List (Fin 12 × ComputedClassBank) :=
  [(0,.recovery (.parameter 0)),(1,.recovery (.parameter 1)),
   (2,.recovery (.parameter 2)),(3,.recovery (.parameter 3)),
   (4,.recovery (.parameter 4)),(5,.recovery (.parameter 5)),
   (0,.recovery (.control .precision)),(7,.recovery (.control .packet)),
   (8,.recovery (.control .replicas)),(9,.recovery (.control .cropOffset)),
   (10,.recovery (.control .cropRows)),(6,.recovery (.scalar .wr)),
   (6,.control .width),(11,.control .halo),(6,.geometry 37)]

theorem inputAssignments_nodup : (inputAssignments.map Prod.snd).Nodup := by decide +kernel

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)

def inputCopies : List (Fin 12 × Fin T) := inputAssignments.map (fun p => (p.1,bank p.2))
def inputRegisters : List (Fin T) := (inputCopies bank).map Prod.snd

include hinj in
theorem inputRegisters_nodup : (inputRegisters bank).Nodup := by
  simpa only [inputRegisters,inputCopies,List.map_map,Function.comp_def] using
    List.Nodup.map hinj inputAssignments_nodup

def inputState (values : Fin 12 → ℕ) (S : Stacks T A) : Stacks T A :=
  {S with R := unaryCopiesR values S.R (inputCopies bank)}

include hinj in
theorem inputState_at (values : Fin 12 → ℕ) (S : Stacks T A)
    (hblank : ∀ k ∈ inputRegisters bank, S.R k = [])
    (p : Fin 12 × ComputedClassBank) (hp : p ∈ inputAssignments) :
    (inputState bank values S).R (bank p.2) = List.replicate (values p.1) tick := by
  have hmem : (p.1,bank p.2) ∈ inputCopies bank := List.mem_map.mpr ⟨p,hp,rfl⟩
  have h := unaryCopiesR_at values S.R (inputCopies bank) (inputRegisters_nodup bank hinj) _ hmem
  change unaryCopiesR values S.R (inputCopies bank) (bank p.2) = _
  rw [h,hblank _ (List.mem_map.mpr ⟨_,hmem,rfl⟩),List.append_nil]

theorem inputState_off (values : Fin 12 → ℕ) (S : Stacks T A) (k : Fin T)
    (hk : k ∉ inputRegisters bank) : (inputState bank values S).R k = S.R k := by
  apply unaryCopiesR_off
  intro p hp he
  exact hk (List.mem_map.mpr ⟨p,hp,he⟩)

theorem inputState_clear (values : Fin 12 → ℕ) (S : Stacks T A)
    (hblank : ∀ k ∈ inputRegisters bank, S.R k = []) :
    {inputState bank values S with R := (fun k =>
      if k ∈ inputRegisters bank then [] else (inputState bank values S).R k)} = S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk : k ∈ inputRegisters bank
  · simp only [hk,ite_true]; exact (hblank k hk).symm
  · simp only [hk,ite_false]; exact inputState_off bank values S k hk

theorem inputState_update (values : Fin 12 → ℕ) (S : Stacks T A) (k : Fin T)
    (xs : List (Fin (A+4))) (hk : k ∉ inputRegisters bank) :
    inputState bank values {S with R := Function.update S.R k xs} =
      {inputState bank values S with R := Function.update (inputState bank values S).R k xs} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext j
  by_cases hj : j = k
  · subst j
    change (inputState bank values {S with R := Function.update S.R k xs}).R k =
      Function.update (inputState bank values S).R k xs k
    rw [Function.update_self,inputState_off bank values _ k hk]
    exact Function.update_self ..
  · change unaryCopiesR values (Function.update S.R k xs) (inputCopies bank) j =
      Function.update (unaryCopiesR values S.R (inputCopies bank)) k xs j
    rw [Function.update_of_ne hj]
    apply unaryCopiesR_congr_base
    · intro p hp
      exact Function.update_of_ne (by
        intro he; exact hk (List.mem_map.mpr ⟨p,hp,he⟩)) _ _
    · exact Function.update_of_ne hj _ _

def inputVolume (values : Fin 12 → ℕ) : ℕ := (inputAssignments.map (fun p => values p.1)).sum

include hinj in
theorem inputState_volume (values : Fin 12 → ℕ) (S : Stacks T A)
    (hblank : ∀ k ∈ inputRegisters bank, S.R k = []) :
    ((inputRegisters bank).map (fun k => ((inputState bank values S).R k).length)).sum = inputVolume values := by
  unfold inputRegisters inputCopies inputVolume
  simp only [List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [inputState_at bank hinj values S hblank p hp,List.length_replicate]

def inputProgram (rg : TblR 12 → Fin T) : Pr P T Q A U := tblUnaryCopies rg (inputCopies bank)

theorem input_exec (rg : TblR 12 → Fin T) (hrg : Function.Injective rg)
    (hoff : ∀ r k, rg r ≠ bank k) (B : ℕ) (wl nl : List (Fin (A+4)))
    (st : TblSt 12 A) (hfit : ∀ i, st.val i < 2^B)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho B wl nl st)) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ unaryCopiesCost B st.val (inputCopies bank) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        3*unaryCopiesCost B st.val (inputCopies bank)) depth
        (inputProgram bank rg) (Host.mk v S) n (Host.mk v' (inputState bank st.val S)) := by
  obtain ⟨v',n,hu,hn,he⟩ := tblUnaryCopies_exec (body := body) hrg wl nl st hfit (inputCopies bank)
    (by intro p hp r; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact hoff r q.2) v S hS
  refine ⟨v',n,hu,hn,?_⟩
  exact mn_native_exec_within he 3 (tblUnaryCopies_native rg (inputCopies bank)) depth _
    (by nlinarith only [hn])

include hinj in
theorem input_release_exec (values : Fin 12 → ℕ) (S : Stacks T A)
    (hblank : ∀ k ∈ inputRegisters bank, S.R k = []) (v : HS T Q A U) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v (inputState bank values S))+depth+
        3*(2*inputVolume values+2*(inputRegisters bank).length+1)) depth
        (clearWords (inputRegisters bank)) (Host.mk v (inputState bank values S))
        (2*inputVolume values+2*(inputRegisters bank).length+1) (Host.mk v' S) := by
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) (inputRegisters bank)
    (inputRegisters_nodup bank hinj) v (inputState bank values S)
  rw [inputState_volume bank hinj values S hblank,inputState_clear bank values S hblank] at he
  exact ⟨v',hu,mn_native_exec_within he 3 (clearWords_native_three _) depth _ le_rfl⟩

theorem inputCost_eq (B : ℕ) (values : Fin 12 → ℕ) :
    unaryCopiesCost B values (inputCopies bank) = 165*B+6*inputVolume values+91 := by
  rw [unaryCopiesCost_eq]
  simp only [inputCopies,List.length_map,List.map_map,Function.comp_def]
  change 15*(11*B+6)+6*inputVolume values+1 = _
  ring

theorem inputLifecycleCost_eq (B : ℕ) (values : Fin 12 → ℕ) :
    unaryCopiesCost B values (inputCopies bank)+(2*inputVolume values+2*(inputRegisters bank).length+1) =
      165*B+8*inputVolume values+122 := by
  rw [inputCost_eq]
  change 165*B+6*inputVolume values+91+(2*inputVolume values+2*15+1) = _
  ring

/-- The class changes only these external streams. Its exact frame commutes
with input export, so final input cleanup preserves the produced output. -/
theorem inputState_output (values : Fin 12 → ℕ) (S : Stacks T A) (source result : Fin T)
    (tail word : List (Fin (A+4))) (hs : source ∉ inputRegisters bank) (hr : result ∉ inputRegisters bank) :
    let F := inputState bank values S
    {F with R := Function.update (Function.update F.R source tail) result (word++F.R result)} =
      inputState bank values {S with R := Function.update (Function.update S.R source tail) result (word++S.R result)} := by
  dsimp only
  have h := inputState_update bank values {S with R := Function.update S.R source tail}
    result (word++S.R result) hr
  rw [inputState_update bank values S source tail hs] at h
  simpa only [inputState_off bank values S result hr] using h.symm

include hinj in
theorem input_release_output_exec (values : Fin 12 → ℕ) (S : Stacks T A)
    (hblank : ∀ k ∈ inputRegisters bank, S.R k = []) (source result : Fin T)
    (tail word : List (Fin (A+4))) (hs : source ∉ inputRegisters bank) (hr : result ∉ inputRegisters bank)
    (v : HS T Q A U) (depth : ℕ) :
    let F := inputState bank values S
    let G : Stacks T A := {F with R := Function.update (Function.update F.R source tail) result (word++F.R result)}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v G)+depth+
        3*(2*inputVolume values+2*(inputRegisters bank).length+1)) depth
        (clearWords (inputRegisters bank)) (Host.mk v G)
        (2*inputVolume values+2*(inputRegisters bank).length+1)
        (Host.mk v' {S with R := Function.update (Function.update S.R source tail) result (word++S.R result)}) := by
  dsimp only
  rw [inputState_output bank values S source result tail word hs hr]
  apply input_release_exec bank hinj values _ ?_ v depth
  intro k hk
  change Function.update (Function.update S.R source tail) result (word++S.R result) k = []
  rw [Function.update_of_ne (by intro h; subst k; exact hr hk),
    Function.update_of_ne (by intro h; subst k; exact hs hk)]
  exact hblank k hk

include hinj in
theorem inputRegisters_off (k : ComputedClassBank) (hk : k ∉ inputAssignments.map Prod.snd) :
    bank k ∉ inputRegisters bank := by
  intro h
  simp only [inputRegisters,inputCopies,List.map_map,Function.comp_def,List.mem_map] at h
  obtain ⟨p,hp,he⟩ := h
  exact hk (List.mem_map.mpr ⟨p,hp,hinj he⟩)

theorem inputParameter_assignment (i : Fin 6) :
    (Fin.castLE (by decide : 6 ≤ 12) i,
      ComputedClassBank.recovery (.parameter (Fin.castLE (by decide : 6 ≤ 8) i))) ∈ inputAssignments := by
  revert i
  decide +kernel

include hinj in
theorem inputState_parameter (values : Fin 12 → ℕ) (S : Stacks T A)
    (hblank : ∀ k ∈ inputRegisters bank, S.R k = []) (i : Fin 6) :
    (inputState bank values S).R (recovery bank (.parameter (Fin.castLE (by decide : 6 ≤ 8) i))) =
      List.replicate (values (Fin.castLE (by decide : 6 ≤ 12) i)) tick :=
  inputState_at bank hinj values S hblank _ (inputParameter_assignment i)

theorem parameter_prefix (i : Fin 8) (ha : i ≠ 6) (hb : i ≠ 7) :
    ∃ j : Fin 6, Fin.castLE (by decide : 6 ≤ 8) j = i := by
  have h6 : i.val ≠ 6 := fun h => ha (Fin.ext h)
  have h7 : i.val ≠ 7 := fun h => hb (Fin.ext h)
  have hi : i.val < 6 := by omega
  exact ⟨⟨i.val,hi⟩,Fin.ext rfl⟩

end ComputedClassBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
