module

public import IntegerMultBounds.MathlibTM2.M6.ModularScatter
public import IntegerMultBounds.MathlibTM2.M6.BitInvocation
public import IntegerMultBounds.Machine.SparseRoleCircuit

/-! Copy, fan out, and clear the PR589 temporary on the scheduled owner tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Certificates.PR589
variable {a : ℕ}

noncomputable def ownerTape (n : Fin 9) (r : Fin 32) (d : Fin 5) (j : Fin 661) : Fin 142081 :=
  ((Fin.cast card_role) (Fintype.equivFin Role (owner n r d j))).castSucc

theorem ownerTape_injective (n : Fin 9) (r : Fin 32) (d : Fin 5) :
    Function.Injective (ownerTape n r d) := by
  intro i j eq
  apply Fin.ext
  apply owner_injective n r d i i.isLt j j.isLt
  exact (Fintype.equivFin Role).injective (Fin.cast_injective _ (Fin.castSucc_injective _ eq))

private theorem fanout {t N : ℕ} (src : Fin t) (targets : List (Fin t)) (fresh : src ∉ targets)
    (unique : targets.Nodup) (data : Fin t → Fin N → ZMod 2) :
    let gates := targets.attach.map fun dst => (⟨src,dst.val,fun h => fresh (h ▸ dst.property)⟩ : PointwiseRoleGate.Gate t)
    PointwiseRoleCircuit.execute (PointwiseBinary.xorSymbol (a := a)) gates (SparseRoleCircuit.encoded data) =
      SparseRoleCircuit.encoded (fun j i => if j ∈ targets then data j i + data src i else data j i) := by
  induction targets generalizing data with
  | nil => rfl
  | cons j js ih =>
    have off : src ≠ j := fun eq => fresh (eq ▸ List.mem_cons_self)
    have tail : src ∉ js := fun mem => fresh (List.mem_cons_of_mem _ mem)
    let next := Function.update data j (fun i => data j i + data src i)
    have step : PointwiseRoleGate.applyGate ⟨src,j,off⟩ PointwiseBinary.xorSymbol
        (SparseRoleCircuit.encoded (a := a) data) = SparseRoleCircuit.encoded next := by
      funext k i
      by_cases h : k = j
      · subst k
        simp [PointwiseRoleGate.applyGate,SparseRoleCircuit.encoded,next,SparseRoleCircuit.encode_add]
      · simp [PointwiseRoleGate.applyGate,SparseRoleCircuit.encoded,next,h]
    simp only [List.attach_cons,List.map_cons,List.map_map,PointwiseRoleCircuit.execute,step]
    trans SparseRoleCircuit.encoded (fun k i => if k ∈ js then next k i + next src i else next k i)
    · exact ih tail unique.of_cons next
    congr 1
    funext k i
    by_cases eq : k = j
    · subst k
      simp [next,unique.notMem]
    · simp [next,eq,off]

/-- Fan out the common-frame temporary to every target of a selected COPY
window. All retained owners outside that window keep their original streams. -/
theorem copyAdds_hoare (n : Fin 9) (r : Fin 32) (d : Fin 5) (life : Copy.Lifecycle)
    (scheduled : life ∈ Copy.lifecycles) :
    let regs := life.targets.attach.map fun j => (⟨j.val,((Copy.target_bounds life scheduled _ j.property).2.trans (by decide : 222 < 661))⟩ : Fin 661)
    let tapes := regs.map (ownerTape n r d)
    ∃ (states : ℕ) (program : Program (142081+2) states a), ∀ {N : ℕ} (data : Fin 142081 → Fin N → ZMod 2)
      (background : Fin 142081 → ℤ → Fin (a+4)) (origins : Fin 142081 → ℤ)
      (bs : List Bool), Counter.value bs = N →
      HoareTime program (fun w => w = PointwiseRoleGate.bank background origins (SparseRoleCircuit.encoded data) bs)
        (fun w => w = PointwiseRoleGate.bank background origins (SparseRoleCircuit.encoded
          (fun j i => if j ∈ tapes then data j i + data (Fin.last 142080) i else data j i)) bs)
        (life.targets.length*(14*N+14*bs.length+34)) := by
  intro regs tapes
  have unique : regs.Nodup := by
    apply List.Nodup.of_map (f := Fin.val)
    simpa [regs,List.map_map,Function.comp_def] using (Copy.wellformed life scheduled).1
  have nodup := unique.map (ownerTape_injective n r d)
  have fresh : Fin.last 142080 ∉ tapes := by
    intro mem
    obtain ⟨j,_,eq⟩ := List.mem_map.mp mem
    exact Fin.castSucc_ne_last _ eq
  let gates := tapes.attach.map fun dst => (⟨Fin.last 142080,dst.val,fun h => fresh (h ▸ dst.property)⟩ : PointwiseRoleGate.Gate 142081)
  refine ⟨_,PointwiseRoleCircuit.program (PointwiseBinary.xorSymbol (a := a)) gates,?_⟩
  intro N data background origins bs count
  have exec := PointwiseRoleCircuit.circuit_hoare PointwiseBinary.xorSymbol gates background origins
    (SparseRoleCircuit.encoded data) bs count
  have action := fanout (a := a) _ tapes fresh nodup data
  change PointwiseRoleCircuit.execute _ gates _ = _ at action
  rw [action] at exec
  simpa only [gates,tapes,regs,List.length_map,List.length_attach] using exec

/-- Copy the retained owner into the temporary, convert its frame, fan out,
then clear it. Only the single-register frame conversion is supplied by the
caller. The copy and erase gates overwrite their destination on every bit. -/
theorem copyWindow_hoare {q : ℕ} (n : Fin 9) (r : Fin 32) (d : Fin 5) (life : Copy.Lifecycle)
    (scheduled : life ∈ Copy.lifecycles) (w : ℕ) (convert : Program (142081+2) q a) :
    let src := ownerTape n r d ⟨life.source,(Copy.source_bounds life scheduled).2⟩
    let tmp := Fin.last 142080
    let regs := life.targets.attach.map fun j => (⟨j.val,((Copy.target_bounds life scheduled _ j.property).2.trans (by decide : 222 < 661))⟩ : Fin 661)
    let targets := regs.map (ownerTape n r d)
    let R := ZMod (Shared50ModularControl.prime^w)
    let S := Swap.Shear.State (Fin 8) R
    ∃ (frame : ℕ → FramedCircuit.Frame (ZMod 2) (S → ZMod 2))
      (word : ℕ × ℕ → List (AffineFieldProgram.Op (Fin 8) R))
      (states : ℕ) (program : Program (142081+2) states a),
      LocalMoveProfile word ∧ AffineFieldProgram.interchanges (word (life.sourceFrame,0)) = 7 ∧
      ∀ {N W : ℕ} (addr : Fin N ≃ S × Fin W) (data : Fin 142081 → Fin N → ZMod 2)
      (background : Fin 142081 → ℤ → Fin (a+4)) (origins : Fin 142081 → ℤ)
      (bs : List Bool) (cost : ℕ), Counter.value bs = N →
      let frameOf := fun j => tapeFrame addr (frame j)
      let common := fun i => data src (addr.symm
        (AffineFieldProgram.run (word (life.sourceFrame,0)) (addr i).1,(addr i).2))
      let bank := fun X => PointwiseRoleGate.bank background origins (SparseRoleCircuit.encoded X) bs
      HoareTime convert (fun w => w = bank (Function.update data tmp (data src)))
        (fun w => w = bank (Function.update data tmp common)) cost →
      let output := Function.update (fun j i => if j ∈ targets then data j i + common i else data j i) tmp 0
      let stored := Copy.extendStored (fun j => data (ownerTape n r d j))
      HoareTime program (fun w => w = bank data) (fun w => w = bank output)
        (cost + (life.targets.length+2)*(14*N+14*bs.length+34)+1) ∧
      (∀ j : Fin 661, output (ownerTape n r d j) = Copy.execute frameOf life stored j) ∧
      output tmp = Copy.execute frameOf life stored 661 := by
  intro src tmp regs targets R S
  obtain ⟨frame,word,profile,windows⟩ := copyAddress_word w
  obtain ⟨seven,read⟩ := windows life scheduled
  let gate : PointwiseRoleGate.Gate 142081 := ⟨src,tmp,Fin.castSucc_ne_last _⟩
  let copy := fun (s _ : Fin (a+4)) => s
  let erase := fun (_ _ : Fin (a+4)) => SparseRoleCircuit.encode (a := a) 0
  obtain ⟨_,adds,addRun⟩ := copyAdds_hoare (a := a) n r d life scheduled
  refine ⟨frame,word,_,seq (seq (seq (PointwiseRoleGate.program gate copy) convert) adds)
    (PointwiseRoleGate.program gate erase),profile,seven,?_⟩
  intro N W addr data background origins bs cost count frameOf common bank converted output stored
  have decoded : common = frameOf 0 ((frameOf life.sourceFrame).symm (data src)) := funext (read addr (data src))
  let loaded := Function.update data tmp common
  let added := fun j i => if j ∈ targets then loaded j i + loaded tmp i else loaded j i
  have add := addRun loaded background origins bs count
  change HoareTime adds (fun w => w = bank loaded) (fun w => w = bank added) _ at add
  have write (X : Fin 142081 → Fin N → ZMod 2) (op : Fin (a+4) → Fin (a+4) → Fin (a+4))
      (value : Fin N → ZMod 2) (action : ∀ i, op (SparseRoleCircuit.encode (X src i))
        (SparseRoleCircuit.encode (X tmp i)) = SparseRoleCircuit.encode (value i)) :
      HoareTime (PointwiseRoleGate.program gate op) (fun w => w = bank X)
        (fun w => w = bank (Function.update X tmp value)) (14*N+14*bs.length+33) := by
    have step := PointwiseRoleGate.gate_hoare gate op background origins (SparseRoleCircuit.encoded X) bs count
    have same : PointwiseRoleGate.applyGate gate op (SparseRoleCircuit.encoded X) =
        SparseRoleCircuit.encoded (Function.update X tmp value) := by
      funext j i
      by_cases eq : j = tmp
      · subst j
        simpa [PointwiseRoleGate.applyGate,gate,SparseRoleCircuit.encoded] using action i
      · simp [PointwiseRoleGate.applyGate,gate,SparseRoleCircuit.encoded,eq]
    rw [same] at step
    exact step
  have done := (((write data copy (data src) (fun _ => rfl)).seq converted).seq add).seq
    (write added erase 0 (fun _ => rfl))
  have cleaned : Function.update added tmp 0 =
      Function.update (fun j i => if j ∈ targets then data j i + common i else data j i) tmp 0 := by
    funext j i
    by_cases eq : j = tmp <;> simp [eq,added,loaded]
  rw [cleaned] at done
  refine ⟨?_,?_,?_⟩
  · convert done using 1
    ring
  · intro j
    have off : ownerTape n r d j ≠ tmp := Fin.castSucc_ne_last _
    have member : ownerTape n r d j ∈ targets ↔ j.val ∈ life.targets := by
      change ownerTape n r d j ∈ regs.map (ownerTape n r d) ↔ _
      rw [List.mem_map_of_injective (ownerTape_injective n r d)]
      constructor
      · intro mem
        obtain ⟨k,_,eq⟩ := List.mem_map.mp mem
        exact (congrArg Fin.val eq) ▸ k.property
      · intro mem
        exact List.mem_map.mpr ⟨⟨j.val,mem⟩,List.mem_attach ..,Fin.ext rfl⟩
    have wf := Copy.wellformed life scheduled
    have retained : stored life.source = data src := by
      simp [stored,Copy.extendStored,(Copy.source_bounds life scheduled).2,src]
    have old : stored j.val = data (ownerTape n r d j) := by simp [stored,Copy.extendStored,j.isLt]
    have distinct : j.val ≠ 661 := Nat.ne_of_lt j.isLt
    simp only [output,Function.update_of_ne off,Copy.execute,Function.update_of_ne distinct,
      Copy.addTargets_eq _ wf.1 wf.2.1,Function.update_self,old,retained,member,decoded]
    funext i
    split <;> rfl
  · simp [output,Copy.execute]

end IntegerMultBounds.MathlibTM2.M6.BitNode
