module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCoreOrigins
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicGatherHeaders

/-! Generate the real-core count from binary geometry, move it into the router's
retained count port and retire the temporary origin queue. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q K : ℕ} {P U : Type}

def gatherCoreCountProgram : Pr P tapeCount Q (prime+K) U :=
  .seq (placedCoreOrigins headerReg)
    (.seq (moveR (headerReg 116) realRows id) (uclear (headerReg 109)))

theorem gatherCoreCount_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (V s width radius L : ℕ) (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V)
    (hLfit : L < 2^V) (hA : 4 ≤ prime+K) (hV : 0 < V)
    (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (h37 : (S.R (headerReg 37)).length = V)
    (hs : S.R (headerReg 32) = binSyms V s) (hw : S.R (headerReg 33) = binSyms V width)
    (hr : S.R (headerReg 34) = binSyms V radius) (hL : S.R (headerReg 35) = binSyms V L)
    (hz : S.R (headerReg 36) = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R (headerReg k) = [])
    (h104 : S.R (headerReg 104) = []) (h106 : S.R (headerReg 106) = [])
    (h116 : S.R (headerReg 116) = []) (h109 : S.R (headerReg 109) = [])
    (hrows : S.R realRows = []) (depth : ℕ) :
    let rows := (coreGatherIndices s width radius L).length
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedCoreOriginsCost V s width radius L+
      ((2*rows+2)+(2*(rows*V)+2)) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (3*preparedCoreOriginsCost V s width radius L+2*(2*rows+2))) depth gatherCoreCountProgram (mk v S) n
        (mk v' {S with R := Function.update S.R realRows (List.replicate rows tick)}) := by
  dsimp only
  let rows := (coreGatherIndices s width radius L).length
  let origins := (coreGatherIndices s width radius L).flatMap (fun k => binSyms (A := prime+K) V (coreStart width k-radius))
  have hi := headerReg_injective
  have hcore : realRows = headerReg 80 := rfl
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := placedCoreOrigins_exec_within (body := body) headerReg hi
    hwidth hwide hLfit hA hV v S h37 hs hw hr hL hz hblank h104 h106 h116 depth
  simp only [h109,List.append_nil] at he₁
  let M : Stacks tapeCount (prime+K) := {S with R := (Function.update
    (Function.update S.R (headerReg 109) origins) (headerReg 116) (List.replicate rows tick))}
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body (headerReg 116) realRows (by simp [hcore,hi.eq_iff]) id v₁ M
  have hcount : M.R (headerReg 116) = List.replicate rows tick := by simp [M]
  have hrowsM : M.R realRows = [] := by simpa [M,hcore,hi.eq_iff] using hrows
  let F : Stacks tapeCount (prime+K) := {S with R := (Function.update
    (Function.update S.R (headerReg 109) origins) realRows (List.replicate rows tick))}
  have hrow80 : S.R (headerReg 80) = [] := by simpa only [hcore] using hrows
  have hclear : Function.update (Function.update S.R (headerReg 109) origins) (headerReg 116) [] =
      Function.update S.R (headerReg 109) origins := by
    funext k
    by_cases hk : k = headerReg 116
    · subst k; simp [hi.eq_iff,h116]
    · simp [hk]
  have he₂' : Exec body (moveR (headerReg 116) realRows id) (mk v₁ M) (2*rows+2) (mk v₂ F) := by
    simpa [M,F,movedR,hcount,hrowsM,hcore,hi.eq_iff,h116,hrow80,hclear] using he₂
  have hn₂ : mnNativePushBound 2 (moveR (P := P) (Q := Q) (A := prime+K) (U := U) (headerReg 116) realRows id) := by
    simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have he₂w := mn_native_exec_within he₂' 2 hn₂ depth (mnSize (mk v₁ M)+depth+2*(2*rows+2)) (by omega)
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) (headerReg 109) v₂ F
  have hlen : (F.R (headerReg 109)).length = rows*V := by
    simp [F,hcore,hi.eq_iff,origins,List.length_flatMap,length_binSyms,rows]
  rw [hlen] at he₃
  have hend : {F with R := Function.update F.R (headerReg 109) []} =
      {S with R := Function.update S.R realRows (List.replicate rows tick)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = headerReg 109
    · subst k; simp [hcore,hi.eq_iff,h109]
    · simp [F,hk,Function.update_apply]
  rw [hend] at he₃
  have he₃w : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₂ F)+depth+0) depth
      (uclear (headerReg 109)) (mk v₂ F) (2*(rows*V)+2)
      (mk v₃ {S with R := Function.update S.R realRows (List.replicate rows tick)}) :=
    mn_native_exec_within he₃ 0 (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth _ (by omega)
  refine ⟨v₃,n₁+((2*rows+2)+(2*(rows*V)+2)),hu₃.trans (hu₂.trans hu₁),Nat.add_le_add_right hn₁ _,?_⟩
  simpa only [gatherCoreCountProgram,M,origins,rows,Nat.add_zero] using mn_seq_within_add he₁ (mn_seq_within_add he₂w he₃w)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
