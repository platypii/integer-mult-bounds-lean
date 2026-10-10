import IntegerMultBounds.Machine.NativeSignedGapPromoteReturn
import IntegerMultBounds.Machine.CleanSubbank

/-! Physical clean spectator promotion at arbitrary permanent role slots.
The two retained gap/volume descriptors are appended after the permanent
bank; the original bank's other tapes and every private slot are framed. -/
namespace IntegerMultBounds.Machine.CompactComplexSpectatorPromoteFamily
noncomputable section
open RadixSignedShiftRight (Word)
open NativeSignedReturnStream (volume)
open NativeSignedGapPromoteReturn (word)
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}

def headers (bs ls : List Bool) : Tapes 2 2 :=
  ⟨fun _ => 1,![RadixZeroFill.encodedBinary bs,RadixZeroFill.encodedBinary ls]⟩
def bank (v : Tapes t 2) (bs ls : List Bool) := v.append (headers bs ls)
def ready (v : Tapes t 2) (bs ls : List Bool) := CleanSubbank.bank (s:=8) (bank v bs ls)
def ports : Fin 3 → Fin 8 := ![0,4,5]
def common (i : Fin t) : Fin 3 → Fin (t+2) :=
  ![Fin.castAdd 2 i,Fin.natAdd t 0,Fin.natAdd t 1]

theorem ports_injective : Function.Injective ports := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [ports]

theorem common_injective (i : Fin t) : Function.Injective (common i) := by
  intro j k h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  fin_cases j <;> fin_cases k <;> simp [common] at hv ⊢
  all_goals omega

def one (i : Fin t) := Placement.placed NativeSignedGapPromoteReturn.program
  (CleanSubbank.placement ports (common i) (common_injective i))

private theorem small_input_clean (ws : List Word) (bs ls : List Bool) :
    SharedBank.strip (CountedLoopHeaderClean.bank (NativeSignedGapPromoteReturn.input ws bs ls)) ports =
      SharedBank.empty 8 2 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [ports,Fin.exists_fin_succ,CountedLoopHeaderClean.bank,
      NativeSignedGapPromoteReturn.input,NativeSignedGapPromoteReturn.originalStreams,
      RadixSignedShiftRight.tapes,RadixSignedShiftRight.cfg,Config.tapes,
      RadixZeroFill.input,NativeSignedReturnClean.header,
      Tapes.append,Fin.addCases,SharedBank.empty] <;> rfl

private theorem small_output_clean (ws : List Word) (d : ℕ) (bs ls : List Bool) :
    SharedBank.strip (CountedLoopHeaderClean.bank (NativeSignedGapPromoteReturn.output ws d bs ls)) ports =
      SharedBank.empty 8 2 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [ports,Fin.exists_fin_succ,CountedLoopHeaderClean.bank,
      NativeSignedGapPromoteReturn.output,Tapes.append,Fin.addCases,SharedBank.empty]

private theorem input_payload (v : Tapes t 2) (i : Fin t) (ws : List Word) (bs ls : List Bool)
    (hh : v.head i=0) (ht : v.tape i=word ws) :
    SharedBank.payload (CountedLoopHeaderClean.bank (NativeSignedGapPromoteReturn.input ws bs ls)) ports =
      SharedBank.payload (bank v bs ls) (common i) := by
  apply congrArg₂ Tapes.mk <;> funext j <;> fin_cases j <;>
    simp [ports,common,bank,headers,hh,ht,CountedLoopHeaderClean.bank,
      NativeSignedGapPromoteReturn.input,NativeSignedGapPromoteReturn.originalStreams,
      RadixSignedShiftRight.tapes,RadixSignedShiftRight.cfg,Config.tapes,
      RadixZeroFill.input,NativeSignedReturnClean.header,Tapes.append,Fin.addCases] <;> rfl

private theorem output_payload (v : Tapes t 2) (i : Fin t) (ws : List Word) (d : ℕ) (bs ls : List Bool) :
    SharedBank.payload (CountedLoopHeaderClean.bank (NativeSignedGapPromoteReturn.output ws d bs ls)) ports =
      SharedBank.payload (bank (setTape v i (word (ws.map (NativeSignedGapPromoteWord.result d))) 0) bs ls)
        (common i) := by
  apply congrArg₂ Tapes.mk <;> funext j <;> fin_cases j <;>
    simp [ports,common,bank,headers,setTape,CountedLoopHeaderClean.bank,
      NativeSignedGapPromoteReturn.output,Tapes.append,Fin.addCases]

private theorem outside_frame (v : Tapes t 2) (i : Fin t) (g : ℤ → Fin 6) (bs ls : List Bool) :
    SharedBank.strip (bank v bs ls) (common i) =
      SharedBank.strip (bank (setTape v i g 0) bs ls) (common i) := by
  rw [bank,bank,←SharedPlacementAlphabet.setTape_append_left]
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals by_cases hj : ∃ k,common i k=j
  all_goals simp only [hj,↓reduceIte]
  all_goals
    have hne : j≠Fin.castAdd 2 i := by
      intro h
      exact hj ⟨0,by change Fin.castAdd 2 i=j; exact h.symm⟩
    simp [setTape,hne]

/-- This is a literal placed eight-tape program, with no execution callback.
Every other permanent tape, both descriptors, and all private heads survive. -/
theorem one_runs (v : Tapes t 2) (i : Fin t) (ws : List Word) (d : ℕ)
    (hd : ∀ w∈ws,d≤w.length) (hn : ws≠[]) (bs ls : List Bool)
    (hgap : Counter.value bs=d) (hlen : Counter.value ls=volume ws)
    (hb : GrowingCounterData.Canonical bs) (hl : GrowingCounterData.Canonical ls)
    (hh : v.head i=0) (ht : v.tape i=word ws) :
    HoareTime (one i) (fun z => z=ready v bs ls)
      (fun z => z=ready (setTape v i (word (ws.map (NativeSignedGapPromoteWord.result d))) 0) bs ls)
      (130*volume ws+324) := by
  exact CleanSubbank.realizes NativeSignedGapPromoteReturn.program ports (common i)
    ports_injective (common_injective i) _ _ _ _ _
    (input_payload v i ws bs ls hh ht) (output_payload v i ws d bs ls)
    (small_input_clean ws bs ls) (small_output_clean ws d bs ls)
    (outside_frame v i _ bs ls)
    (NativeSignedGapPromoteReturn.runs_linear ws d hd hn bs ls hgap hlen hb hl)

def compile {c : ℕ} (roles : Fin c → Fin t) : List (Fin c) → Σ n,Program (t+2+8) n 2
  | [] => ⟨1,skip _ _ (by omega)⟩
  | j::js => ⟨_,seq (one (roles j)) (compile roles js).2⟩

def execute {c : ℕ} (roles : Fin c → Fin t) (words : Fin c → ℤ → Fin 6) :
    List (Fin c) → Tapes t 2 → Tapes t 2
  | [],v => v
  | j::js,v => execute roles words js (setTape v (roles j) (words j) 0)

theorem execute_frame {c : ℕ} (roles : Fin c → Fin t) (words : Fin c → ℤ → Fin 6)
    (js : List (Fin c)) (v : Tapes t 2) (i : Fin t)
    (hout : ∀ j∈js,i≠roles j) :
    (execute roles words js v).head i=v.head i ∧
      (execute roles words js v).tape i=v.tape i := by
  induction js generalizing v with
  | nil => exact ⟨rfl,rfl⟩
  | cons j js ih =>
    have h := ih (setTape v (roles j) (words j) 0)
      (fun k hk => hout k (List.mem_cons_of_mem j hk))
    simpa only [execute,setTape,Function.update_of_ne (hout j List.mem_cons_self)] using h

/-- A fixed list executes literal stream promoters, reusing the same clean
workspace and retained descriptors at every role. No huge concrete role list
is evaluated by this proof. -/
theorem compile_runs {c : ℕ} (roles : Fin c → Fin t) (hinj : Function.Injective roles)
    (ws : Fin c → List Word) (js : List (Fin c)) (hnd : js.Nodup)
    (v : Tapes t 2) (d V : ℕ) (bs ls : List Bool)
    (hd : ∀ j w,w∈ws j → d≤w.length) (hn : ∀ j,ws j≠[])
    (hv : ∀ j,volume (ws j)=V) (hgap : Counter.value bs=d) (hlen : Counter.value ls=V)
    (hb : GrowingCounterData.Canonical bs) (hl : GrowingCounterData.Canonical ls)
    (hsource : ∀ j∈js,v.head (roles j)=0 ∧ v.tape (roles j)=word (ws j)) :
    HoareTime (compile roles js).2 (fun z => z=ready v bs ls)
      (fun z => z=ready (execute roles
        (fun j => word ((ws j).map (NativeSignedGapPromoteWord.result d))) js v) bs ls)
      (js.length*(130*V+325)) := by
  induction js generalizing v with
  | nil =>
    simpa only [compile,execute,List.length_nil,Nat.zero_mul] using
      (skip_hoare (a:=2) (by omega : 0<t+2+8) (ready v bs ls))
  | cons j js ih =>
    obtain ⟨hj,hjs⟩ := List.nodup_cons.mp hnd
    have h0 := one_runs v (roles j) (ws j) d (hd j) (hn j) bs ls hgap
      (by rw [hv];exact hlen) hb hl (hsource j (by simp)).1 (hsource j (by simp)).2
    rw [hv j] at h0
    have ht := ih hjs (setTape v (roles j) (word ((ws j).map (NativeSignedGapPromoteWord.result d))) 0)
      (by
        intro k hk
        have hne : roles k≠roles j := by
          intro he
          have he' := hinj he
          subst k
          exact hj hk
        simpa only [setTape,Function.update_of_ne hne] using hsource k (List.mem_cons_of_mem j hk))
    exact (h0.seq ht).consequence (fun _ h => h) (fun _ h => h)
      (by simp only [List.length_cons,Nat.add_mul]; omega)

def spectatorList {c : ℕ} (selected : Fin c) :=
  (List.finRange c).filter (fun j => j≠selected)

theorem spectatorList_nodup {c : ℕ} (selected : Fin c) : (spectatorList selected).Nodup :=
  (List.nodup_finRange c).filter _

@[simp] theorem spectatorList_mem {c : ℕ} (selected j : Fin c) :
    j∈spectatorList selected ↔ j≠selected := by simp [spectatorList]

theorem selected_frame {c : ℕ} (roles : Fin c → Fin t) (hinj : Function.Injective roles)
    (selected : Fin c) (words : Fin c → ℤ → Fin 6) (v : Tapes t 2) :
    (execute roles words (spectatorList selected) v).head (roles selected)=v.head (roles selected) ∧
      (execute roles words (spectatorList selected) v).tape (roles selected)=v.tape (roles selected) := by
  apply execute_frame
  intro j hj he
  exact ((spectatorList_mem selected j).mp hj) (hinj he).symm

/-- Genuine selected-role exclusion is part of the fixed finite program. -/
theorem spectators_runs {c : ℕ} (roles : Fin c → Fin t) (hinj : Function.Injective roles)
    (selected : Fin c) (ws : Fin c → List Word) (v : Tapes t 2) (d V : ℕ) (bs ls : List Bool)
    (hd : ∀ j w,w∈ws j → d≤w.length) (hn : ∀ j,ws j≠[])
    (hv : ∀ j,volume (ws j)=V) (hgap : Counter.value bs=d) (hlen : Counter.value ls=V)
    (hb : GrowingCounterData.Canonical bs) (hl : GrowingCounterData.Canonical ls)
    (hsource : ∀ j,j≠selected → v.head (roles j)=0 ∧ v.tape (roles j)=word (ws j)) :
    HoareTime (compile roles (spectatorList selected)).2 (fun z => z=ready v bs ls)
      (fun z => z=ready (execute roles
        (fun j => word ((ws j).map (NativeSignedGapPromoteWord.result d))) (spectatorList selected) v) bs ls)
      ((spectatorList selected).length*(130*V+325)) :=
  compile_runs roles hinj ws _ (spectatorList_nodup selected) v d V bs ls hd hn hv hgap hlen hb hl
    (fun j hj => hsource j ((spectatorList_mem selected j).mp hj))

end
end IntegerMultBounds.Machine.CompactComplexSpectatorPromoteFamily
