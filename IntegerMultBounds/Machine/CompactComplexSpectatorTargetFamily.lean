import IntegerMultBounds.Machine.NativeSignedGapPromoteHeadersReturn
import IntegerMultBounds.Machine.CompactComplexSpectatorPromoteFamily

/-! Spectator promotion uses physical current/target denominator tapes.
Each actual subroutine synthesizes and erases the difference, preserving the
true denominator words until the whole role bank has been aligned. -/
namespace IntegerMultBounds.Machine.CompactComplexSpectatorTargetFamily
noncomputable section
open RadixSignedShiftRight (Word)
open NativeSignedReturnStream (volume)
open NativeSignedGapPromoteReturn (word)
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)
open CompactComplexSpectatorPromoteFamily (execute spectatorList spectatorList_nodup spectatorList_mem)
variable {t c : ℕ}

def ports : Fin 4 → Fin 10 := ![0,8,9,5]
def common (source current target length : Fin t) : Fin 4 → Fin t :=
  ![source,current,target,length]
def ready (v : Tapes t 2) := CleanSubbank.bank (s:=10) v
def one (p : Fin 4 → Fin t) (hp : Function.Injective p) :=
  Placement.placed NativeSignedGapPromoteHeadersReturn.program (CleanSubbank.placement ports p hp)

theorem ports_injective : Function.Injective ports := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [ports]

private theorem input_clean (ws : List Word) (current target : ℕ) (ls : List Bool) :
    SharedBank.strip (NativeSignedGapPromoteHeadersReturn.input ws current target ls) ports =
      SharedBank.empty 10 2 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [ports,Fin.exists_fin_succ,NativeSignedGapPromoteHeadersReturn.input,
      NativeSignedGapPromoteHeadersReturn.prepared,NativeSignedGapPromoteHeadersReturn.exponents,
      setTape,CountedLoopHeaderClean.bank,NativeSignedGapPromoteReturn.input,
      NativeSignedGapPromoteReturn.originalStreams,RadixSignedShiftRight.tapes,
      RadixSignedShiftRight.cfg,Config.tapes,RadixZeroFill.input,
      NativeSignedReturnClean.header,Tapes.append,Fin.addCases,SharedBank.empty] <;> rfl

private theorem output_clean (ws : List Word) (current target : ℕ) (ls : List Bool) :
    SharedBank.strip (NativeSignedGapPromoteHeadersReturn.output ws current target ls) ports =
      SharedBank.empty 10 2 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [ports,Fin.exists_fin_succ,NativeSignedGapPromoteHeadersReturn.output,
      NativeSignedGapPromoteHeadersReturn.returned,NativeSignedGapPromoteHeadersReturn.exponents,
      setTape,CountedLoopHeaderClean.bank,NativeSignedGapPromoteReturn.output,
      Tapes.append,Fin.addCases,SharedBank.empty]

private theorem input_payload (v : Tapes t 2) (p : Fin 4 → Fin t)
    (ws : List Word) (current target : ℕ) (ls : List Bool)
    (hs : v.head (p 0)=0 ∧ v.tape (p 0)=word ws)
    (hc : v.head (p 1)=1 ∧ v.tape (p 1)=RadixZeroFill.encodedBinary (bits current))
    (ht : v.head (p 2)=1 ∧ v.tape (p 2)=RadixZeroFill.encodedBinary (bits target))
    (hl : v.head (p 3)=1 ∧ v.tape (p 3)=RadixZeroFill.encodedBinary ls) :
    SharedBank.payload (NativeSignedGapPromoteHeadersReturn.input ws current target ls) ports =
      SharedBank.payload v p := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [ports,hs.1,hs.2,hc.1,hc.2,ht.1,ht.2,hl.1,hl.2,
      NativeSignedGapPromoteHeadersReturn.input,NativeSignedGapPromoteHeadersReturn.prepared,
      NativeSignedGapPromoteHeadersReturn.exponents,setTape,CountedLoopHeaderClean.bank,
      NativeSignedGapPromoteReturn.input,NativeSignedGapPromoteReturn.originalStreams,
      RadixSignedShiftRight.tapes,RadixSignedShiftRight.cfg,Config.tapes,RadixZeroFill.input,
      NativeSignedReturnClean.header,Tapes.append,Fin.addCases]

private theorem output_payload (v : Tapes t 2) (p : Fin 4 → Fin t) (hp : Function.Injective p)
    (ws : List Word) (current target : ℕ) (ls : List Bool)
    (hc : v.head (p 1)=1 ∧ v.tape (p 1)=RadixZeroFill.encodedBinary (bits current))
    (ht : v.head (p 2)=1 ∧ v.tape (p 2)=RadixZeroFill.encodedBinary (bits target))
    (hl : v.head (p 3)=1 ∧ v.tape (p 3)=RadixZeroFill.encodedBinary ls) :
    SharedBank.payload (NativeSignedGapPromoteHeadersReturn.output ws current target ls) ports =
      SharedBank.payload (setTape v (p 0)
        (word (ws.map (NativeSignedGapPromoteWord.result (target-current)))) 0) p := by
  have h1 : p 1≠p 0 := fun h => (by decide : (1:Fin 4)≠0) (hp h)
  have h2 : p 2≠p 0 := fun h => (by decide : (2:Fin 4)≠0) (hp h)
  have h3 : p 3≠p 0 := fun h => (by decide : (3:Fin 4)≠0) (hp h)
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [ports,h1,h2,h3,hc.1,hc.2,ht.1,ht.2,hl.1,hl.2,
      NativeSignedGapPromoteHeadersReturn.output,NativeSignedGapPromoteHeadersReturn.returned,
      NativeSignedGapPromoteHeadersReturn.exponents,setTape,CountedLoopHeaderClean.bank,
      NativeSignedGapPromoteReturn.output,Tapes.append,Fin.addCases]

private theorem outside_frame (v : Tapes t 2) (p : Fin 4 → Fin t) (g : ℤ → Fin 6) :
    SharedBank.strip v p=SharedBank.strip (setTape v (p 0) g 0) p := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases hi : ∃ j,p j=i
  all_goals simp only [hi,↓reduceIte]
  all_goals
    have hne : i≠p 0 := fun h => hi ⟨0,h.symm⟩
    simp [setTape,hne]

theorem one_runs (v : Tapes t 2) (p : Fin 4 → Fin t) (hp : Function.Injective p)
    (ws : List Word) (current target : ℕ) (hle : current≤target)
    (hd : ∀ w∈ws,target-current≤w.length) (hn : ws≠[]) (ls : List Bool)
    (hlen : Counter.value ls=volume ws) (hcanonical : GrowingCounterData.Canonical ls)
    (hs : v.head (p 0)=0 ∧ v.tape (p 0)=word ws)
    (hc : v.head (p 1)=1 ∧ v.tape (p 1)=RadixZeroFill.encodedBinary (bits current))
    (ht : v.head (p 2)=1 ∧ v.tape (p 2)=RadixZeroFill.encodedBinary (bits target))
    (hl : v.head (p 3)=1 ∧ v.tape (p 3)=RadixZeroFill.encodedBinary ls) :
    HoareTime (one p hp) (fun z => z=ready v)
      (fun z => z=ready (setTape v (p 0)
        (word (ws.map (NativeSignedGapPromoteWord.result (target-current)))) 0))
      (130*volume ws+8*target+359) := by
  apply (CleanSubbank.realizes NativeSignedGapPromoteHeadersReturn.program ports p
    ports_injective hp _ _ _ _ _ (input_payload v p ws current target ls hs hc ht hl)
    (output_payload v p hp ws current target ls hc ht hl)
    (input_clean ws current target ls) (output_clean ws current target ls)
    (outside_frame v p _)
    (NativeSignedGapPromoteHeadersReturn.runs ws current target hle hd hn ls hlen hcanonical)).consequence
      (fun _ h => h) (fun _ h => h)
  exact NativeSignedGapPromoteHeadersReturn.cost_le ws current target hle

def compile (roles : Fin c → Fin t) (cur tar len : Fin t)
    (hp : ∀ j,Function.Injective (common (roles j) cur tar len)) :
    List (Fin c) → Σ n,Program (t+10) n 2
  | [] => ⟨1,skip _ _ (by omega)⟩
  | j::js => ⟨_,seq (one (common (roles j) cur tar len) (hp j)) (compile roles cur tar len hp js).2⟩

/-- All spectators use original true denominator descriptors; the gap is
physically constructed and erased in each literal promoter, while the shared
denominator ledger itself stays unchanged throughout this finite sequence. -/
theorem compile_runs (roles : Fin c → Fin t) (hinj : Function.Injective roles) (cur tar len : Fin t)
    (hp : ∀ j,Function.Injective (common (roles j) cur tar len))
    (ws : Fin c → List Word) (js : List (Fin c)) (hnd : js.Nodup) (v : Tapes t 2)
    (current target V : ℕ) (hle : current≤target) (ls : List Bool)
    (hd : ∀ j w,w∈ws j → target-current≤w.length) (hn : ∀ j,ws j≠[])
    (hv : ∀ j,volume (ws j)=V) (hlen : Counter.value ls=V)
    (hcanonical : GrowingCounterData.Canonical ls)
    (hcurrent : v.head cur=1 ∧ v.tape cur=RadixZeroFill.encodedBinary (bits current))
    (htarget : v.head tar=1 ∧ v.tape tar=RadixZeroFill.encodedBinary (bits target))
    (hlength : v.head len=1 ∧ v.tape len=RadixZeroFill.encodedBinary ls)
    (hsource : ∀ j∈js,v.head (roles j)=0 ∧ v.tape (roles j)=word (ws j)) :
    HoareTime (compile roles cur tar len hp js).2 (fun z => z=ready v)
      (fun z => z=ready (execute roles
        (fun j => word ((ws j).map (NativeSignedGapPromoteWord.result (target-current)))) js v))
      (js.length*(130*V+8*target+360)) := by
  induction js generalizing v with
  | nil =>
    simpa only [compile,execute,List.length_nil,Nat.zero_mul] using
      (skip_hoare (a:=2) (by omega : 0<t+10) (ready v))
  | cons j js ih =>
    obtain ⟨hj,hjs⟩ := List.nodup_cons.mp hnd
    have h0 := one_runs v (common (roles j) cur tar len) (hp j) (ws j) current target hle
      (hd j) (hn j) ls (by rw [hv];exact hlen) hcanonical (hsource j (by simp))
      hcurrent htarget hlength
    rw [hv j] at h0
    have hc : cur≠roles j := by
      intro he
      have h : (1:Fin 4)=0 := hp j (by change cur=roles j;exact he)
      exact (by decide : (1:Fin 4)≠0) h
    have ht : tar≠roles j := by
      intro he
      have h : (2:Fin 4)=0 := hp j (by change tar=roles j;exact he)
      exact (by decide : (2:Fin 4)≠0) h
    have hl : len≠roles j := by
      intro he
      have h : (3:Fin 4)=0 := hp j (by change len=roles j;exact he)
      exact (by decide : (3:Fin 4)≠0) h
    have htail := ih hjs (setTape v (roles j)
      (word ((ws j).map (NativeSignedGapPromoteWord.result (target-current)))) 0)
      (by simpa only [setTape,Function.update_of_ne hc] using hcurrent)
      (by simpa only [setTape,Function.update_of_ne ht] using htarget)
      (by simpa only [setTape,Function.update_of_ne hl] using hlength)
      (by
        intro k hk
        have hne : roles k≠roles j := by
          intro he
          have he' := hinj he
          subst k
          exact hj hk
        simpa only [setTape,Function.update_of_ne hne] using hsource k (List.mem_cons_of_mem j hk))
    exact (h0.seq htail).consequence (fun _ h => h) (fun _ h => h)
      (by simp only [List.length_cons,Nat.add_mul]; omega)

theorem spectators_runs (roles : Fin c → Fin t) (hinj : Function.Injective roles) (cur tar len : Fin t)
    (hp : ∀ j,Function.Injective (common (roles j) cur tar len)) (selected : Fin c)
    (ws : Fin c → List Word) (v : Tapes t 2) (current target V : ℕ) (hle : current≤target) (ls : List Bool)
    (hd : ∀ j w,w∈ws j → target-current≤w.length) (hn : ∀ j,ws j≠[])
    (hv : ∀ j,volume (ws j)=V) (hlen : Counter.value ls=V)
    (hcanonical : GrowingCounterData.Canonical ls)
    (hcurrent : v.head cur=1 ∧ v.tape cur=RadixZeroFill.encodedBinary (bits current))
    (htarget : v.head tar=1 ∧ v.tape tar=RadixZeroFill.encodedBinary (bits target))
    (hlength : v.head len=1 ∧ v.tape len=RadixZeroFill.encodedBinary ls)
    (hsource : ∀ j,j≠selected → v.head (roles j)=0 ∧ v.tape (roles j)=word (ws j)) :
    HoareTime (compile roles cur tar len hp (spectatorList selected)).2 (fun z => z=ready v)
      (fun z => z=ready (execute roles
        (fun j => word ((ws j).map (NativeSignedGapPromoteWord.result (target-current))))
          (spectatorList selected) v))
      ((spectatorList selected).length*(130*V+8*target+360)) :=
  compile_runs roles hinj cur tar len hp ws _ (spectatorList_nodup selected) v current target V hle ls
    hd hn hv hlen hcanonical hcurrent htarget hlength
    (fun j hj => hsource j ((spectatorList_mem selected j).mp hj))

/-- Every listed role has the exact promoted word and normalized head at
the finite-family endpoint. Roles outside the list retain their literal data. -/
theorem execute_slot (roles : Fin c → Fin t) (hinj : Function.Injective roles)
    (words : Fin c → ℤ → Fin 6) (js : List (Fin c)) (v : Tapes t 2) (j : Fin c) :
    (execute roles words js v).head (roles j)=(if j∈js then 0 else v.head (roles j)) ∧
      (execute roles words js v).tape (roles j)=(if j∈js then words j else v.tape (roles j)) := by
  induction js generalizing v with
  | nil => simp [execute]
  | cons k js ih =>
    have h := ih (setTape v (roles k) (words k) 0)
    by_cases hj : j∈js
    · simpa only [execute,List.mem_cons,hj,or_true,ite_true] using h
    · by_cases hk : j=k
      · subst k
        simpa [execute,hj,setTape] using h
      · have hne : roles j≠roles k := fun he => hk (hinj he)
        simpa [execute,hj,hk,setTape,Function.update_of_ne hne] using h

theorem spectators_endpoint (roles : Fin c → Fin t) (hinj : Function.Injective roles)
    (selected : Fin c) (words : Fin c → ℤ → Fin 6) (v : Tapes t 2) :
    (execute roles words (spectatorList selected) v).head (roles selected)=v.head (roles selected) ∧
      (execute roles words (spectatorList selected) v).tape (roles selected)=v.tape (roles selected) ∧
      ∀ j,j≠selected →
        (execute roles words (spectatorList selected) v).head (roles j)=0 ∧
        (execute roles words (spectatorList selected) v).tape (roles j)=words j := by
  have hs := CompactComplexSpectatorPromoteFamily.selected_frame roles hinj selected words v
  refine ⟨hs.1,hs.2,?_⟩
  intro j hj
  simpa [hj] using execute_slot roles hinj words (spectatorList selected) v j

end
end IntegerMultBounds.Machine.CompactComplexSpectatorTargetFamily
