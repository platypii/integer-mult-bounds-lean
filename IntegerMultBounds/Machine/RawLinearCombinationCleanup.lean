import IntegerMultBounds.Machine.RadixLinearCombinationBootstrap
import IntegerMultBounds.Machine.MarkedBinaryCleanup

/-! Erase every physically copied radix-expression source while retaining the
actual result. This cleanup is linear in word width, with no value conversion. -/
namespace IntegerMultBounds.Machine.RawLinearCombinationCleanup
noncomputable section
open MarkedWordCleanup (one word marked empty)
open RadixLinearCombinationRefresh (Expr)
open RadixDigits
variable {c q t r machineStates B : ℕ}

def prepend (M : Program t machineStates q) (r : ℕ) :=
  Placement.placed M (finAddFlip : Fin (t+r) ≃ Fin (r+t))

theorem prepend_runs (M : Program t machineStates q) (v w : Tapes t q) (frame : Tapes r q)
    (h : HoareTime M (fun x => x=v) (fun x => x=w) B) :
    HoareTime (prepend M r) (fun x => x=frame.append v) (fun x => x=frame.append w) B := by
  let e : Fin (t+r) ≃ Fin (r+t) := finAddFlip
  have ha : Placement.active e (frame.append v)=v := by
    cases v; simp [Placement.active,e,Tapes.append,finAddFlip_apply_castAdd]
  have hb : Placement.active e (frame.append w)=w := by
    cases w; simp [Placement.active,e,Tapes.append,finAddFlip_apply_castAdd]
  have hf : Placement.extra e (frame.append v)=Placement.extra e (frame.append w) := by
    cases frame; simp [Placement.extra,e,Tapes.append,finAddFlip_apply_natAdd]
  apply (Placement.hoare_at h e (frame.append v) ha).consequence (fun _ h => h) ?_ le_rfl
  rintro x ⟨z,rfl,rfl⟩
  rw [Placement.replace,hf]
  exact (congrArg (fun small => Placement.combine e small (Placement.extra e (frame.append z))) hb.symm).trans
    (Placement.view e (frame.append z))

theorem marked_radix (xs : List (Fin q)) :
    HoareTime (MarkedBinaryCleanup.program (q:=q))
      (fun v => v=one (marked (xs.map digitSymbol)) 1)
      (fun v => v=one (fun _ => blank) 0) (2*xs.length+4) := by
  have hn : ∀ x ∈ xs.map digitSymbol,x≠blank := by
    intro x hx
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hx
    simp [digitSymbol,blank,Fin.ext_iff]
  have hr := Rewind.rewind_hoare (separator : Fin (q+4)) empty (xs.length+1) (xs.length+1)
    (by intro j hj; simp [empty,show (xs.length:ℤ)+1-j≠0 by omega,blank,separator,Fin.ext_iff])
    (by simp [empty])
  have hr' : HoareTime (Rewind.program (separator : Fin (q+4)))
      (fun v => v=one empty (1+xs.length)) (fun v => v=one empty 0) (xs.length+1) := by
    simpa only [Rewind.cfg,Config.tapes,one,sub_self,Nat.cast_add,Nat.cast_one,add_comm] using hr
  have hc := MarkedWordCleanup.clear_hoare (xs.map digitSymbol) hn
  simp only [List.length_map] at hc
  exact ((hc.seq hr').seq (MarkedWordCleanup.unmark_hoare [])).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

def clean (e : Expr c) (zs : List (Fin q)) :=
  (one (word (zs.map digitSymbol)) 0).append (RadixLinearCombinationBootstrap.empty (RadixLinearCombination.AuxTapes e.erase))

def states : Expr c → ℕ
  | .term _ _ => 4
  | .add l r => states l+states r

def program : (e : Expr c) → Program (RadixLinearCombinationRefresh.Size e) (states e) q
  | .term _ _ => prepend MarkedBinaryCleanup.program 1
  | .add l r => prepend (FamilyPlacementAlphabet.sequence (program l) (program r)) 1

def cost : Expr c → ℕ → ℕ
  | .term _ _,b => 2*b+4
  | .add l r,b => cost l b+cost r b+1

theorem clean_nil (e : Expr c) : clean (q:=q) e []=RadixLinearCombinationBootstrap.empty (RadixLinearCombinationRefresh.Size e) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;> simp [one,word,RadixLinearCombinationBootstrap.empty,putWord]

theorem empty_append (m n : ℕ) :
    (RadixLinearCombinationBootstrap.empty (q:=q) m).append (RadixLinearCombinationBootstrap.empty n)=
      RadixLinearCombinationBootstrap.empty (m+n) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;> simp [RadixLinearCombinationBootstrap.empty]

theorem runs (e : Expr c) (xs : ℕ → List (Fin q)) (zs : List (Fin q)) (b : ℕ)
    (hw : ∀ i,(xs i).length=b) :
    HoareTime (program e) (fun v => v=RadixLinearCombination.bank e.erase xs zs)
      (fun v => v=clean e zs) (cost e b) := by
  induction e generalizing zs with
  | term i r =>
    have h := prepend_runs MarkedBinaryCleanup.program _ _ (one (word (zs.map digitSymbol)) 0) (marked_radix (xs i.val))
    rw [hw] at h
    exact h
  | add l r hl hr =>
    have h := FamilyPlacementAlphabet.sequence_hoare (hl []) (hr [])
    rw [clean_nil,clean_nil,empty_append] at h
    exact prepend_runs _ _ _ (one (word (zs.map digitSymbol)) 0) h

end
end IntegerMultBounds.Machine.RawLinearCombinationCleanup
