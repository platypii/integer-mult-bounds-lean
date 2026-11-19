module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecord

/-! Run the anchor on a queue of records, in sign-stream order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open M8 AtomSegment ActualAffineScaling
variable {T n f b W : ℕ} {P U : Type}
local instance : NeZero (modulus b) := ⟨(modulus_pos b).ne'⟩

abbrev Array (n f b W : ℕ) := FlatCoordinateStages.Array ((n+1)*f) b W

def Correct (input : Bool × Array n f b W) (out : Array n f b W) : Prop :=
  ∀ (x : Fin (n+1) → Fin f → ZMod (modulus b)) (j : Fin W),
    out (FlatCoordinateLayout.index (AtomOps.refine
      (Fin.cons (fun k => if input.1 then -x 0 k else x 0 k) (fun i => x i.succ))) j) =
      input.2 (FlatCoordinateLayout.index (AtomOps.refine x) j)

def cost (n T f b W : ℕ) (negative : Bool) :=
  let K := (modulus b)^((n+1)*f)*W
  10*K+10+(chainConst (anchorOps n negative)*f*K+1)*(size n+T+5)+2*T+8

def loop (n : ℕ) (r : Fin 6 ↪ Fin T) :=
  Prog.loop (·.flag) (.seq (program (P := P) (U := U) n r) (.act (peekR (port n r 4))))

def scan (n : ℕ) (r : Fin 6 ↪ Fin T) :=
  Prog.seq (.act (peekR (port n r 4))) (loop (P := P) (U := U) n r)

theorem scan_runs (r : Fin 6 ↪ Fin T) (hf : 0 < f) (hb : 0 < b) (hW : 0 < W)
    (body : P → Pr P _ _ prime U) (inputs : List (Bool × Array n f b W))
    (u : HS _ _ prime U) (S : Stacks _ prime) (tail : List (Fin (prime+4)))
    (ready : Ready n f b W S) (count : (S.R (port n r 0)).length = (modulus b)^((n+1)*f)*W)
    (queue : S.R (port n r 1) = inputs.flatMap (fun a => payloadWord a.2) ++ tail)
    (saved : S.R (port n r 2) = []) (tmp : S.R (port n r 3) = [])
    (signs : S.R (port n r 4) = inputs.map (fun a => bitSymbol a.1)) :
    ∃ outs z F t, inputs.Forall₂ Correct outs ∧ Exec body (scan n r) (mk u S) t (mk z F) ∧
      t ≤ (inputs.map (fun a => cost n T f b W a.1 + 2)).sum + 2 ∧ Ready n f b W F ∧
      z.user = u.user ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L (port n r 1) = S.L (port n r 1) ∧
      ∀ j : Fin T, F.R (Fin.natAdd (size n) j) =
        if j = r 5 then (outs.flatMap payloadWord).reverse ++ S.R (port n r 5)
        else if j = r 4 then [] else if j = r 1 then tail else S.R (Fin.natAdd (size n) j) := by
  have main (v : HS _ _ prime U) (flag : v.flag = inputs.head?.isSome) :
      ∃ outs z F t, inputs.Forall₂ Correct outs ∧ Exec body (loop n r) (mk v S) t (mk z F) ∧
        t ≤ (inputs.map (fun a => cost n T f b W a.1 + 2)).sum + 1 ∧ Ready n f b W F ∧
        z.user = v.user ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L (port n r 1) = S.L (port n r 1) ∧
        ∀ j : Fin T, F.R (Fin.natAdd (size n) j) =
          if j = r 5 then (outs.flatMap payloadWord).reverse ++ S.R (port n r 5)
          else if j = r 4 then [] else if j = r 1 then tail else S.R (Fin.natAdd (size n) j) := by
    induction inputs generalizing v S with
    | nil =>
      refine ⟨[],v,S,1,.nil,.loop_false (by simpa using flag),by simp,ready,rfl,rfl,rfl,rfl,?_⟩
      intro j
      split_ifs <;> subst_vars <;> simp_all [port]
    | cons a xs ih =>
      obtain ⟨a',z,F,t,run,rf,hu,hi,ho,left,ht,frame,act⟩ := runs r a.1 hf hb hW a.2 body v S
        (xs.flatMap (fun a => payloadWord a.2) ++ tail) (xs.map (fun a => bitSymbol a.1))
        ready count (by simpa [List.append_assoc] using queue) saved tmp (by simpa using signs)
      have slot (i : Fin 6) := frame (r i)
      simp only [r.injective.eq_iff] at slot
      have sig : F.R (port n r 4) = xs.map (fun a => bitSymbol a.1) := by simpa using slot 4
      have peek := Exec.act (body := body) (peekR (port n r 4)) (mk z F)
      rw [peekR_run,sig] at peek
      obtain ⟨os,y,G,c,ok,rest,ct,rg,yu,yi,yo,yl,result⟩ := ih F rf
        (by simpa [port,slot] using count) (by simpa using slot 1) (by simpa [port,slot] using saved)
        (by simpa [port,slot] using tmp) sig {z with flag := (xs.map (fun a => bitSymbol (a := prime) a.1)).head?.isSome}
        (by cases xs <;> rfl)
      refine ⟨a'::os,y,G,_,.cons act ok,.loop_true (by simpa using flag) (.seq run peek) rest,
        ?_,rg,yu.trans hu,yi.trans hi,yo.trans ho,yl.trans left,?_⟩
      · simp only [List.map_cons,List.sum_cons]
        change t ≤ cost n T f b W a.1 at ht
        omega
      · intro j
        rw [result,frame]
        by_cases h : j = r 5 <;> simp [h,List.reverse_append,List.append_assoc]
        rw [frame j]
        split_ifs <;> rfl
  have peek := Exec.act (body := body) (peekR (port n r 4)) (mk u S)
  rw [peekR_run,signs] at peek
  obtain ⟨os,z,F,c,h,run,ct,rf,hu,hi,ho,left,result⟩ := main {u with flag := (inputs.map (fun a => bitSymbol (a := prime) a.1)).head?.isSome} (by
    change (inputs.map (fun a => bitSymbol (a := prime) a.1)).head?.isSome = _
    cases inputs <;> rfl)
  exact ⟨os,z,F,_,h,.seq peek run,by omega,rf,hu,hi,ho,left,result⟩

end
end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
