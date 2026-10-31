module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawReplicaPayload
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval

/-! Ambient consecutive RHS lines produce exactly the supplier's packed-list
payload, with original ambient coordinates and a preserved borrowed suffix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

private theorem range_getD_flatMap {α β : Type} (xs : List α) (d : α) (f : α → List β) :
    (List.range xs.length).flatMap (fun i => f (xs.getD i d)) = xs.flatMap f := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simpa [List.range_succ_eq_map,List.flatMap_map] using congrArg (f x ++ ·) ih

theorem replicaAmbientWords_list {s : ℕ} (Fs : List (ZMod s → GaussianInt)) :
    replicaAmbientWords Fs.length (fun i => Fs.getD i 0) = Fs.flatMap (chirpLine s) :=
  range_getD_flatMap Fs 0 (chirpLine s)

theorem replicaPayload_list {s : ℕ} (Fs : List (ZMod s → GaussianInt)) (p L : ℕ) (hfit : p+L ≤ s) :
    (List.range Fs.length).flatMap (cellSourceRows L (fun _ => (p : ZMod s)) (fun i => Fs.getD i 0)) =
      (Fs.map (packedInterval p L)).flatten := by
  have hrow (i : ℕ) : cellSourceRows L (fun _ => (p : ZMod s)) (fun j => Fs.getD j 0) i =
      packedInterval p L (Fs.getD i 0) := by
    simpa only [cellSourceRows,packedInterval] using (ambientLine_window (Fs.getD i 0) p L hfit).symm
  change (List.range Fs.length).flatMap (fun i => cellSourceRows L (fun _ => (p : ZMod s)) (fun j => Fs.getD j 0) i) = _
  simp_rw [hrow]
  rw [range_getD_flatMap]
  rfl

theorem replicaPayload_exec_within {s : ℕ} (Fs : List (ZMod s → GaussianInt))
    (B w p L : ℕ) (hcount : Fs.length = B+1) (hwpos : 0 < w) (hLpos : 0 < L) (hfit : p+L ≤ s)
    (borrowed : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hw : (S.R 94).length = w) (hs : (S.R 97).length = s) (hp : (S.R 111).length = p)
    (hL : (S.R 102).length = L) (hB : (S.R 116).length = Fs.length)
    (hsrc : S.R 110 = cstream A w (Fs.flatMap (chirpLine s))++borrowed)
    (hdst : S.R 93 = []) (hblank : ∀ k : Fin 117, k.val < 13 → S.R k = [])
    (hfresh : ∀ k ∈ [(91 : Fin 117),92], S.R k = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ rawReplicaPayloadCost w s p L B ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+500*(Fs.length*s*w)) depth
        rawReplicaPayload (mk v S) n (mk v' {S with R := (Function.update S.R 93
          (cstream A w (Fs.map (packedInterval p L)).flatten))}) := by
  have hsource : S.R 110 = cstream A w (replicaAmbientWords (B+1) (fun i => Fs.getD i 0))++borrowed := by
    rw [← hcount,replicaAmbientWords_list]
    exact hsrc
  obtain ⟨v',n,hu,hn,he⟩ := rawReplicaPayload_exec_within (body := body) w p L B (fun i => Fs.getD i 0)
    hwpos hLpos hfit borrowed v S hw hs hp hL (hB.trans hcount) hsource hblank hfresh depth
  rw [← hcount,replicaPayload_list Fs p L hfit,hdst,List.append_nil] at he
  exact ⟨v',n,hu,hn,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
