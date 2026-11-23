module

public import IntegerMultBounds.MathlibTM2.M6.BitIdleDispatchSeed

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Node Cover.Fallback
open Shared50ModularControl (prime)

private def skipBits {T Q A : ℕ} {U : Type} (src : Fin T) : ℕ → Act T Q A U
  | 0 => .done
  | n+1 => .pop (.rt src) (fun u _ => u) (skipBits src n)

private theorem skipBits_run {T Q A : ℕ} {U : Type} (src : Fin T) (n : ℕ)
    (v : HS T Q A U) (S : Stacks T A) :
    (skipBits src n).run (mk v S) = mk v {S with R := Function.update S.R src ((S.R src).drop n)} := by
  induction n generalizing S with
  | zero => simp [skipBits,run_done]
  | succ n ih =>
    simp only [skipBits,Action.run,mk_var,mk_stk,get_rt,update_rt,store_mk]
    rw [ih]
    simp

private theorem scaledWidthWord {A : ℕ} (x : ℕ) (pos : 0 < x) :
    (binSyms (64*x).size (64*x) : List (Fin (A+4))) =
      List.replicate 6 (bitSymbol false) ++ binSyms x.size x := by
  have size := Nat.size_shiftLeft pos.ne' 6
  rw [Nat.shiftLeft_eq,Nat.mul_comm x] at size
  change (64*x).size = x.size+6 at size
  rw [size,Nat.add_comm x.size 6,binSyms_append,← binSyms_mod 6]
  simp [show 2^6 = 64 by decide,binSyms_zero_right]

/-- Read the quotient of a positive aligned width by 64 into a unary clock.
The six low bits are known zeros, so restoring the width needs no saved tape. -/
private theorem alignedWidthUnary {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    {src dst work tmp saved : Fin T} (regs : [src,dst,work,tmp,saved].Nodup) :
    ∃ code : Pr P T Q prime U, ∀ x, 0 < x → ∀ u (S : Stacks T prime),
      S.R src = binSyms (64*x).size (64*x) → S.R work = [] → S.R tmp = [] → S.R saved = [] →
      ∃ z n, Exec body code (mk u S) n (mk z {S with R := Function.update S.R dst (List.replicate x tick ++ S.R dst)}) ∧
        z.user = u.user ∧ n ≤ 6*x+11*x.size+8 := by
  refine ⟨(Prog.act (skipBits src 6)).seq ((toUnary src dst work tmp saved).seq
    (.act (pushN src (fun _ => bitSymbol false) 6 .done))),?_⟩
  intro x pos u S width hw ht hs
  rw [scaledWidthWord x pos] at width
  let D := {S with R := Function.update S.R src (binSyms x.size x)}
  have strip := Exec.act (body := body) (skipBits src 6) (mk u S)
  rw [skipBits_run,width,List.drop_append_of_le_length (by simp),List.drop_replicate] at strip
  simp only [Nat.sub_self,List.replicate_zero,List.nil_append] at strip
  have distinct := regs
  regs_ne distinct
  obtain ⟨v,m,user,time,convert⟩ := toUnary_exec_linear body regs (Nat.lt_size_self x) u D
    (Function.update_self ..) ((Function.update_of_ne ‹src ≠ work›.symm ..).trans hw)
    ((Function.update_of_ne ‹src ≠ tmp›.symm ..).trans ht) ((Function.update_of_ne ‹src ≠ saved›.symm ..).trans hs)
  have restore := Exec.act (body := body) (pushN src (fun _ => bitSymbol false) 6 .done)
    (mk v {D with R := Function.update D.R dst (List.replicate x tick ++ D.R dst)})
  rw [pushN_run,run_done] at restore
  refine ⟨v,1+(m+1),(strip.seq (convert.seq restore)).cast rfl ?_,user,by omega⟩
  congr 2
  funext j
  by_cases h : j = src
  · subst j; simp [D,width,Function.update_of_ne ‹src ≠ dst›]
  · simp [D,Function.update_of_ne h,Function.update_of_ne ‹src ≠ dst›.symm,Function.update_apply]

/-- A single program makes both remainder clocks from the descriptor width.
The shorter clock omits the leading tick used by the comparison loop. -/
theorem idleDispatchClocks {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (r : Fin 7 ↪ Fin T) :
    ∃ code : Pr P T Q prime U, ∀ w u (S : Stacks T prime),
      S.R (r 0) = binSyms (64*(w+1)).size (64*(w+1)) → (∀ i, i ≠ 0 → S.R (r i) = []) →
      let clocks := Function.update (Function.update S.R (r 1) (List.replicate (w+1) blank)) (r 2) (List.replicate w blank)
      ∃ z n, Exec body code (mk u S) n (mk z {S with R := clocks}) ∧ z.user = u.user ∧
        CleanupBound S {S with R := clocks} n (18*(w+1)+11*(w+1).size+17) := by
  obtain ⟨read,run⟩ := alignedWidthUnary (src := r 0) (dst := r 3) (work := r 4) (tmp := r 5) (saved := r 6)
    body (by simp [r.injective.eq_iff])
  refine ⟨read.seq ((moveR (r 3) (r 1) (fun _ => blank)).seq
    ((bcopy (r 1) (r 2) (r 4) (r 5)).seq (.act (skipBits (r 2) 1)))),?_⟩
  intro w u S width empty clocks
  obtain ⟨v,m,readWidth,user,time⟩ := run (w+1) (Nat.succ_pos _) u S width
    (empty 4 (by decide)) (empty 5 (by decide)) (empty 6 (by decide))
  rw [empty 3 (by decide),List.append_nil] at readWidth
  let ticks := {S with R := Function.update S.R (r 3) (List.replicate (w+1) tick)}
  obtain ⟨y,same,move⟩ := moveR_exec body (r 3) (r 1) (r.injective.ne (by decide)) (fun _ => blank) v ticks
  let D := {S with R := Function.update S.R (r 1) (List.replicate (w+1) blank)}
  have moved : movedR ticks.R (r 3) (r 1) (fun _ => blank) (ticks.R (r 3)) = D.R := by
    funext j
    by_cases h : j = r 1
    · subst j; simp [D,ticks,movedR,r.injective.eq_iff,empty]
    · by_cases g : j = r 3
      · subst j; simp [D,ticks,movedR,h,empty]
      · simp [D,ticks,movedR,h,g]
  rw [moved] at move
  simp only [ticks,Function.update_self,List.length_replicate] at move
  obtain ⟨z,done,copy⟩ := bcopy_exec (a := r 1) (c := r 2) (t₁ := r 4) (t₂ := r 5)
    body (by simp [r.injective.eq_iff]) y D (by simp [D,r.injective.eq_iff,empty])
    (by simp [D,r.injective.eq_iff,empty])
  have long : D.R (r 1) = List.replicate (w+1) blank := Function.update_self ..
  have vacant : D.R (r 2) = [] := by simp [D,r.injective.eq_iff,empty]
  rw [long,vacant,List.append_nil,List.length_replicate] at copy
  let G := {D with R := Function.update D.R (r 2) (List.replicate (w+1) blank)}
  have drop := Exec.act (body := body) (skipBits (r 2) 1) (mk z G)
  simp only [skipBits_run,G,Function.update_self,List.drop_replicate,Nat.add_sub_cancel,
    Function.update_idem] at drop
  refine ⟨z,_,readWidth.seq (move.seq (copy.seq drop)),done.trans (same.trans user),?_⟩
  intro js distinct
  have a := prependedWordCharge S (r 1) (List.replicate (w+1) blank) js distinct
  have b := prependedWordCharge D (r 2) (List.replicate w blank) js distinct
  simp only [empty 1 (by decide),List.append_nil,List.length_replicate] at a
  simp only [vacant,List.append_nil,List.length_replicate] at b
  change tapeCharge cleanupWeight js D ≤ _ at a
  change tapeCharge cleanupWeight js {S with R := clocks} ≤ tapeCharge cleanupWeight js D+2*w at b
  change _ + tapeCharge cleanupWeight js {S with R := clocks} ≤ tapeCharge cleanupWeight js S+_
  omega

/-- Initialize the remainder bank directly from the aligned width and the
four persistent master words. Both clocks remain available after the load. -/
theorem loadRemainderFromWidth {P U : Type} {H N T Q : ℕ} (body : P → Pr P T Q prime U)
    (origin : Fin H → Option (Fin (72+N))) (src : Fin (142081+2) ↪ Fin H)
    (bank : Fin H ↪ Fin T) (r : Fin 11 ↪ Fin T) (apart : ∀ j i, bank j ≠ r i) :
    ∃ code : Pr P T Q prime U, ∀ w W L cutoff u (S : Stacks T prime),
      S.R (r 0) = binSyms (64*(w+1)).size (64*(w+1)) →
      (∀ i : Fin 7, i ≠ 0 → S.R (r (i.castAdd 4)) = []) →
      S.R (r 7) = binSyms (prime^(w+1)).size (prime^(w+1)) →
      S.R (r 8) = binSyms 1 1 → S.R (r 9) = binSyms W.size W → S.R (r 10) = binSyms L cutoff →
      (∀ j, (∀ i, src i ≠ j) → S.L (bank j) = [] ∧ S.R (bank j) = []) →
      let seed := remainderDispatchSeed origin w W L cutoff
      let clocks := Function.update (Function.update S.R (r 1) (List.replicate (w+1) blank)) (r 2) (List.replicate w blank)
      ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n ((18*(w+1)+11*(w+1).size+17)+(H*(8*((prime^(w+1)).size+W.size+2*w+L)+53)+1)) ∧
        (∀ j, (∀ i, src i ≠ j) → F.L (bank j) = seed.L j ∧ F.R (bank j) = seed.R j) ∧
        (∀ i, F.L (bank (src i)) = S.L (bank (src i)) ∧ F.R (bank (src i)) = S.R (bank (src i))) ∧
        ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = clocks j := by
  let fields : Fin 6 → Fin 11 := ![7,8,9,1,2,10]
  let small := (Fin.castAddEmb 4 (n := 7)).trans r
  obtain ⟨clock,make⟩ := idleDispatchClocks body small
  obtain ⟨load,fill⟩ := loadRemainderDispatchSeed body origin src bank (r ∘ fields) (r 4) (r 5)
    (fun j i => apart j _) (by
      intro i j
      have a : fields i ≠ 4 := by fin_cases i <;> decide
      have b : fields i ≠ 5 := by fin_cases i <;> decide
      simp [List.nodup_cons,Function.comp_apply,r.injective.eq_iff,a,b,apart,Ne.symm (apart j _)])
  refine ⟨clock.seq load,?_⟩
  intro w W L cutoff u S width empty radix unit spectator cut fresh seed clocks
  obtain ⟨v,m,run,user,paid⟩ := make w u S width empty
  let D := {S with R := clocks}
  have outside {j} (a : j ≠ r 1) (b : j ≠ r 2) : D.R j = S.R j := by simp [D,clocks,a,b]
  have bankEq j := outside (apart j 1) (apart j 2)
  have words (i) : D.R ((r ∘ fields) i) = idleDispatchWord w W L cutoff (idleSeedPorts i).val := by
    fin_cases i <;> simp [D,clocks,fields,idleDispatchWord,idleSeedPorts,r.injective.eq_iff,radix,unit,spectator,cut]
  obtain ⟨z,F,n,exec,same,bill,ready,live,frame⟩ := fill w W L cutoff v D words
    (fun j off => ⟨(fresh j off).1,(bankEq j).trans (fresh j off).2⟩)
    ((outside (r.injective.ne (by decide)) (r.injective.ne (by decide))).trans (empty 4 (by decide)))
    ((outside (r.injective.ne (by decide)) (r.injective.ne (by decide))).trans (empty 5 (by decide)))
  exact ⟨z,F,m+n,run.seq exec,same.trans user,fun js nd => by
          have a := paid js nd
          have b := bill js nd
          change m+tapeCharge cleanupWeight js D ≤ _ at a
          unfold cleanupWeight at a
          omega,
        ready,fun i => ⟨(live i).1,(live i).2.trans (bankEq _)⟩,frame⟩

/-- Execute the embedded child once its private seed is loaded and its input fan preserved. -/
theorem execPreparedRemainder {P A U : Type} {H T Q V : ℕ}
    (body : P → Pr P H Q prime U) (program : Pr P H Q prime U) (label : P → A)
    (host : A → Pr A T Q prime U) (bank : Fin H ↪ Fin T)
    (installed : ∀ f, host (label f) = embProg bank label (body f))
    {src dst seed effect price} (child : PackedPieceHandoffWithCharge cleanupWeight V effect
      body program src dst seed price) {x v} {S D : Stacks T prime}
    (words : ParentStageWords (fun i => src (i.castAdd 2)) src V x (embStk bank S))
    (fresh : ∀ j, (∀ i, src i ≠ j) → D.L (bank j) = seed.L j ∧ D.R (bank j) = seed.R j)
    (live : ∀ i, D.L (bank (src i)) = S.L (bank (src i)) ∧ D.R (bank (src i)) = S.R (bank (src i))) :
    ∃ q G t y, Exec host (embProg bank label program) (mk v D) t (mk q G) ∧ q.user = v.user ∧
      ParentStageWords (fun i => dst (i.castAdd 2)) dst V y (embStk bank G) ∧ effect x y ∧
      CleanupBound D G t price ∧
      ∀ j, (∀ i, bank i ≠ j) → G.L j = D.L j ∧ G.R j = D.R j := by
  have rows : ParentStageWords (fun i => src (i.castAdd 2)) src V x (embStk bank D) := by
    constructor
    · intro i
      exact (live _).1.trans (words.left i)
    · intro i
      exact (live _).2.trans (words.right i)
    · intro j k
      simpa only [embStk,Function.comp_apply,(live _).1,(live _).2] using words.controls j k
  obtain ⟨z,F,b,y,run,bill,same,out,result⟩ := child x (embDn bank v) (embStk bank D) rows fresh
  obtain ⟨q,G,lifted,_,userEq,view,frame⟩ := exec_emb bank.injective installed run v rfl D rfl
  rw [← view] at out bill
  exact ⟨q,G,b,y,lifted,userEq.trans same,out,result,CleanupBound.place bank frame bill,frame⟩

/-- Load the remainder headers from the caller, then invoke its installed packed child. -/
theorem callRemainderFromWidth {P A U : Type} {H N T Q : ℕ}
    (body : P → Pr P H Q prime U) (entry : P) (label : P → A)
    (host : A → Pr A T Q prime U) (bank : Fin H ↪ Fin T)
    (installed : ∀ f, host (label f) = embProg bank label (body f))
    (origin : Fin H → Option (Fin (72+N))) (src dst : Fin (142081+2) ↪ Fin H)
    (r : Fin 11 ↪ Fin T) (apart : ∀ j i, bank j ≠ r i) :
    ∃ code : Pr A T Q prime U, ∀ w W L cutoff V effect price,
      PackedPieceHandoffWithCharge cleanupWeight V effect body (body entry) src dst
        (remainderDispatchSeed origin w W L cutoff) price →
      ∀ x u (S : Stacks T prime),
      ParentStageWords (fun i => src (i.castAdd 2)) src V x (embStk bank S) →
      S.R (r 0) = binSyms (64*(w+1)).size (64*(w+1)) →
      (∀ i : Fin 7, i ≠ 0 → S.R (r (i.castAdd 4)) = []) →
      S.R (r 7) = binSyms (prime^(w+1)).size (prime^(w+1)) →
      S.R (r 8) = binSyms 1 1 → S.R (r 9) = binSyms W.size W → S.R (r 10) = binSyms L cutoff →
      (∀ j, (∀ i, src i ≠ j) → S.L (bank j) = [] ∧ S.R (bank j) = []) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        ParentStageWords (fun i => dst (i.castAdd 2)) dst V y (embStk bank F) ∧ effect x y ∧
        CleanupBound S F t ((18*(w+1)+11*(w+1).size+17)+
          (H*(8*((prime^(w+1)).size+W.size+2*w+L)+53)+1)+(price+2)) := by
  obtain ⟨load,prepare⟩ := loadRemainderFromWidth host origin src bank r apart
  refine ⟨load.seq (.call (label entry)),?_⟩
  intro w W L cutoff V effect price child x u S words width empty radix unit spectator cut fresh
  obtain ⟨v,D,a,exec,user,paid,seed,live,_⟩ := prepare w W L cutoff u S width empty radix unit spectator cut fresh
  obtain ⟨q,G,b,y,run,same,out,result,charge,_⟩ :=
    execPreparedRemainder body (body entry) label host bank installed child words seed live (v := v)
  rw [← installed] at run
  refine ⟨q,G,_,y,exec.seq (Exec.call run),same.trans user,out,result,?_⟩
  intro js nd
  have h := paid.seq charge js nd
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
