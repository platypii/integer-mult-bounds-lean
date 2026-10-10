import IntegerMultBounds.Machine.EqualWordReplace

/-! Physical simultaneous exchange of equal-length nonblank words, followed
by paid restoration of both heads. The full complementary tape exteriors are
retained. This supplies the bank exchange needed by endpoint corrections. -/
namespace IntegerMultBounds.Machine.EqualWordSwap
variable {a : ℕ}
open CopyWord (cfg)

def forward : Program 2 1 a where
  tapes_pos := by decide
  start := 0
  transition := fun _ symbols =>
    if symbols 0=blank then none
    else some (0,fun i => (if i=0 then symbols 1 else symbols 0,Move.right))

theorem forward_step (f g : ℤ → Fin (a+4)) (p q : ℤ) (h : f p≠blank) :
    step forward (cfg f g p q)=some
      (cfg (Function.update f p (g q)) (Function.update g q (f p)) (p+1) (q+1)) := by
  simp only [step,forward,cfg,h,↓reduceIte,Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply,eq_comm]

theorem forward_run (f g : ℤ → Fin (a+4)) (p q : ℤ)
    (xs ys : List (Fin (a+4))) (hlen : xs.length=ys.length)
    (hx : ∀ x∈xs,x≠blank) :
    run forward xs.length (cfg (putWord f p xs) (putWord g q ys) p q)=
      some (cfg (putWord f p ys) (putWord g q xs) (p+xs.length) (q+xs.length)) := by
  induction xs generalizing f g p q ys with
  | nil => cases ys <;> simp_all [run,putWord]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      rw [List.length_cons,add_comm,run_add,run_one,
        forward_step _ _ _ _ (by rw [putWord_head]; exact hx x (by simp))]
      simp only [Option.bind_some,putWord_head,putWord_cons]
      rw [←putWord_update_before _ (p+1) p y xs (by omega),Function.update_idem,
        ←putWord_update_before _ (q+1) q x ys (by omega),Function.update_idem,
        ih (Function.update f p y) (Function.update g q x) (p+1) (q+1) ys
          (by simpa using hlen) (fun z hz => hx z (by simp [hz]))]
      congr 2 <;> push_cast <;> ring

theorem forward_hoare (f g : ℤ → Fin (a+4)) (p q : ℤ)
    (xs ys : List (Fin (a+4))) (hlen : xs.length=ys.length)
    (hx : ∀ x∈xs,x≠blank) (hend : f (p+xs.length)=blank) :
    HoareTime forward (fun v => v=(cfg (putWord f p xs) (putWord g q ys) p q).tapes)
      (fun v => v=(cfg (putWord f p ys) (putWord g q xs) (p+xs.length) (q+xs.length)).tapes)
      xs.length := by
  rintro v rfl
  refine ⟨xs.length,_,le_rfl,forward_run f g p q xs ys hlen hx,?_,rfl⟩
  simp [step,forward,cfg,putWord_outside f p (p+xs.length) ys (Or.inr (by omega)),hend]

def program (a : ℕ) : Program 2 7 a :=
  seq (seq forward (extend ReturnOrigin.program 1))
    (reindex (extend ReturnOrigin.program 1) EqualWordReplace.swap)

/-- Both words are exchanged literally, both heads restored, and all costs
paid, including the empty-word case. No temporary payload tape is needed. -/
theorem runs (f g : ℤ → Fin (a+4)) (p q : ℤ)
    (xs ys : List (Fin (a+4))) (hlen : xs.length=ys.length)
    (hx : ∀ x∈xs,x≠blank) (hy : ∀ y∈ys,y≠blank)
    (hf : f (p-1)=blank) (hf' : f (p+xs.length)=blank) (hg : g (q-1)=blank) :
    HoareTime (program a)
      (fun v => v=(cfg (putWord f p xs) (putWord g q ys) p q).tapes)
      (fun v => v=(cfg (putWord f p ys) (putWord g q xs) p q).tapes)
      (3*xs.length+6) := by
  have h0 := forward_hoare f g p q xs ys hlen hx hf'
  have h1 := hoare_extend_eq (ReturnOrigin.return_hoare_at f p ys hy hf)
    (⟨fun _ => q+xs.length,fun _ => putWord g q xs⟩ : Tapes 1 a)
  change HoareTime (extend ReturnOrigin.program 1)
    (fun v => v=(ReturnOrigin.cfg (putWord f p ys) (p+ys.length) 0).tapes.append _)
    (fun v => v=(ReturnOrigin.cfg (putWord f p ys) p 0).tapes.append _) _ at h1
  rw [←hlen] at h1
  rw [EqualWordReplace.first_bank,EqualWordReplace.first_bank] at h1
  have h2 := hoare_place (ReturnOrigin.return_hoare_at g q xs hx hg) EqualWordReplace.swap
    (⟨fun _ => p,fun _ => putWord f p ys⟩ : Tapes 1 a)
  change HoareTime (reindex (extend ReturnOrigin.program 1) EqualWordReplace.swap)
    (fun v => v=((ReturnOrigin.cfg (putWord g q xs) (q+xs.length) 0).tapes.append _).reindex EqualWordReplace.swap)
    (fun v => v=((ReturnOrigin.cfg (putWord g q xs) q 0).tapes.append _).reindex EqualWordReplace.swap) _ at h2
  rw [EqualWordReplace.second_bank,EqualWordReplace.second_bank] at h2
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.EqualWordSwap
