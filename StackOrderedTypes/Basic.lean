mutual
  inductive TyCtx where
  | empty
  | push (t : Ty) (ctx : TyCtx)

  inductive Ty where
  | number
  | function : TyCtx -> TyCtx -> Ty
end

notation t ":::" ctx => TyCtx.push t ctx
instance : Append TyCtx where
  append := f
  where
    f
    | TyCtx.empty, b => b
    | TyCtx.push t ctx, b => TyCtx.push t (f ctx b)
def TyCtx.nth (ctx : TyCtx) (n : Nat) : Option Ty :=
  match ctx, n with
  | TyCtx.push t _, 0 => some t
  | TyCtx.push _ ctx, n + 1 => ctx.nth n
  | TyCtx.empty, _ => none

inductive BinOp where
| plus
| times

inductive Term where
| number (n : Nat)
| bin_op (op : BinOp)
| function (ctx : TyCtx) (body : Term)
| app
| dup (i : Nat)
| seq (t1 t2 : Term)

notation t1 ";" t2 => Term.seq t1 t2

def BinOp.eval (op : BinOp) (n1 n2 : Nat) : Term :=
  match op with
  | BinOp.plus => .number (n1 + n2)
  | BinOp.times => .number (n1 * n2)

inductive Stack where
| empty
| push (t : Term) (s : Stack)

notation "[" "]" => Stack.empty
notation t "::" s => Stack.push t s

def Stack.nth (s : Stack) (n : Nat) : Option Term :=
  match s, n with
  | t :: _, 0 => some t
  | _ :: s, n + 1 => s.nth n
  | [], _ => none

inductive Reduce : Stack -> Term -> Stack -> Prop where
| number : Reduce s (.number n) (.number n :: s)
| bin_op : Reduce (.number n2 :: .number n1 :: s) (.bin_op op) (BinOp.eval op n1 n2 :: s)
| function : Reduce s (.function ctx body) (.function ctx body :: s)
| app : Reduce s body s' -> Reduce (.function ctx body :: s) .app s'
| dup : s.nth i = some t -> Reduce s (.dup i) (t :: s)
| seq : Reduce s1 t1 s2 -> Reduce s2 t2 s3 -> Reduce s1 (t1 ; t2) s3

notation s "‖" t " ==> " s' => Reduce s t s'
notation t " ⇓ " s => [] ‖ t ==> s

inductive Typing : TyCtx -> Term -> TyCtx -> Prop where
| number : Typing ctx (.number n) (.number ::: ctx)
| bin_op : Typing (.number ::: .number ::: ctx) (.bin_op op) (.number ::: ctx)
| function : Typing ctx1 body ctx2 -> Typing ctx (.function ctx1 body) (.function ctx1 ctx2 ::: ctx)
| app : Typing (.function ctx1 ctx2 ::: ctx1 ++ ctx) .app (ctx2 ++ ctx)
| dup : ctx.nth i = some T -> Typing ctx (.dup i) (T ::: ctx)
| seq : Typing ctx1 t1 ctx2 -> Typing ctx2 t2 ctx3 -> Typing ctx1 (t1 ; t2) ctx3

notation ctx " ⊢ " t " : " ctx' => Typing ctx t ctx'

theorem q15 :
  (.number 4 ; .number 1 ; .dup 1 ; .dup 1 ; .bin_op .plus) ⇓ (.number 5 :: .number 1 :: .number 4 :: []) := by
  repeat constructor

theorem q16 : ∃s,
  (.function ctx (.number 1 ; .bin_op .plus) ; .number 4 ; .dup 1 ; .app) ⇓ s := by
  repeat constructor

theorem q17 : ∃t, ∀s, ¬t ⇓ s := by
  apply Exists.intro .app
  intro s reduction
  cases reduction

theorem q18 : ∀ t s s', (t ⇓ s) ∧ (t ⇓ s') → s = s' := by
  have general : ∀ t s s' st, (st ‖ t ==> s) ∧ (st ‖ t ==> s') → s = s' := by
    intro t s s' st ⟨reduction1, reduction2⟩

    induction reduction1 generalizing s' with
    | number =>
      cases reduction2
      rfl
    | bin_op =>
      cases reduction2
      rfl
    | function =>
      cases reduction2
      rfl
    | app _ ih =>
      cases reduction2
      rename_i bh
      exact ih _ bh
    | dup h1 =>
      cases reduction2
      rename_i h2
      rw [h1] at h2
      injection h2 with eq
      rw [eq]
    | seq h1 h2 ih1 ih2 =>
      cases reduction2
      rename_i h1' h2'
      have eq := ih1 _ h1'
      rw [eq] at ih2
      exact ih2 _ h2'

  exact general (st := _)

theorem q19 : ∃ctx, .empty ⊢ (.number 4 ; .function (.number ::: .empty) (.number 1 ; .bin_op .plus) ; .app) : ctx := by
  apply Exists.intro
  repeat constructor

-- First, define how to append Stacks, which mirrors how we append TyCtx.
def Stack.append : Stack → Stack → Stack
| [], s => s
| t :: s1, s2 => t :: (Stack.append s1 s2)

instance : Append Stack where
  append := Stack.append

-- A structural frame lemma: Evaluation behaves identically when a tail stack is attached.
theorem frame {s s' : Stack} {t : Term} (h : s ‖ t ==> s') : ∀ s2, (s ++ s2) ‖ t ==> (s' ++ s2) := by
  induction h <;> try (solve | intros; constructor)
  case app _ ih => intro s2; exact Reduce.app (ih s2)
  case dup h_nth =>
    intro s2
    have nth_append : ∀ {s : Stack} {i : Nat} {t : Term}, s.nth i = some t → (s ++ s2).nth i = some t := by
      intro s i t h
      induction s generalizing i with
      | empty => contradiction
      | push hd tl ih =>
        cases i with
        | zero => exact h
        | succ i' => exact ih h
    exact Reduce.dup (nth_append h_nth)
  case seq _ _ ih1 ih2 => intro s2; exact Reduce.seq (ih1 s2) (ih2 s2)

-- We define a mutual logical relation to establish stack and term validity.
mutual
def ValidTy : Ty → Term → Prop
| .number, .number _ => True
| .function ctx1 ctx2, .function ctx1' body =>
  ctx1 = ctx1' ∧ ∀ s1, ValidStack ctx1 s1 → ∃ s2, ValidStack ctx2 s2 ∧ s1 ‖ body ==> s2
| _, _ => False

def ValidStack : TyCtx → Stack → Prop
| .empty, [] => True
| .push ty ctx, t :: s => ValidTy ty t ∧ ValidStack ctx s
| _, _ => False
end


-- Appending valid stacks keeps them valid for appended contexts.
theorem ValidStack_append : ∀ {ctx1 : TyCtx} {s1 : Stack},
  ValidStack ctx1 s1 → ∀ {ctx2 : TyCtx} {s2 : Stack}, ValidStack ctx2 s2 → ValidStack (ctx1 ++ ctx2) (s1 ++ s2)
| .empty, [], _, ctx2, s2, h2 => h2
| .push ty ctx1', t :: s1', h, ctx2, s2, h2 => by
  have ⟨hty, hstack⟩ := h
  exact ⟨hty, ValidStack_append hstack h2⟩

-- We can split a valid stacked combined context back into its valid parts.
theorem ValidStack_split : ∀ {ctx1 ctx2 : TyCtx} {s : Stack},
  ValidStack (ctx1 ++ ctx2) s → ∃ s1 s2, s = s1 ++ s2 ∧ ValidStack ctx1 s1 ∧ ValidStack ctx2 s2
| .empty, ctx2, s, h => ⟨[], s, rfl, True.intro, h⟩
| .push ty ctx1', ctx2, t :: s', h => by
  have ⟨hty, hstack⟩ := h
  have ⟨s1', s2, heq, hv1, hv2⟩ := ValidStack_split hstack
  exists (t :: s1'), s2
  constructor
  · rw [heq]; rfl
  · exact ⟨⟨hty, hv1⟩, hv2⟩

-- Lookups into valid stacks yield valid terms.
theorem valid_nth : ∀ {ctx : TyCtx} {s : Stack} {i : Nat} {T : Ty},
  ValidStack ctx s → ctx.nth i = some T → ∃ t, s.nth i = some t ∧ ValidTy T t
| .push ty ctx', t :: s', 0, T, hs, h_nth => by
  have ⟨hty, _⟩ := hs
  injection h_nth with eq
  rw [←eq]
  exact ⟨t, rfl, hty⟩
| .push ty ctx', t :: s', i' + 1, T, hs, h_nth => by
  have ⟨_, htl⟩ := hs
  exact @valid_nth ctx' s' i' T htl h_nth

-- The main progress/normalization theorem generalized over ValidStack
theorem progress {ctx t ctx'} (h : Typing ctx t ctx') :
  ∀ s, ValidStack ctx s → ∃ s', ValidStack ctx' s' ∧ s ‖ t ==> s' := by
  induction h with
  | number =>
    rename_i ctx n
    intro s hs
    exists (.number n :: s)
    exact ⟨⟨True.intro, hs⟩, Reduce.number⟩
  | bin_op =>
    rename_i ctx op
    intro s hs
    cases s with | empty => cases hs | push t1 s' =>
    have ⟨hty1, hs'⟩ := hs
    cases s' with | empty => cases hs' | push t2 s'' =>
    have ⟨hty2, hs''⟩ := hs'
    cases t1 with
    | bin_op _ => cases hty1
    | function _ _ => cases hty1
    | app => cases hty1
    | dup _ => cases hty1
    | seq _ _ => cases hty1
    | number n2 =>
      cases t2 with
      | bin_op _ => cases hty2
      | function _ _ => cases hty2
      | app => cases hty2
      | dup _ => cases hty2
      | seq _ _ => cases hty2
      | number n1 =>
        exists (BinOp.eval op n1 n2 :: s'')
        constructor
        · constructor
          · cases op <;> exact True.intro
          · exact hs''
        · exact Reduce.bin_op
  | function h_typing ih =>
    rename_i ctx1 body ctx2 ctx
    intro s hs
    exists (.function ctx1 body :: s)
    constructor
    · constructor
      · constructor
        · rfl
        · intro s1 hs1
          exact ih s1 hs1
      · exact hs
    · exact Reduce.function
  | app =>
    rename_i ctx1 ctx2 ctx
    intro s hs
    cases s with | empty => cases hs | push t s' =>
    have ⟨hty, hs'⟩ := hs
    cases t with
    | number _ => cases hty
    | bin_op _ => cases hty
    | app => cases hty
    | dup _ => cases hty
    | seq _ _ => cases hty
    | function ctx1' body =>
      have ⟨heq, hbody⟩ := hty
      cases heq
      have ⟨s1, s2, heq_s', hv1, hv2⟩ := ValidStack_split hs'
      have ⟨s1', hv1', hred⟩ := hbody s1 hv1
      have hred_frame := frame hred s2
      exists (s1' ++ s2)
      constructor
      · apply ValidStack_append hv1' hv2
      · rw [heq_s']
        exact Reduce.app hred_frame
  | dup h_nth =>
    rename_i ctx i T
    intro s hs
    have ⟨t, h_snth, h_ty⟩ := @valid_nth _ _ _ _ hs h_nth
    exists (t :: s)
    exact ⟨⟨h_ty, hs⟩, Reduce.dup h_snth⟩
  | seq _ _ ih1 ih2 =>
    rename_i ctx1 t1 ctx2 t2 ctx3
    intro s hs
    have ⟨s1, hs1, hr1⟩ := ih1 s hs
    have ⟨s2, hs2, hr2⟩ := ih2 s1 hs1
    exists s2
    exact ⟨hs2, Reduce.seq hr1 hr2⟩

-- And finally, your target theorem.
theorem q20 : ∀t ctx, (.empty ⊢ t : ctx) → ∃s, t ⇓ s := by
  intro t ctx h_typing
  have ⟨s', _, h_red⟩ := progress h_typing [] True.intro
  exact ⟨s', h_red⟩
