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
  have general : ∀ t s s' ctx, (ctx ‖ t ==> s) ∧ (ctx ‖ t ==> s') → s = s' := by
    intro t s s' ctx ⟨reduction1, reduction2⟩

    induction reduction1 generalizing s'
    . cases reduction2
      rfl
    . cases reduction2
      rfl
    . cases reduction2
      rfl
    . cases reduction2
      apply_assumption
      assumption
    . cases reduction2
      simp_all
    . apply_assumption
      cases reduction2
      rename_i a b c d e
      specialize a _ d
      subst a
      assumption

  exact general (ctx := _)

theorem q19 : ∃ctx, .empty ⊢ (.number 4 ; .function (.number ::: .empty) (.number 1 ; .bin_op .plus) ; .app) : ctx := by
  apply Exists.intro
  repeat constructor

