mutual
  inductive TyCtx where
  | empty
  | push (t : Ty) (ctx : TyCtx)

  inductive Ty where
  | number
  | function : TyCtx -> TyCtx -> Ty
end

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
  | _ :: s, n + 1 => Stack.nth s n
  | [], _ => none

inductive Reduce : (Stack × Term) -> Stack -> Prop where
| number : Reduce (s, .number n) (.number n :: s)
| bin_op : Reduce (.number n2 :: .number n1 :: s, .bin_op op) (BinOp.eval op n1 n2 :: s)
| function : Reduce (s, .function ctx body) (.function ctx body :: s)
| app : Reduce (s, body) s' -> Reduce (.function ctx body :: s, .app) s'
| dup : Stack.nth s i = some t -> Reduce (s, .dup i) (t :: s)
| seq : Reduce (s1, t1) s2 -> Reduce (s2, t2) s3 -> Reduce (s1, t1 ; t2) s3

notation s "|" t " ==> " s' => Reduce (s, t) s'
notation t " ⇓ " s => [] | t ==> s
