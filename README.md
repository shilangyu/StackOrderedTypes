# Stack based language with ordered types

Small formalization of a stack-based language with ordered types.

The language operates on numbers using binary operators, function abstractions and applications, duplication of items on the stack.

For instance,

- `4 1 dup1 dup1 +` reduces to `5 :: 1 :: 4 :: ∅` (proof `q15`)
- `fun{ 1 + } 4 dup1 app` has a reduction (proof `q16`)
- there are terms which do not reduce (proof `q17`)
- every reducable term has a unique reduction (proof `q18`)

Then, we add typing for terms. This forbids terms which are not reducible

- `4 fun(Nat :: ∅){ 1 + } app` has a type that can be inferred (proof `q19`)
- every well-typed term has a reduction (proof `q20` NOT DONE)
