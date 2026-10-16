module

/-! Tiny shared string helpers. This library sits below the spec types and
must not import them. -/

namespace LeanUtil

public section

/-- True when `s` contains a non-whitespace character.

Defined over `s.toList`, not `String.any`: the kernel can evaluate the list form,
so a literal's proof is `by decide +kernel` and needs no `native_decide` axiom. Exposed so
`decide` in importing modules can unfold it. -/
@[expose] public def nonemptyText (s : String) : Bool :=
  s.toList.any fun c => !c.isWhitespace

/-- Split a character list at every `sep`, keeping empty pieces — the same pieces
as `String.splitOn` with a one-character separator, in a kernel-reducible form. -/
@[expose] public def splitChars (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c == sep then [] :: splitChars sep cs
    else
      match splitChars sep cs with
      | [] => [[c]]
      | piece :: rest => (c :: piece) :: rest

/-- True when `needle` occurs contiguously in `haystack` — `String` substring search
in a kernel-reducible form. An empty needle occurs everywhere. -/
@[expose] public def hasInfix (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | c :: cs => needle.isPrefixOf (c :: cs) || hasInfix needle cs

public def joinSep (sep : String) : List String → String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ sep ++ joinSep sep xs

end

end LeanUtil
