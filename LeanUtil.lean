module

/-! Tiny shared string helpers. This library sits below the spec types and
must not import them. -/

namespace LeanUtil

public section

/-- True when `s` contains a non-whitespace character. -/
public def nonemptyText (s : String) : Bool :=
  s.any fun c => !c.isWhitespace

public def joinSep (sep : String) : List String → String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ sep ++ joinSep sep xs

end

end LeanUtil
