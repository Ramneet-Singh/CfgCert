import Basic

variables {NT T : Type}

constant fresh : (list NT) → NT
constant isFresh (α : list NT) (A = fresh α) : A ∉ α

def StartTransform (g : CFG NT T) : CFG NT T :=
  let
    N := CFG_NonTerms g,
    SNew := fresh N
  in
    (CFG.mk
      [ (SNew, [Symbol.NonTerminal g.start])] ++ g.rules,
      SNew
    )