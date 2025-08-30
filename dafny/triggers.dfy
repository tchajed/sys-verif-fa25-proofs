// leaving off the body makes this an arbitrary but fixed (and deterministic)
// function
ghost function f(x: int): int

lemma {:axiom} fLinear(x: int, y: int)
  ensures f(x + y) == f(x) + f(y)
lemma {:axiom} fAntiSymm(x: int)
  ensures f(-x) == -f(x)

// we create lemmas with specifically chosen triggers, rather than the ones
// Dafny would have automatically chosen
lemma fLinear_auto()
  ensures forall x, y {:trigger f(x), f(y) } :: f(x + y) == f(x) + f(y)
{
  forall x, y
    ensures f(x + y) == f(x) + f(y)
  {
    fLinear(x, y);
  }
}

lemma fAntiSymm_auto()
  ensures forall x {:trigger {f(-x)}} :: f(-x) == -f(x)
{
  forall x
    ensures f(-x) == -f(x)
  {
    fAntiSymm(x);
  }
}

lemma LinearSubtraction_manual_proof(x: int, y: int)
  ensures f(x - y) == f(x) - f(y)
{
  // with no proof, Dafny cannot prove this: it doesn't know to use the fLinear
  // and fAntiSymm axioms. Z3 doesn't even see those axioms for performance
  // reasons.

  // if we think about it, these exact instantiations of the axioms work
  fLinear(x, -y);
  fAntiSymm(y);
  // this assertion is not required but it connects the known facts to the
  // postcondition
  assert x + (-y) == x - y;
}

lemma LinearSubtraction_auto_proof(x: int, y: int)
  ensures f(x - y) == f(x) - f(y)
{
  // The auto lemmas introduce a forall into the context, so we don't have to
  // manually specify how to use fLinear and fAntiSymm.
  fLinear_auto();
  fAntiSymm_auto();

  // Given the triggers and the fact that the context contains terms like f(x -
  // y), f(x), and f(y), Z3 instantiates the foralls in the _auto lemma
  // postconditions appropriately and has enough facts to finish the proof (as
  // well as some useless facts like f(x - y) + f(x) == f(x - y + x)).
}

lemma TriggerNotEnough()
  ensures f(0) == 0
{
  // This is a case where the trigger on fAntiSymm_auto is not syntactically
  // visible (the trigger requires f(-x), and due to internals of Z3, x can't be
  // the constant 0 either) so the proof needs some more work to cause it to
  // trigger.
  fAntiSymm_auto();
  fAntiSymm(0); // required
}
