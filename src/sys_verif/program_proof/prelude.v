(* slightly extend Perennial's proof setup *)
From New.proof Require Export proof_prelude.
From iris_named_props Require Import named_props.
From sys_verif Require Export options.
From Coq Require Import Strings.Ascii.

(* enable ASCII [name :: P] instead of Unicode [name ∷ P] for named
propositions, in bi_scope *)
Export named_props_ascii_notation.

#[global] Open Scope general_if_scope.

(* Print ncfupd as a normal fupd, to avoid seeing (even more) confusing
goals.

These notations need to be distinct from the fupd notations (otherwise those
don't parse), so they include a Unicode zero-width space after the => *)
Notation "|={ E }=>​ Q" := (ncfupd E E Q) (only printing, at level 200, E at level 50) : bi_scope.
Notation "|==>​ Q" := (ncfupd ⊤ ⊤ Q) (only printing, at level 200) : bi_scope.

Ltac wp_finish :=
  wp_pures;
  repeat iModIntro;
  first [
      iApply "HΦ" |
      (* if HΦ doesn't unify, maybe an equality proof is needed *)
      iDestruct ("HΦ" with "[-]") as "HΦ"; [ | iExactEq "HΦ"; f_equal ]
  ];
  try solve [
      auto;
      iFrame;
      word
  ].
