From sys_verif.program_proof Require Import prelude.
From New.proof Require Export std.
From New.generatedproof.sys_verif_code Require Export heap.
From Perennial Require Import base.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit heap := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf heap := build_get_is_pkg_init_wf.

End proof.
