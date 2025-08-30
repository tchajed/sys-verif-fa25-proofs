From sys_verif.program_proof Require Import prelude.
From New.proof Require Export std sync.
From sys_verif.program_proof Require Import demos.barrier_proof.
From New.generatedproof.sys_verif_code Require Export concurrent.
From Perennial Require Import base.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit concurrent := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf concurrent := build_get_is_pkg_init_wf.

End proof.
