From aneris.aneris_lang Require Import ast.
From aneris.examples.transactional_consistency.snapshot_isolation Require Import snapshot_isolation_code.
From aneris.examples.transactional_consistency Require Import wrapped_library.

Definition start : val := wrap_start start.

Definition read : val := wrap_read read.

Definition write : val := wrap_write write.

Definition commit : val := wrap_commit commit.

Definition init_server ser : val := init_server ser.

Definition init_client_proxy ser : val := init_client_proxy ser.