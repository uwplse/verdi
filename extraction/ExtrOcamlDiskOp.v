From Verdi Require Import Net.
From Coq Require Extraction.

Extract Inductive disk_op => "DiskOpShim.disk_op" ["DiskOpShim.Append" "DiskOpShim.Write" "DiskOpShim.Delete"].
