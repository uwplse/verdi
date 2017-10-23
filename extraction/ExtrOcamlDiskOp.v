Require Import Verdi.Net.
Require Extraction.

Extract Inductive disk_op => "DiskOpShim.disk_op" ["DiskOpShim.Append" "DiskOpShim.Write" "DiskOpShim.Delete"].
