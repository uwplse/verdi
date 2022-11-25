Require Import Bool.
Require Extraction.

Extract Inlined Constant negb => "not".

Extract Inlined Constant Nat.leb => "(<=)".
Extract Inlined Constant bool_dec => "(=)".
