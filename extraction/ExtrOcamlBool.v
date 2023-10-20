From Coq Require Import Bool.
From Coq Require Extraction.

Extract Inlined Constant negb => "not".

Extract Inlined Constant Nat.leb => "(<=)".
Extract Inlined Constant bool_dec => "(=)".
