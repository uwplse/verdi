Require Import Bool.
Require Extraction.

Extract Inlined Constant negb => "not".

Extract Inlined Constant leb => "(<=)".
Extract Inlined Constant bool_dec => "(=)".
