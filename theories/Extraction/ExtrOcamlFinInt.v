From StructTact Require Import Fin.
From Coq Require Extraction.

Extract Inlined Constant fin => int.

Extract Inlined Constant fin_eq_dec => "(fun _ -> (=))".

Extract Inlined Constant all_fin => "(fun n -> (Obj.magic (seq 0 n)))".

Extract Inlined Constant fin_to_nat => "(fun _ n -> n)".

Extract Inlined Constant fin_compare_compat => "(fun _ n m -> if n = m then EQ else if n < m then LT else GT)".
Extract Inlined Constant fin_compare => "(fun _ n m -> if n = m then Eq else if n < m then Lt else Gt)".
