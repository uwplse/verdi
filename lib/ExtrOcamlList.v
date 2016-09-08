Require Import List.

Extract Inlined Constant length => "List.length".
Extract Inlined Constant app => "List.append".

Extract Inlined Constant map => "List.map".
Extract Inlined Constant rev => "List.rev".
Extract Inlined Constant filter => "List.filter".
Extract Inlined Constant fold_left => "(fun a b c -> List.fold_left a c b)".

Extract Inlined Constant in_dec => "(fun h -> List.mem)".
