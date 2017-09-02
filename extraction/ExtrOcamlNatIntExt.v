Require Import PeanoNat.
Require Import Ascii.

Extract Inlined Constant Nat.max => "Pervasives.max".
Extract Inlined Constant Nat.min => "Pervasives.min".

Extract Inlined Constant Nat.ltb => "(<)".

Extract Inlined Constant nat_of_ascii => "Char.code".
