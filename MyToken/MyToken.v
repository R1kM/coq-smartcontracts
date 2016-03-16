Require Import String.

Record MyToken := mytoken {
  name: string;
  symbol: string;
  decimals: nat;
}.
