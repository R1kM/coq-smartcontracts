Require Import String.

Variable address : Type.

Record MyToken := mytoken {
  name: string;
  symbol: string;
  decimals: nat;

  balanceOf: address -> nat;
  allowance : address -> address -> nat;
  spentAllowance : address -> address -> nat;
}.