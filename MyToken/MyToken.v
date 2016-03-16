Require Import Coq.FSets.FMapWeakList.
Require Import String.
Require Import OrderedTypeEx.

Module AddrMap := FMapWeakList.Make(Nat_as_OT).
Definition MapAddrIntType := AddrMap.t nat.

Record MyToken := mytoken {
  name: string;
  symbol: string;
  decimals: nat;

  balanceOf: AddrMap.t nat;
  allowance: AddrMap.t MapAddrIntType;
  spentAllowance: AddrMap.t MapAddrIntType;
}.



