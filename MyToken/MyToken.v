Require Import Coq.FSets.FMapWeakList.
Require Import String.
Require Import OrderedTypeEx.

Module AddrMap := FMapWeakList.Make(Nat_as_OT).
Definition MapAddrIntType := AddrMap.t nat.

Definition sender := 0.

Record MyToken := mytoken {
  name: string;
  symbol: string;
  decimals: nat;

  balanceOf: AddrMap.t nat;
  allowance: AddrMap.t MapAddrIntType;
  spentAllowance: AddrMap.t MapAddrIntType;
}.

Definition create_token (initialSupply:nat) (tokenName:string) (decimalUnits:nat) (tokenSymbol:string) :=
  let startBalance := AddrMap.empty nat in
  let actualBalance := AddrMap.add sender initialSupply startBalance in
  mytoken tokenName tokenSymbol decimalUnits startBalance (AddrMap.empty MapAddrIntType) (AddrMap.empty MapAddrIntType).
