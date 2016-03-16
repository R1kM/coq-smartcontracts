Require Import Nat.
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

Definition transfer (token:MyToken) (toAddress:nat) (value:nat) :=
  let obalanceSender := AddrMap.find sender (balanceOf token) in
  let obalanceReceiver := AddrMap.find toAddress (balanceOf token) in
  let balanceSender := match obalanceSender with
    | None =>  0
    | Some a => a 
  end in
  let balanceReceiver := match obalanceReceiver with
    | None => 0 
    | Some a => a 
  end in
  if (ltb balanceSender value) then token
  else if (ltb (balanceReceiver + value) balanceReceiver) then token 
  else
    let balance := AddrMap.add sender (minus balanceSender value) (balanceOf token) in
    let balance := AddrMap.add toAddress (plus balanceReceiver value) balance in
  mytoken (name token) (symbol token) (decimals token) balance (allowance token) (spentAllowance token)
  .
