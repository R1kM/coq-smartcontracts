Require Import List.
Require Import Arith.
Require Import Nat.
Require Import Coq.FSets.FMapList.
Require Import String.
Require Import OrderedTypeEx.
Require Import Coq.Program.Equality.
Require Import PeanoNat.

Module AddrMap := FMapList.Make(Nat_as_OT).
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
  mytoken tokenName tokenSymbol decimalUnits actualBalance (AddrMap.empty MapAddrIntType) (AddrMap.empty MapAddrIntType).

Definition get_balance (token : MyToken) (address : nat) :=
  match AddrMap.find address (balanceOf token) with
    |None => 0
    |Some a => a
  end.

Definition transfer (token:MyToken) (toAddress:nat) (value:nat) :=
  let balanceSender := get_balance token sender in
  let balanceReceiver := get_balance token toAddress in
  if (ltb balanceSender value) then token
  else if (ltb (balanceReceiver + value) balanceReceiver) then token 
  else
    let balance := AddrMap.add sender (minus balanceSender value) (balanceOf token) in
    let balance := AddrMap.add toAddress (plus balanceReceiver value) balance in
  mytoken (name token) (symbol token) (decimals token) balance (allowance token) (spentAllowance token)
  .

Definition transferFrom (token:MyToken) (fromAddress:nat) (toAddress:nat) (value:nat) := 
  let obalanceSender := AddrMap.find fromAddress (balanceOf token) in
  let obalanceReceiver := AddrMap.find toAddress (balanceOf token) in
  let balanceSender := match obalanceSender with
    | None => 0
    | Some a => a
  end in
  let balanceReceiver := match obalanceReceiver with
    | None => 0
    | Some a => a
  end in
  if (ltb balanceSender value) then (token, false)
  else if (ltb (balanceReceiver + value) balanceReceiver) then (token, false)
  else 
  let ospentAllowance := match (AddrMap.find fromAddress (spentAllowance token)) with
    | None => None
    | Some a => AddrMap.find sender a
  end in
  let currSpentAllowance := match ospentAllowance with
    | None => 0
    | Some a => a
  end in 
  let oallowance := match (AddrMap.find fromAddress (allowance token)) with
    | None => None
    | Some a => AddrMap.find sender a
  end in
  let currAllowance := match oallowance with
    | None => 0
    | Some a => a
  end in 
  if (ltb (currSpentAllowance + value) currAllowance) then (token, false)
  else 
    let balance := AddrMap.add fromAddress (minus balanceSender value) (balanceOf token) in
    let balance := AddrMap.add toAddress (plus balanceReceiver value) balance in
    let auxSpentAllowance := match (AddrMap.find fromAddress (spentAllowance token)) with
      | None => AddrMap.empty nat
      | Some a => a
    end in
    let newSpentAllowance := AddrMap.add fromAddress (AddrMap.add sender (currSpentAllowance + value) auxSpentAllowance) (spentAllowance token) in
    (mytoken (name token) (symbol token) (decimals token) balance (allowance token) newSpentAllowance, true)
.

Fixpoint sum_onBalance (balance_list : list (nat * nat)) :=
  match balance_list with
    | nil => 0
    | a::q => (snd a) +(sum_onBalance q)
  end.

Definition totalBalance (token : MyToken) :=
  sum_onBalance (AddrMap.elements (balanceOf token))
.

Lemma correct_creation : forall (initial dec : nat ) (name symbol: string), 
  totalBalance (create_token initial name dec symbol) = initial.
Proof.
  intros.
  unfold totalBalance.
  unfold balanceOf.
  simpl.
  symmetry.
  apply plus_n_O.
Qed.

Lemma plus_reg_r : forall (n m p : nat), n = m -> p+n= p+m.
Proof.
  intros.
  auto.
Qed.

Lemma extract_Sorted : forall (a b : nat*nat) (l : list (nat * nat)),
  Sorted.Sorted (AddrMap.Raw.PX.ltk (elt:=nat)) (a::b::l) -> Sorted.Sorted (AddrMap.Raw.PX.ltk (elt:=nat)) (b::l).
Proof.
  intros.
  apply Sorted.Sorted_inv in H.
  apply H.
Qed.

Lemma update_balance : forall (token : MyToken) (address value : nat),
  let balance_map := (balanceOf token) in
  let balance2 := sum_onBalance (AddrMap.elements (AddrMap.add address value balance_map)) in
  (sum_onBalance (AddrMap.elements balance_map)) + value = balance2 + (get_balance token address).
Proof.
  intros.
  unfold balance2.
  unfold sum_onBalance.
  simpl.
  intros.
  unfold get_balance.
  unfold AddrMap.find.
  replace (balanceOf token) with balance_map.
  destruct balance_map.
  simpl.
  unfold AddrMap.Raw.add.
  remember (hd this) as a.
  remember (tl this) as a_bis.
  dependent induction this.
-  unfold snd.
   simpl.
   elim value.
  simpl.
  reflexivity.
  intros.
  simpl in |- *.
  rewrite <- H.
  reflexivity.
-  simpl.
  destruct a.
  unfold fst.
  destruct (Nat_as_OT.compare).
  +simpl.
  rewrite <- plus_n_O.
  rewrite -> Nat.add_comm.
  reflexivity.
  + simpl.
  rewrite -> Nat.add_comm.
  symmetry.
  rewrite -> plus_assoc_reverse.
  symmetry.
  apply plus_reg_r with (p := value) (n := n0 +
 (fix sum_onBalance (balance_list : list (nat * nat)) : nat :=
    match balance_list with
    | nil => 0
    | a :: q => snd a + sum_onBalance q
    end) this) (m := (fix sum_onBalance (balance_list : list (nat * nat)) : nat :=
   match balance_list with
   | nil => 0
   | a :: q => snd a + sum_onBalance q
   end) this + n0).
  rewrite -> Nat.add_comm.
  reflexivity.
  +simpl.
   rewrite -> plus_assoc_reverse.
   symmetry.
   rewrite -> plus_assoc_reverse.
   apply plus_reg_r with (p := n0) (m := ((fix sum_onBalance (balance_list : list (nat * nat)) : nat :=
    match balance_list with
    | nil => 0
    | a :: q => snd a + sum_onBalance q
    end) this + value))
 (n := ((fix sum_onBalance (balance_list : list (nat * nat)) : nat :=
    match balance_list with
    | nil => 0
    | a :: q => snd a + sum_onBalance q
    end)
   ((fix add (k : AddrMap.Raw.key) (x : nat) (s : AddrMap.Raw.t nat) {struct s} :
       AddrMap.Raw.t nat :=
       match s with
       | nil => (k, x) :: nil
       | (k', y) :: l0 =>
           match Nat_as_OT.compare k k' with
           | OrderedType.LT _ => (k, x) :: s
           | OrderedType.EQ _ => (k, x) :: l0
           | OrderedType.GT _ => (k', y) :: add k x l0
           end
       end) address value this) +
 match AddrMap.Raw.find (elt:=nat) address this with
 | Some a => a
 | None => 0
 end)).
  induction this.
  simpl.
  rewrite <- Nat.add_comm.
  simpl.
  rewrite <- Nat.add_comm.
  simpl.
  reflexivity.
  symmetry.
  apply IHthis with (a0:=hd (a::this)) (a_bis := this).
  * apply extract_Sorted with (a := (n,n0)).
    apply sorted.
  * reflexivity.
  * reflexivity.
  - unfold balance_map.
    reflexivity.
Qed.

Lemma transfer_preservation : forall (token :MyToken) (toAddress value : nat), 
  let token2 := transfer token toAddress value in 
  totalBalance token = totalBalance token2.
Proof.
  intros.
  unfold totalBalance.
  unfold token2.
  unfold transfer.