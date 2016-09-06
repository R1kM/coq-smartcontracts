Require Import Arith.
Require Import Nat.
Require Import OrderedTypeEx.
Require Import Coq.FSets.FMapList.
Require Import BinInt.
Require Import BinIntDef.
Open Scope Z_scope.
Include BinIntDef.Z.
Module IntMap := FMapList.Make(Z_as_OT).
Definition contract_addr := 0.

Definition EtherMap := IntMap.t Z.

Record Message := create_message {
sender: Z;
value: Z;
}.

Definition get_ether (addr : Z) map : Z :=
  match (IntMap.find addr map) with
  | None => 0
  | Some a => a
  end.

Definition send addr value map := 
  if (leb value (get_ether contract_addr map)) then 
    (let map_bis := IntMap.add contract_addr ((get_ether contract_addr map) - value) map in
    let map_bis := IntMap.add addr ((get_ether addr map_bis) + value) map_bis in
    (true, map_bis))
  else (false, map).

Record Auction := create_Auction { 
bids: IntMap.t (Z);
isWinner: IntMap.t (bool);
highestBid: Z;
}.

Definition get_isWinner (mapping : IntMap.t (bool) ) (a0 : Z) := 
let m1:= match (IntMap.find a0 mapping)  with
 | None => false
 | Some a => a end in 
m1.

Definition get_money (Auction : Auction) (ether : EtherMap) (msg: Message) :=
  if (get_isWinner (isWinner Auction) (sender msg)) then 
  (let (_, new_ether) := send (sender msg) (highestBid Auction) ether in
    let isWinner := IntMap.add (sender msg) false (isWinner Auction) in
    (create_Auction (bids Auction) isWinner (highestBid Auction), new_ether))
  else (Auction, ether).

Require Import Bool.

Lemma test_send : forall (Auction : Auction) (ether : EtherMap) (msg: Message),
  Is_true (get_isWinner (isWinner Auction) (sender msg)) -> Is_true (ltb 0 (highestBid Auction)) 
  -> let (_, etherbis) := get_money Auction ether msg in Is_true (ltb (get_ether (sender msg) ether) (get_ether (sender msg) etherbis)).
Proof.
intros.
unfold get_money.
destruct (get_isWinner (isWinner Auction0) (sender msg)).
* unfold send.
  destruct (highestBid Auction0 <=?
     get_ether contract_addr ether).
  admit.
  destruct (get_ether (sender msg) ether <? get_ether (sender msg) ether).
  trivial.
  (* This point is impossible : incorrect behaviour *)
  admit.
* contradiction.
Admitted.


Definition get_bids (mapping : IntMap.t (Z) ) (a0 : Z) : Z := 
let m1:= match (IntMap.find a0 mapping)  with
 | None => 0
 | Some a => a end in 
m1.

Definition Auction_constructor (ether: EtherMap) (msg : Message):= 
let bids := IntMap.empty (Z) in
let isWinner := IntMap.empty (bool) in
let highestBid := 0 in
let highestBid := 0 in 
let imap1 := match (IntMap.find (sender msg) isWinner) with
 |None => false
 | Some a => a end in
let isWinner := IntMap.add (sender msg) (true)isWinner in
(create_Auction bids isWinner highestBid).

Definition bid (Auction:Auction) (value:Z) (ether: EtherMap) (msg : Message) := 
let bids := (bids Auction) in
let isWinner := (isWinner Auction) in
let highestBid := (highestBid Auction) in
let Auction2 := Auction in 
if (( Z.leb value (get_bids bids  (sender msg)))) then (Auction) 
else (let imap1 := match (IntMap.find (sender msg) bids) with
 |None => 0
 | Some a => a end in
let bids := IntMap.add (sender msg) (value)bids in
if (( Z.leb highestBid value)) then (let highestBid := value in 
let imap1 := match (IntMap.find (sender msg) isWinner) with
 |None => false
 | Some a => a end in
let isWinner := IntMap.add (sender msg) (true)isWinner in
(create_Auction bids isWinner highestBid)) 
 else (create_Auction bids isWinner highestBid))
.

Lemma plus_reg_r : forall (n m p : Z), n = m -> p+n= p+m.
Proof.
  intros.
  induction p.
  auto.
  rewrite -> H.
  auto.
rewrite -> H.
auto.
Qed.

Lemma plus_reg_r2 : forall (n m p : Z), n = m -> n+p= m+p.
Proof.
  intros.
  destruct p.
  rewrite -> H.
  reflexivity.
rewrite -> H.
  reflexivity.
rewrite -> H.
  reflexivity.
Qed.

Lemma plus_reg_l2 : forall (n m p : Z), n+p= m+p -> n = m.
Proof.
  intros.
rewrite <- Z.add_cancel_l with (n := n) (m := m) (p := p).
rewrite -> Z.add_comm.
symmetry.
rewrite -> Z.add_comm.
symmetry.
apply H.
Qed.

Lemma add_0_n : forall (n : Z), n + 0 = n.
Proof.
intro.
now destruct n.
Qed.

Lemma Zminus_assoc_reverse : forall (n m p : Z), n + m - p = n + (m - p).
Proof.
intros.
assert (m-p = m + -p).
apply Zplus_minus_eq.
symmetry.
apply Zplus_minus.
rewrite -> H.
symmetry.
apply Zplus_minus_eq.
rewrite -> Zplus_assoc.
symmetry.
rewrite -> Z.add_comm.
rewrite -> Zplus_assoc.
rewrite -> Z.add_comm.
apply plus_reg_r.
rewrite <- Zplus_assoc.
assert (-p + p = 0).
destruct p.
simpl.
auto.
simpl.
apply Z.pos_sub_diag.
simpl.
apply Z.pos_sub_diag.
rewrite -> H0.
symmetry.
apply Zplus_0_r_reverse.
Qed.

