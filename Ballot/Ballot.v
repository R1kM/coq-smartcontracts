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

Definition get_ether (addr : Z) map : Z :=
    match (IntMap.find addr map) with
    | None => 0
    | Some a => a
    end.

Definition send addr value map :=
    if (Z.leb value (get_ether contract_addr map)) then
        (let map_bis := IntMap.add contract_addr ((get_ether contract_addr map) - value) map in
        let map_bis := IntMap.add addr ((get_ether addr map_bis) + value) map_bis in
        (true, map_bis))
    else (false, map).

Record Message := create_message {
sender : Z;
value : Z;
}.
Record Ballot := create_Ballot { 
voteCounts: IntMap.t (Z);
delegations: IntMap.t (Z);
votes: IntMap.t (Z);
voted: IntMap.t (bool);
voterWeight: IntMap.t (Z);
numProposals: Z;
chairperson: Z;
}.
Definition get_voteCounts (mapping : IntMap.t (Z) ) (a0 : Z) := 
let m1:= match (IntMap.find a0 mapping)  with
 | None => 0
 | Some a => a end in 
m1.
Definition get_delegations (mapping : IntMap.t (Z) ) (a0 : Z) := 
let m1:= match (IntMap.find a0 mapping)  with
 | None => 0
 | Some a => a end in 
m1.
Definition get_votes (mapping : IntMap.t (Z) ) (a0 : Z) := 
let m1:= match (IntMap.find a0 mapping)  with
 | None => 0
 | Some a => a end in 
m1.
Definition get_voted (mapping : IntMap.t (bool) ) (a0 : Z) := 
let m1:= match (IntMap.find a0 mapping)  with
 | None => false
 | Some a => a end in 
m1.
Definition get_voterWeight (mapping : IntMap.t (Z) ) (a0 : Z) := 
let m1:= match (IntMap.find a0 mapping)  with
 | None => 0
 | Some a => a end in 
m1.
Fixpoint Ballot_constructor(ether : EtherMap) (msg : Message)(_numProposals:Z)  := 
let voteCounts := IntMap.empty (Z) in
let delegations := IntMap.empty (Z) in
let votes := IntMap.empty (Z) in
let voted := IntMap.empty (bool) in
let voterWeight := IntMap.empty (Z) in
let numProposals := 0 in
let chairperson := 0 in
let new_ether := ether in
let chairperson := sender in 
let numProposals := _numProposals in 
((create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson), new_ether).
Fixpoint giveRightToVote gas (Ballot:Ballot) (ether : EtherMap) (msg : Message)(voter:Z)  := 
let voteCounts := (voteCounts Ballot) in
let delegations := (delegations Ballot) in
let votes := (votes Ballot) in
let voted := (voted Ballot) in
let voterWeight := (voterWeight Ballot) in
let numProposals := (numProposals Ballot) in
let chairperson := (chairperson Ballot) in
let new_ether := ether in 
match gas with
    | O => ((create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson), new_ether)
 | S g => let new_gas := g in
if ((get_voted voted  (voter))) then (((create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson), new_ether)) 
 else let imap1 := match (IntMap.find voter voterWeight) with
 |None => 0
 | Some a => a end in
let voterWeight := IntMap.add voter (1)voterWeight in
((create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson), new_ether)end.
Fixpoint delegate gas (Ballot:Ballot) (ether : EtherMap) (msg : Message)(to:Z)  := 
let voteCounts := (voteCounts Ballot) in
let delegations := (delegations Ballot) in
let votes := (votes Ballot) in
let voted := (voted Ballot) in
let voterWeight := (voterWeight Ballot) in
let numProposals := (numProposals Ballot) in
let chairperson := (chairperson Ballot) in
let new_ether := ether in 
match gas with
    | O => ((create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson), new_ether)
 | S g => let new_gas := g in
if ((get_voted voted  (sender))) then (((create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson), new_ether)) 
 else if (( eqb to sender)) then (((create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson), new_ether)) 
 else let imap1 := match (IntMap.find sender voted) with
 |None => false
 | Some a => a end in
let voted := IntMap.add sender (true)voted in
let imap1 := match (IntMap.find sender delegations) with
 |None => 0
 | Some a => a end in
let delegations := IntMap.add sender (to)delegations in
if ((get_voted voted  (to))) then (let imap1 := match (IntMap.find (get_votes votes  (to)) voteCounts) with
 |None => 0
 | Some a => a end in
let voteCounts := IntMap.add (get_votes votes  (to)) (((get_voteCounts voteCounts  ((get_votes votes  (to)))) + (get_voterWeight voterWeight  (sender))))voteCounts in
((create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson), new_ether)) 
else (let imap1 := match (IntMap.find to voterWeight) with
 |None => 0
 | Some a => a end in
let voterWeight := IntMap.add to (((get_voterWeight voterWeight  (to)) + (get_voterWeight voterWeight  (sender))))voterWeight in
let imap1 := match (IntMap.find sender voterWeight) with
 |None => 0
 | Some a => a end in
let voterWeight := IntMap.add sender (0)voterWeight in
((create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson), new_ether))
end.
Fixpoint vote gas (Ballot:Ballot) (ether : EtherMap) (msg : Message)(proposal:Z)  := 
let voteCounts := (voteCounts Ballot) in
let delegations := (delegations Ballot) in
let votes := (votes Ballot) in
let voted := (voted Ballot) in
let voterWeight := (voterWeight Ballot) in
let numProposals := (numProposals Ballot) in
let chairperson := (chairperson Ballot) in
let new_ether := ether in 
match gas with
    | O => ((create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson), new_ether)
 | S g => let new_gas := g in
if (( orb (get_voted voted  (sender)) ( ltb numProposals proposal))) then (((create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson), new_ether)) 
 else let imap1 := match (IntMap.find sender voted) with
 |None => false
 | Some a => a end in
let voted := IntMap.add sender (true)voted in
let imap1 := match (IntMap.find sender votes) with
 |None => 0
 | Some a => a end in
let votes := IntMap.add sender (proposal)votes in
let imap1 := match (IntMap.find proposal voteCounts) with
 |None => 0
 | Some a => a end in
let voteCounts := IntMap.add proposal (((get_voteCounts voteCounts  (proposal)) + (get_voterWeight voterWeight  (sender))))voteCounts in
((create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson), new_ether)end.
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

