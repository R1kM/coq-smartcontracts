Require Import List.
Require Import OrderedType.
Require Import Coq.Program.Equality.
Require Import Arith.
Require Import Nat.
Require Import OrderedTypeEx.
Require Import Coq.FSets.FMapList.
Require Import BinInt.
Require Import BinIntDef.
Open Scope Z_scope.
Include BinIntDef.Z.
Module IntMap := FMapList.Make(Z_as_OT).
Definition sender := 0.
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
Definition Ballot_constructor(_numProposals:Z)  := 
let voteCounts := IntMap.empty (Z) in
let delegations := IntMap.empty (Z) in
let votes := IntMap.empty (Z) in
let voted := IntMap.empty (bool) in
let voterWeight := IntMap.empty (Z) in
let numProposals := 0 in
let chairperson := 0 in
let chairperson := sender in 
let numProposals := _numProposals in 
(create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson).
Definition giveRightToVote (Ballot:Ballot) (voter:Z)  := 
let voteCounts := (voteCounts Ballot) in
let delegations := (delegations Ballot) in
let votes := (votes Ballot) in
let voted := (voted Ballot) in
let voterWeight := (voterWeight Ballot) in
let numProposals := (numProposals Ballot) in
let chairperson := (chairperson Ballot) in
let Ballot2 := Ballot in 
if ((get_voted voted  (voter))) then ((create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson)) 
 else let imap1 := match (IntMap.find voter voterWeight) with
 |None => 0
 | Some a => a end in
let voterWeight := IntMap.add voter (1)voterWeight in
(create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson).
Definition delegate (Ballot:Ballot) (to:Z)  := 
let voteCounts := (voteCounts Ballot) in
let delegations := (delegations Ballot) in
let votes := (votes Ballot) in
let voted := (voted Ballot) in
let voterWeight := (voterWeight Ballot) in
let numProposals := (numProposals Ballot) in
let chairperson := (chairperson Ballot) in
let Ballot2 := Ballot in 
if ((get_voted voted  (sender))) then ((create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson)) 
 else if (( eqb to sender)) then ((create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson)) 
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
(create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson)) 
else (let imap1 := match (IntMap.find to voterWeight) with
 |None => 0
 | Some a => a end in
let voterWeight := IntMap.add to (((get_voterWeight voterWeight  (to)) + (get_voterWeight voterWeight  (sender))))voterWeight in
let imap1 := match (IntMap.find sender voterWeight) with
 |None => 0
 | Some a => a end in
let voterWeight := IntMap.add sender (0)voterWeight in
(create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson))
.
Definition vote (Ballot:Ballot) (proposal:Z)  := 
let voteCounts := (voteCounts Ballot) in
let delegations := (delegations Ballot) in
let votes := (votes Ballot) in
let voted := (voted Ballot) in
let voterWeight := (voterWeight Ballot) in
let numProposals := (numProposals Ballot) in
let chairperson := (chairperson Ballot) in
let Ballot2 := Ballot in 
if (( orb (get_voted voted  (sender)) ( ltb numProposals proposal))) then ((create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson)) 
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
(create_Ballot voteCounts delegations votes voted voterWeight numProposals chairperson).
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


Lemma extract_Sorted_0 : forall (a b : Z*Z) (l : list (Z * Z)),
  Sorted.Sorted (IntMap.Raw.PX.ltk (elt:=Z)) (a::b::l) -> Sorted.Sorted (IntMap.Raw.PX.ltk (elt:=Z)) (b::l).
Proof.
  intros.
  apply Sorted.Sorted_inv in H.
  apply H.
Qed. 

Definition mapping_function_voterWeight ( x : Z * Z) := 
 (snd (x)).
Fixpoint sum_voterWeight (maplist : list (Z * Z)) := 
 match maplist with
    | nil => 0
    | a::q => (mapping_function_voterWeight a) + (sum_voterWeight q)
end.
Lemma update_voterWeight : forall ( Ballot2 : Ballot ) (address : Z) (value : Z),
      let balance_map := (voterWeight Ballot2) in
      let original_value := match (IntMap.find address (voterWeight Ballot2)) with
      | None => 0
      | Some a => mapping_function_voterWeight(address, a) end in
      let balance2 := sum_voterWeight (IntMap.elements (IntMap.add address value balance_map)) in
      (sum_voterWeight (IntMap.elements balance_map)) + mapping_function_voterWeight(address, value) = balance2 + original_value.
      Proof.
      Opaque mapping_function_voterWeight.
      intros.
      case_eq (IntMap.find (elt := Z) address (voterWeight Ballot2)).
      intro t0.
      unfold balance2.
      unfold sum_voterWeight.
      simpl.
      unfold get_voterWeight.
      unfold balance_map.
      destruct (voterWeight Ballot2).
      intros.
      simpl.
      unfold IntMap.Raw.add.
      remember (hd this) as a.
      remember (tl this) as a_bis.
      dependent induction this.
      - assert (original_value = 0).
      simpl in original_value.
      auto.
      rewrite -> H0.
      simpl.
      symmetry.
      rewrite -> Z.add_comm.
      simpl.
      rewrite -> Z.add_comm.
      simpl.
      reflexivity.
      - simpl.
      destruct a as (z0, z1).
      destruct (Z_as_OT.compare).
      + simpl.
      assert (IntMap.find (elt := Z) address {| IntMap.this := (z0, z1) :: this; IntMap.sorted := sorted |} = None).
      unfold IntMap.find.
      unfold IntMap.Raw.find.
      simpl.
      destruct Z_as_OT.compare.
      reflexivity.
      unfold Z_as_OT.lt in l.
      unfold Z_as_OT.eq in e.
      apply Z_as_OT.lt_not_eq in e.
      contradiction.
      apply l.
      apply Z_as_OT.lt_trans with (x:=z0) (y:=address) (z:=z0) in l0.
      apply Z_as_OT.lt_not_eq in l0.
      compute in l0.
      absurd (z0 = z0).
      auto.
      reflexivity.
      apply l.
      rewrite -> H0 in H.
      discriminate.
      + rewrite <- Z.add_comm.
      symmetry.
      rewrite <- Z.add_assoc.
      apply plus_reg_r.
      rewrite -> Z.add_comm.
      assert (original_value = mapping_function_voterWeight (z0, z1)).
      unfold original_value.
      rewrite -> e.
      unfold IntMap.find.
      unfold IntMap.Raw.find.
      simpl.
      destruct Z_as_OT.compare.
      apply Z_as_OT.lt_not_eq in l.
      absurd (z0 <> z0).
      auto.
      apply l.
      rewrite -> e.
      reflexivity.
      apply Z_as_OT.lt_not_eq in l.
      absurd (z0 <> z0).
      auto.
      apply l.
      rewrite -> H0.
      reflexivity.
      + rewrite <- Z.add_assoc.
      symmetry.
      rewrite <- Z.add_assoc.
      apply plus_reg_r.
      symmetry.
      assert (Sorted (IntMap.Raw.PX.ltk (elt := Z)) this).
      induction this.
      auto.
      apply extract_Sorted_0 with (a:=(z0, z1)).
      apply sorted.
      assert (original_value = match
        IntMap.find (elt := Z) address {| IntMap.this := this; IntMap.sorted := H0 |} with
        | Some a => mapping_function_voterWeight (address, a)
        | None => 0
        end).
      unfold original_value.
      unfold IntMap.find.
      unfold IntMap.Raw.find.
      simpl.
      destruct Z_as_OT.compare.
      apply Z_as_OT.lt_trans with (x:=address) (y:=z0) (z:=address) in l0.
      absurd (address < address).
      auto.
      apply l0.
      apply l.
      rewrite -> e in l.
      apply Z_as_OT.lt_not_eq in l.
      absurd (z0 <> z0).
      auto.
      apply l.
      reflexivity.
      rewrite -> H1.
      apply IHthis with (sorted := H0) (a := hd this) (a_bis := tl this) (t0:=t0).
      unfold IntMap.find.
      unfold IntMap.Raw.find.
      simpl.
      unfold IntMap.find in H.
      unfold IntMap.Raw.find in H.
      simpl in H.
      destruct Z_as_OT.compare in H.
      apply Z_as_OT.lt_trans with (x:=address) (y:=z0) (z:=address) in l0.
      absurd (address < address).
      auto.
      apply l0.
      apply l.
      rewrite -> e in l.
      apply Z_as_OT.lt_not_eq in l.
      absurd (z0 <> z0).
      auto.
      apply l.
      apply H.
      reflexivity.
      reflexivity.
      - intros.
      assert (original_value = 0).
      unfold original_value.
      rewrite -> H.
      reflexivity.
      rewrite -> H0.
      unfold balance2.
      unfold balance_map.
      destruct (voterWeight Ballot2).
      simpl.
      dependent induction this.
      simpl.
      symmetry.
      rewrite -> Z.add_comm.
      simpl.
      rewrite -> Z.add_comm.
      simpl.
      reflexivity.
      unfold IntMap.Raw.add.
      destruct a as (z, t0).
      destruct Z_as_OT.compare.
      unfold sum_voterWeight.
      rewrite -> Z.add_comm.
      symmetry.
      rewrite <- Z.add_assoc.
      apply plus_reg_r.
      rewrite -> Z.add_comm.
      simpl.
      reflexivity.
      simpl.
      assert (original_value = mapping_function_voterWeight (z, t0)).
      unfold original_value.
      unfold IntMap.find.
      unfold IntMap.Raw.find.
      simpl.
      destruct Z_as_OT.compare.
      apply Z_as_OT.lt_not_eq in l.
      rewrite -> e in l.
      absurd (z <> z).
      auto.
      apply l.
      rewrite -> e.
      reflexivity.
      rewrite -> e in l.
      apply Z_as_OT.lt_not_eq in l.
      absurd (z <> z).
      auto.
      apply l.
      rewrite -> H0 in H1.
      rewrite <- H1.
      simpl.
      symmetry.
      rewrite <- Z.add_comm.
      simpl.
      rewrite <- Z.add_comm.
      reflexivity.
      unfold IntMap.Raw.add in IHthis.
      unfold sum_voterWeight.
      rewrite <- Z.add_assoc.
      symmetry.
      rewrite <- Z.add_assoc.
      symmetry.
      apply plus_reg_r.
      unfold sum_voterWeight in IHthis.
      assert (Sorted (IntMap.Raw.PX.ltk (elt := Z)) this).
      induction this.
      auto.
      apply extract_Sorted_0 with (a:= (z, t0)).
      apply sorted.
      apply IHthis with (sorted := H1).
      unfold IntMap.find.
      unfold IntMap.Raw.find.
      simpl.
      unfold IntMap.find in H.
      unfold IntMap.Raw.find in H.
      simpl in H.
      destruct Z_as_OT.compare in H.
      apply Z_as_OT.lt_trans with (x:=z) (y:=address) (z:=z) in l.
      absurd (z<z).
      auto.
      apply l.
      apply l0.
      discriminate.
      apply H.
      assert (IntMap.find (elt := Z) address {| IntMap.this := this; IntMap.sorted := H1 |} = None).
      unfold IntMap.find.
      unfold IntMap.Raw.find.
      simpl.
      unfold IntMap.find in H.
      unfold IntMap.Raw.find in H.
      simpl in H.
      destruct Z_as_OT.compare in H.
      apply Z_as_OT.lt_trans with (x:=z) (y:=address) (z:=z) in l.
      absurd (z<z).
      auto.
      apply l.
      apply l0.
      discriminate.
      apply H.
      rewrite -> H2.
      reflexivity.
      Qed.
Lemma preservation_vote_voterWeight : forall (Ballot : Ballot) (proposal:Z) , 
 let Ballot_2 := vote Ballot proposal in
 (sum_voterWeight (IntMap.elements (voterWeight Ballot))) = ( sum_voterWeight (IntMap.elements (voterWeight Ballot_2))).
Admitted.

Lemma preservation_delegate_voterWeight : forall (Ballot : Ballot) (to:Z) , 
 let Ballot_2 := delegate Ballot to in
 (sum_voterWeight (IntMap.elements (voterWeight Ballot))) = ( sum_voterWeight (IntMap.elements (voterWeight Ballot_2))).
Admitted.

Lemma preservation_giveRightToVote_voterWeight : forall (Ballot : Ballot) (voter:Z) , 
 let Ballot_2 := giveRightToVote Ballot voter in
 (sum_voterWeight (IntMap.elements (voterWeight Ballot))) = ( sum_voterWeight (IntMap.elements (voterWeight Ballot_2))).
Admitted.

