Require Import List.
Require Import OrderedType.
Require Import Coq.Program.Equality.
Require Import String.
Require Import Arith.
Require Import Nat.
Require Import OrderedTypeEx.
Require Import Coq.FSets.FMapList.
Require Import BinInt.
Require Import BinIntDef.
Open Scope string_scope.
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
Record MyToken := create_MyToken { 
spentAllowance: IntMap.t (IntMap.t (Z));
allowance: IntMap.t (IntMap.t (Z));
balanceOf: IntMap.t (Z);
decimals: Z;
symbol: string;
name: string;
}.
Definition get_spentAllowance (mapping : IntMap.t (IntMap.t (Z)) ) (a0 : Z) (a1 : Z) := 
let m1:= match (IntMap.find a0 mapping)  with
 | None => None 
 | Some a => IntMap.find a0 a end in 
let m2:= match m1 with
 | None => 0
 | Some a => a end in 
m2.
Definition get_allowance (mapping : IntMap.t (IntMap.t (Z)) ) (a0 : Z) (a1 : Z) := 
let m1:= match (IntMap.find a0 mapping)  with
 | None => None 
 | Some a => IntMap.find a0 a end in 
let m2:= match m1 with
 | None => 0
 | Some a => a end in 
m2.
Definition get_balanceOf (mapping : IntMap.t (Z) ) (a0 : Z) := 
let m1:= match (IntMap.find a0 mapping)  with
 | None => 0
 | Some a => a end in 
m1.
Fixpoint MyToken_constructor(ether : EtherMap) (msg : Message)(initialSupply:Z) (tokenName:string) (decimalUnits:Z) (tokenSymbol:string)  := 
let spentAllowance := IntMap.empty (IntMap.t (Z)) in
let allowance := IntMap.empty (IntMap.t (Z)) in
let balanceOf := IntMap.empty (Z) in
let decimals := 0 in
let symbol := "" in
let name := "" in
let new_ether := ether in
let imap1 := match (IntMap.find (sender msg) balanceOf) with
 |None => 0
 | Some a => a end in
let balanceOf := IntMap.add (sender msg) (initialSupply)balanceOf in
let name := tokenName in 
let symbol := tokenSymbol in 
let decimals := decimalUnits in 
((create_MyToken spentAllowance allowance balanceOf decimals symbol name), new_ether).
Fixpoint transfer gas (MyToken:MyToken) (ether : EtherMap) (msg : Message)(_to:Z) (_value:Z)  := 
let spentAllowance := (spentAllowance MyToken) in
let allowance := (allowance MyToken) in
let balanceOf := (balanceOf MyToken) in
let decimals := (decimals MyToken) in
let symbol := (symbol MyToken) in
let name := (name MyToken) in
let new_ether := ether in 
match gas with
    | O => ((create_MyToken spentAllowance allowance balanceOf decimals symbol name), new_ether)
 | S g => let new_gas := g in
if (( ltb (get_balanceOf balanceOf  ((sender msg))) _value)) then ((MyToken, ether)) 
 else if (( ltb ((get_balanceOf balanceOf  (_to)) + _value) (get_balanceOf balanceOf  (_to)))) then ((MyToken, ether)) 
 else let imap1 := match (IntMap.find (sender msg) balanceOf) with
 |None => 0
 | Some a => a end in
let balanceOf := IntMap.add (sender msg) (((get_balanceOf balanceOf  ((sender msg))) - _value))balanceOf in
let imap1 := match (IntMap.find _to balanceOf) with
 |None => 0
 | Some a => a end in
let balanceOf := IntMap.add _to (((get_balanceOf balanceOf  (_to)) + _value))balanceOf in
((create_MyToken spentAllowance allowance balanceOf decimals symbol name), new_ether)end.
Fixpoint transferFrom gas (MyToken:MyToken) (ether : EtherMap) (msg : Message)(_from:Z) (_to:Z) (_value:Z)  := 
let spentAllowance := (spentAllowance MyToken) in
let allowance := (allowance MyToken) in
let balanceOf := (balanceOf MyToken) in
let decimals := (decimals MyToken) in
let symbol := (symbol MyToken) in
let name := (name MyToken) in
let success := false in 
let new_ether := ether in 
match gas with
    | O => ((create_MyToken spentAllowance allowance balanceOf decimals symbol name), new_ether, success)

 | S g => let new_gas := g in
if (( ltb (get_balanceOf balanceOf  (_from)) _value)) then ((MyToken, ether, success)
) 
 else if (( ltb ((get_balanceOf balanceOf  (_to)) + _value) (get_balanceOf balanceOf  (_to)))) then ((MyToken, ether, success)
) 
 else if (( leb (get_allowance allowance  (_from) ((sender msg))) ((get_spentAllowance spentAllowance  (_from) ((sender msg))) + _value))) then ((MyToken, ether, success)
) 
 else let imap1 := match (IntMap.find _from balanceOf) with
 |None => 0
 | Some a => a end in
let balanceOf := IntMap.add _from (((get_balanceOf balanceOf  (_from)) - _value))balanceOf in
let imap1 := match (IntMap.find _to balanceOf) with
 |None => 0
 | Some a => a end in
let balanceOf := IntMap.add _to (((get_balanceOf balanceOf  (_to)) + _value))balanceOf in
let imap1 := match (IntMap.find _from spentAllowance) with
 |None => IntMap.empty (Z)
 | Some a => a end in
let imap2 := match (IntMap.find (sender msg) imap1) with
 |None => 0
 | Some a => a end in
let spentAllowance := IntMap.add _from (IntMap.add (sender msg) (((get_spentAllowance spentAllowance  (_from) ((sender msg))) + _value))imap1)spentAllowance in
((create_MyToken spentAllowance allowance balanceOf decimals symbol name), new_ether, success)
end.
Definition anonymous_function (MyToken : MyToken) (ether : EtherMap) (msg : Message) :=
let new_ether := ether in 
(MyToken, ether).
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

Definition mapping_function_balanceOf ( x : Z * Z) := 
 let new_gas := (Nat.pred new_gas) in
 (snd new_gas (create_MyToken spentAllowance allowance balanceOf decimals symbol name) new_ether msg (x)).
Fixpoint sum_balanceOf (maplist : list (Z * Z)) := 
 match maplist with
    | nil => 0
    | a::q => (mapping_function_balanceOf a) + (sum_balanceOf q)
end.
Lemma update_balanceOf : forall ( MyToken2 : MyToken ) (address : Z) (value : Z),
      let balance_map := (balanceOf MyToken2) in
      let original_value := match (IntMap.find address (balanceOf MyToken2)) with
      | None => 0
      | Some a => mapping_function_balanceOf(address, a) end in
      let balance2 := sum_balanceOf (IntMap.elements (IntMap.add address value balance_map)) in
      (sum_balanceOf (IntMap.elements balance_map)) + mapping_function_balanceOf(address, value) = balance2 + original_value.
      Proof.
      Opaque mapping_function_balanceOf.
      intros.
      case_eq (IntMap.find (elt := Z) address (balanceOf MyToken2)).
      intro t0.
      unfold balance2.
      unfold sum_balanceOf.
      simpl.
      unfold get_balanceOf.
      unfold balance_map.
      destruct (balanceOf MyToken2).
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
      assert (original_value = mapping_function_balanceOf (z0, z1)).
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
        | Some a => mapping_function_balanceOf (address, a)
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
      destruct (balanceOf MyToken2).
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
      unfold sum_balanceOf.
      rewrite -> Z.add_comm.
      symmetry.
      rewrite <- Z.add_assoc.
      apply plus_reg_r.
      rewrite -> Z.add_comm.
      simpl.
      reflexivity.
      simpl.
      assert (original_value = mapping_function_balanceOf (z, t0)).
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
      unfold sum_balanceOf.
      rewrite <- Z.add_assoc.
      symmetry.
      rewrite <- Z.add_assoc.
      symmetry.
      apply plus_reg_r.
      unfold sum_balanceOf in IHthis.
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
Theorem preservation_transferFrom_balanceOf : forall (MyToken : MyToken) (ether : EtherMap) (msg : Message)(_from:Z) (_to:Z) (_value:Z) , 
 let MyToken_2 :=  fst( transferFrom MyToken ether msg _from _to _value) in
 (sum_balanceOf (IntMap.elements (balanceOf MyToken))) = ( sum_balanceOf (IntMap.elements (balanceOf MyToken_2))).
Admitted.

Theorem preservation_transfer_balanceOf : forall (MyToken : MyToken) (ether : EtherMap) (msg : Message)(_to:Z) (_value:Z) , 
 let MyToken_2 :=  fst( transfer MyToken ether msg _to _value) in
 (sum_balanceOf (IntMap.elements (balanceOf MyToken))) = ( sum_balanceOf (IntMap.elements (balanceOf MyToken_2))).
Admitted.

