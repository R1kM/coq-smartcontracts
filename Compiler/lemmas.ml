module SMap = Map.Make(String)
let variables = ref [""]
let typenames = ref SMap.empty
let count = ref 0

let generate_helper_lemmas () = 
"Lemma plus_reg_r : forall (n m p : Z), n = m -> p+n= p+m.
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
Qed.\n\n"

let generate_extract_sorted_lemma () =
    let accu = SMap.bindings (!typenames) in
    let rec aux = function
        | [] -> ""
        | (typename, a) :: q ->
                    
"
Lemma extract_Sorted_"^a^" : forall (a b : Z*"^typename^") (l : list (Z * "^typename^")),
  Sorted.Sorted (IntMap.Raw.PX.ltk (elt:="^typename^")) (a::b::l) -> Sorted.Sorted (IntMap.Raw.PX.ltk (elt:="^typename^")) (b::l).
Proof.
  intros.
  apply Sorted.Sorted_inv in H.
  apply H.
Qed. \n\n" ^ aux q in
    aux accu

let generate_intermediate_lemmas an_var name typename = 
  if not (List.mem an_var (!variables)) then begin
      variables := an_var::(!variables);
      let gen_an_var = "("^an_var^" "^name^"2)" in
      let sorted_number = try (SMap.find typename (!typenames)) with
        |Not_found -> (typenames := SMap.add typename (string_of_int (!count)) (!typenames);
                        count := (!count) + 1;
                        (string_of_int ((!count) - 1))) in
      "Lemma update_"^an_var ^" : forall ( "^name ^"2 : "^name^" ) (address : Z) (value : "^typename^"),
      let balance_map := "^gen_an_var^" in
      let original_value := match (IntMap.find address "^gen_an_var^") with
      | None => 0
      | Some a => mapping_function_"^an_var^"(address, a) end in
      let balance2 := sum_"^an_var^" (IntMap.elements (IntMap.add address value balance_map)) in
      (sum_"^an_var^" (IntMap.elements balance_map)) + mapping_function_"^an_var^"(address, value) = balance2 + original_value.
      Proof.
      Opaque mapping_function_"^an_var^".
      intros.
      case_eq (IntMap.find (elt := "^typename^") address "^gen_an_var^").
      intro t0.
      unfold balance2.
      unfold sum_"^an_var^".
      simpl.
      unfold get_"^an_var^".
      unfold balance_map.
      destruct "^gen_an_var^".
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
      assert (IntMap.find (elt := "^typename^") address {| IntMap.this := (z0, z1) :: this; IntMap.sorted := sorted |} = None).
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
      assert (original_value = mapping_function_"^an_var^" (z0, z1)).
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
      assert (Sorted (IntMap.Raw.PX.ltk (elt := "^typename^")) this).
      induction this.
      auto.
      apply extract_Sorted_"^sorted_number^" with (a:=(z0, z1)).
      apply sorted.
      assert (original_value = match
        IntMap.find (elt := "^typename^") address {| IntMap.this := this; IntMap.sorted := H0 |} with
        | Some a => mapping_function_"^an_var^" (address, a)
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
      destruct "^gen_an_var^".
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
      unfold sum_"^an_var^".
      rewrite -> Z.add_comm.
      symmetry.
      rewrite <- Z.add_assoc.
      apply plus_reg_r.
      rewrite -> Z.add_comm.
      simpl.
      reflexivity.
      simpl.
      assert (original_value = mapping_function_"^an_var^" (z, t0)).
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
      unfold sum_"^an_var^".
      rewrite <- Z.add_assoc.
      symmetry.
      rewrite <- Z.add_assoc.
      symmetry.
      apply plus_reg_r.
      unfold sum_"^an_var^" in IHthis.
      assert (Sorted (IntMap.Raw.PX.ltk (elt := "^typename^")) this).
      induction this.
      auto.
      apply extract_Sorted_"^sorted_number^" with (a:= (z, t0)).
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
      assert (IntMap.find (elt := "^typename^") address {| IntMap.this := this; IntMap.sorted := H1 |} = None).
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
      Qed.\n"
  end else ""  
