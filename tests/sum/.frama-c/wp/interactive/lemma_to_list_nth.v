(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require HighOrd.
Require bool.Bool.
Require int.Int.
Require int.Abs.
Require int.ComputerDivision.
Require real.Real.
Require real.RealInfix.
Require real.FromInt.
Require map.Map.

Parameter eqb:
  forall {a:Type} {a_WT:WhyType a}, a -> a -> Init.Datatypes.bool.

Axiom eqb1 :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:a) (y:a), ((eqb x y) = Init.Datatypes.true) <-> (x = y).

Axiom eqb_false :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:a) (y:a), ((eqb x y) = Init.Datatypes.false) <-> ~ (x = y).

Parameter neqb:
  forall {a:Type} {a_WT:WhyType a}, a -> a -> Init.Datatypes.bool.

Axiom neqb1 :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:a) (y:a), ((neqb x y) = Init.Datatypes.true) <-> ~ (x = y).

Parameter zlt: Numbers.BinNums.Z -> Numbers.BinNums.Z -> Init.Datatypes.bool.

Parameter zleq:
  Numbers.BinNums.Z -> Numbers.BinNums.Z -> Init.Datatypes.bool.

Axiom zlt1 :
  forall (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z),
  ((zlt x y) = Init.Datatypes.true) <-> (x < y)%Z.

Axiom zleq1 :
  forall (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z),
  ((zleq x y) = Init.Datatypes.true) <-> (x <= y)%Z.

Parameter rlt:
  Reals.Rdefinitions.R -> Reals.Rdefinitions.R -> Init.Datatypes.bool.

Parameter rleq:
  Reals.Rdefinitions.R -> Reals.Rdefinitions.R -> Init.Datatypes.bool.

Axiom rlt1 :
  forall (x:Reals.Rdefinitions.R) (y:Reals.Rdefinitions.R),
  ((rlt x y) = Init.Datatypes.true) <-> (x < y)%R.

Axiom rleq1 :
  forall (x:Reals.Rdefinitions.R) (y:Reals.Rdefinitions.R),
  ((rleq x y) = Init.Datatypes.true) <-> (x <= y)%R.

(* Why3 assumption *)
Definition real_of_int (x:Numbers.BinNums.Z) : Reals.Rdefinitions.R :=
  BuiltIn.IZR x.

Axiom c_euclidian :
  forall (n:Numbers.BinNums.Z) (d:Numbers.BinNums.Z), ~ (d = 0%Z) ->
  (n = (((ZArith.BinInt.Z.quot n d) * d)%Z + (ZArith.BinInt.Z.rem n d))%Z).

Axiom cmod_remainder :
  forall (n:Numbers.BinNums.Z) (d:Numbers.BinNums.Z),
  ((0%Z <= n)%Z -> (0%Z < d)%Z ->
   (0%Z <= (ZArith.BinInt.Z.rem n d))%Z /\ ((ZArith.BinInt.Z.rem n d) < d)%Z) /\
  ((n <= 0%Z)%Z -> (0%Z < d)%Z ->
   ((-d)%Z < (ZArith.BinInt.Z.rem n d))%Z /\
   ((ZArith.BinInt.Z.rem n d) <= 0%Z)%Z) /\
  ((0%Z <= n)%Z -> (d < 0%Z)%Z ->
   (0%Z <= (ZArith.BinInt.Z.rem n d))%Z /\
   ((ZArith.BinInt.Z.rem n d) < (-d)%Z)%Z) /\
  ((n <= 0%Z)%Z -> (d < 0%Z)%Z ->
   (d < (ZArith.BinInt.Z.rem n d))%Z /\ ((ZArith.BinInt.Z.rem n d) <= 0%Z)%Z).

Axiom cdiv_neutral :
  forall (a:Numbers.BinNums.Z), ((ZArith.BinInt.Z.quot a 1%Z) = a).

Axiom cdiv_inv :
  forall (a:Numbers.BinNums.Z), ~ (a = 0%Z) ->
  ((ZArith.BinInt.Z.quot a a) = 1%Z).

Axiom cdiv_closed_remainder :
  forall (a:Numbers.BinNums.Z) (b:Numbers.BinNums.Z) (n:Numbers.BinNums.Z),
  (0%Z <= a)%Z -> (0%Z <= b)%Z ->
  (0%Z <= (b - a)%Z)%Z /\ ((b - a)%Z < n)%Z ->
  ((ZArith.BinInt.Z.rem a n) = (ZArith.BinInt.Z.rem b n)) -> (a = b).

(* Why3 assumption *)
Inductive addr :=
  | addr'mk : Numbers.BinNums.Z -> Numbers.BinNums.Z -> addr.
Axiom addr_WhyType : WhyType addr.
Existing Instance addr_WhyType.

(* Why3 assumption *)
Definition offset (v:addr) : Numbers.BinNums.Z :=
  match v with
  | addr'mk x x1 => x1
  end.

(* Why3 assumption *)
Definition base (v:addr) : Numbers.BinNums.Z :=
  match v with
  | addr'mk x x1 => x
  end.

Parameter addr_le: addr -> addr -> Prop.

Parameter addr_lt: addr -> addr -> Prop.

Parameter addr_le_bool: addr -> addr -> Init.Datatypes.bool.

Parameter addr_lt_bool: addr -> addr -> Init.Datatypes.bool.

Axiom addr_le_def :
  forall (p:addr) (q:addr), ((base p) = (base q)) ->
  addr_le p q <-> ((offset p) <= (offset q))%Z.

Axiom addr_lt_def :
  forall (p:addr) (q:addr), ((base p) = (base q)) ->
  addr_lt p q <-> ((offset p) < (offset q))%Z.

Axiom addr_le_bool_def :
  forall (p:addr) (q:addr),
  addr_le p q <-> ((addr_le_bool p q) = Init.Datatypes.true).

Axiom addr_lt_bool_def :
  forall (p:addr) (q:addr),
  addr_lt p q <-> ((addr_lt_bool p q) = Init.Datatypes.true).

(* Why3 assumption *)
Definition null : addr := addr'mk 0%Z 0%Z.

(* Why3 assumption *)
Definition global (b:Numbers.BinNums.Z) : addr := addr'mk b 0%Z.

(* Why3 assumption *)
Definition shift (p:addr) (k:Numbers.BinNums.Z) : addr :=
  addr'mk (base p) ((offset p) + k)%Z.

(* Why3 assumption *)
Definition included (p:addr) (a:Numbers.BinNums.Z) (q:addr)
    (b:Numbers.BinNums.Z) : Prop :=
  (0%Z < a)%Z ->
  (0%Z <= b)%Z /\
  ((base p) = (base q)) /\
  ((offset q) <= (offset p))%Z /\
  (((offset p) + a)%Z <= ((offset q) + b)%Z)%Z.

(* Why3 assumption *)
Definition separated (p:addr) (a:Numbers.BinNums.Z) (q:addr)
    (b:Numbers.BinNums.Z) : Prop :=
  (a <= 0%Z)%Z \/
  (b <= 0%Z)%Z \/
  ~ ((base p) = (base q)) \/
  (((offset q) + b)%Z <= (offset p))%Z \/
  (((offset p) + a)%Z <= (offset q))%Z.

(* Why3 assumption *)
Definition eqmem {a:Type} {a_WT:WhyType a} (m1:addr -> a) (m2:addr -> a)
    (p:addr) (a1:Numbers.BinNums.Z) : Prop :=
  forall (q:addr), included q 1%Z p a1 -> ((m1 q) = (m2 q)).

Parameter havoc:
  forall {a:Type} {a_WT:WhyType a}, (addr -> a) -> (addr -> a) -> addr ->
  Numbers.BinNums.Z -> addr -> a.

(* Why3 assumption *)
Definition valid_rw (m:Numbers.BinNums.Z -> Numbers.BinNums.Z) (p:addr)
    (n:Numbers.BinNums.Z) : Prop :=
  (0%Z < n)%Z ->
  (0%Z < (base p))%Z /\
  (0%Z <= (offset p))%Z /\ (((offset p) + n)%Z <= (m (base p)))%Z.

(* Why3 assumption *)
Definition valid_rd (m:Numbers.BinNums.Z -> Numbers.BinNums.Z) (p:addr)
    (n:Numbers.BinNums.Z) : Prop :=
  (0%Z < n)%Z ->
  ~ (0%Z = (base p)) /\
  (0%Z <= (offset p))%Z /\ (((offset p) + n)%Z <= (m (base p)))%Z.

(* Why3 assumption *)
Definition valid_obj (m:Numbers.BinNums.Z -> Numbers.BinNums.Z) (p:addr)
    (n:Numbers.BinNums.Z) : Prop :=
  (0%Z < n)%Z ->
  (p = null) \/
  ~ (0%Z = (base p)) /\
  (0%Z <= (offset p))%Z /\ (((offset p) + n)%Z <= (1%Z + (m (base p)))%Z)%Z.

(* Why3 assumption *)
Definition invalid (m:Numbers.BinNums.Z -> Numbers.BinNums.Z) (p:addr)
    (n:Numbers.BinNums.Z) : Prop :=
  (n <= 0%Z)%Z \/
  ((base p) = 0%Z) \/
  ((m (base p)) <= (offset p))%Z \/ (((offset p) + n)%Z <= 0%Z)%Z.

Axiom valid_rw_rd :
  forall (m:Numbers.BinNums.Z -> Numbers.BinNums.Z), forall (p:addr),
  forall (n:Numbers.BinNums.Z), valid_rw m p n -> valid_rd m p n.

Axiom valid_string :
  forall (m:Numbers.BinNums.Z -> Numbers.BinNums.Z), forall (p:addr),
  ((base p) < 0%Z)%Z ->
  (0%Z <= (offset p))%Z /\ ((offset p) < (m (base p)))%Z ->
  valid_rd m p 1%Z /\ ~ valid_rw m p 1%Z.

Axiom separated_1 :
  forall (p:addr) (q:addr),
  forall (a:Numbers.BinNums.Z) (b:Numbers.BinNums.Z) (i:Numbers.BinNums.Z)
    (j:Numbers.BinNums.Z),
  separated p a q b -> ((offset p) <= i)%Z /\ (i < ((offset p) + a)%Z)%Z ->
  ((offset q) <= j)%Z /\ (j < ((offset q) + b)%Z)%Z ->
  ~ ((addr'mk (base p) i) = (addr'mk (base q) j)).

Parameter region: Numbers.BinNums.Z -> Numbers.BinNums.Z.

Parameter linked: (Numbers.BinNums.Z -> Numbers.BinNums.Z) -> Prop.

Parameter sconst: (addr -> Numbers.BinNums.Z) -> Prop.

(* Why3 assumption *)
Definition framed (m:addr -> addr) : Prop :=
  forall (p:addr), ((region (base p)) <= 0%Z)%Z ->
  ((region (base (m p))) <= 0%Z)%Z.

Axiom separated_included :
  forall (p:addr) (q:addr),
  forall (a:Numbers.BinNums.Z) (b:Numbers.BinNums.Z), (0%Z < a)%Z ->
  (0%Z < b)%Z -> separated p a q b -> ~ included p a q b.

Axiom included_trans :
  forall (p:addr) (q:addr) (r:addr),
  forall (a:Numbers.BinNums.Z) (b:Numbers.BinNums.Z) (c:Numbers.BinNums.Z),
  included p a q b -> included q b r c -> included p a r c.

Axiom separated_trans :
  forall (p:addr) (q:addr) (r:addr),
  forall (a:Numbers.BinNums.Z) (b:Numbers.BinNums.Z) (c:Numbers.BinNums.Z),
  included p a q b -> separated q b r c -> separated p a r c.

Axiom separated_sym :
  forall (p:addr) (q:addr),
  forall (a:Numbers.BinNums.Z) (b:Numbers.BinNums.Z),
  separated p a q b <-> separated q b p a.

Axiom eqmem_included :
  forall {a:Type} {a_WT:WhyType a},
  forall (m1:addr -> a) (m2:addr -> a), forall (p:addr) (q:addr),
  forall (a1:Numbers.BinNums.Z) (b:Numbers.BinNums.Z), included p a1 q b ->
  eqmem m1 m2 q b -> eqmem m1 m2 p a1.

Axiom eqmem_sym :
  forall {a:Type} {a_WT:WhyType a},
  forall (m1:addr -> a) (m2:addr -> a), forall (p:addr),
  forall (a1:Numbers.BinNums.Z), eqmem m1 m2 p a1 -> eqmem m2 m1 p a1.

Axiom havoc_access :
  forall {a:Type} {a_WT:WhyType a},
  forall (m0:addr -> a) (m1:addr -> a), forall (q:addr) (p:addr),
  forall (a1:Numbers.BinNums.Z),
  (separated q 1%Z p a1 -> ((havoc m0 m1 p a1 q) = (m1 q))) /\
  (~ separated q 1%Z p a1 -> ((havoc m0 m1 p a1 q) = (m0 q))).

Parameter cinits: (addr -> Init.Datatypes.bool) -> Prop.

(* Why3 assumption *)
Definition is_init_range (m:addr -> Init.Datatypes.bool) (p:addr)
    (l:Numbers.BinNums.Z) : Prop :=
  forall (i:Numbers.BinNums.Z), (0%Z <= i)%Z /\ (i < l)%Z ->
  ((m (shift p i)) = Init.Datatypes.true).

Parameter set_init:
  (addr -> Init.Datatypes.bool) -> addr -> Numbers.BinNums.Z ->
  addr -> Init.Datatypes.bool.

Axiom set_init_access :
  forall (m:addr -> Init.Datatypes.bool), forall (q:addr) (p:addr),
  forall (a:Numbers.BinNums.Z),
  (separated q 1%Z p a -> ((set_init m p a q) = (m q))) /\
  (~ separated q 1%Z p a -> ((set_init m p a q) = Init.Datatypes.true)).

(* Why3 assumption *)
Definition monotonic_init (m1:addr -> Init.Datatypes.bool)
    (m2:addr -> Init.Datatypes.bool) : Prop :=
  forall (p:addr), ((m1 p) = Init.Datatypes.true) ->
  ((m2 p) = Init.Datatypes.true).

Parameter int_of_addr: addr -> Numbers.BinNums.Z.

Parameter addr_of_int: Numbers.BinNums.Z -> addr.

Axiom table : Type.
Parameter table_WhyType : WhyType table.
Existing Instance table_WhyType.

Parameter table_of_base: Numbers.BinNums.Z -> table.

Parameter table_to_offset: table -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom table_to_offset_zero :
  forall (t:table), ((table_to_offset t 0%Z) = 0%Z).

Axiom table_to_offset_monotonic :
  forall (t:table), forall (o1:Numbers.BinNums.Z) (o2:Numbers.BinNums.Z),
  (o1 <= o2)%Z <-> ((table_to_offset t o1) <= (table_to_offset t o2))%Z.

Axiom int_of_addr_bijection :
  forall (a:Numbers.BinNums.Z), ((int_of_addr (addr_of_int a)) = a).

Axiom addr_of_int_bijection :
  forall (p:addr), ((addr_of_int (int_of_addr p)) = p).

Axiom addr_of_null : ((int_of_addr null) = 0%Z).

Axiom list : forall (a:Type), Type.
Parameter list_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (list a).
Existing Instance list_WhyType.

Parameter nil: forall {a:Type} {a_WT:WhyType a}, list a.

Parameter cons: forall {a:Type} {a_WT:WhyType a}, a -> list a -> list a.

Parameter concat:
  forall {a:Type} {a_WT:WhyType a}, list a -> list a -> list a.

Parameter repeat:
  forall {a:Type} {a_WT:WhyType a}, list a -> Numbers.BinNums.Z -> list a.

Parameter length:
  forall {a:Type} {a_WT:WhyType a}, list a -> Numbers.BinNums.Z.

Parameter nth:
  forall {a:Type} {a_WT:WhyType a}, list a -> Numbers.BinNums.Z -> a.

Axiom length_pos :
  forall {a:Type} {a_WT:WhyType a}, forall (w:list a), (0%Z <= (length w))%Z.

Axiom length_nil :
  forall {a:Type} {a_WT:WhyType a}, ((length (nil : list a)) = 0%Z).

Axiom length_nil_bis :
  forall {a:Type} {a_WT:WhyType a},
  forall (w:list a), ((length w) = 0%Z) -> (w = (nil : list a)).

Axiom length_cons :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:a) (w:list a), ((length (cons x w)) = (1%Z + (length w))%Z).

Axiom length_concat :
  forall {a:Type} {a_WT:WhyType a},
  forall (u:list a) (v:list a),
  ((length (concat u v)) = ((length u) + (length v))%Z).

Axiom length_repeat :
  forall {a:Type} {a_WT:WhyType a},
  forall (w:list a) (n:Numbers.BinNums.Z), (0%Z <= n)%Z ->
  ((length (repeat w n)) = (n * (length w))%Z).

Axiom nth_cons :
  forall {a:Type} {a_WT:WhyType a},
  forall (k:Numbers.BinNums.Z) (x:a) (w:list a),
  ((k = 0%Z) -> ((nth (cons x w) k) = x)) /\
  (~ (k = 0%Z) -> ((nth (cons x w) k) = (nth w (k - 1%Z)%Z))).

Axiom nth_concat :
  forall {a:Type} {a_WT:WhyType a},
  forall (u:list a) (v:list a) (k:Numbers.BinNums.Z),
  ((k < (length u))%Z -> ((nth (concat u v) k) = (nth u k))) /\
  (~ (k < (length u))%Z ->
   ((nth (concat u v) k) = (nth v (k - (length u))%Z))).

Axiom nth_repeat :
  forall {a:Type} {a_WT:WhyType a},
  forall (n:Numbers.BinNums.Z) (k:Numbers.BinNums.Z) (w:list a),
  (0%Z <= k)%Z /\ (k < (n * (length w))%Z)%Z -> (0%Z < (length w))%Z ->
  ((nth (repeat w n) k) = (nth w (ZArith.BinInt.Z.rem k (length w)))).

(* Why3 assumption *)
Definition vlist_eq {a:Type} {a_WT:WhyType a} (u:list a) (v:list a) : Prop :=
  ((length u) = (length v)) /\
  (forall (i:Numbers.BinNums.Z), (0%Z <= i)%Z /\ (i < (length u))%Z ->
   ((nth u i) = (nth v i))).

Axiom extensionality :
  forall {a:Type} {a_WT:WhyType a},
  forall (u:list a) (v:list a), vlist_eq u v -> (u = v).

Axiom eq_nil_concat :
  forall {a:Type} {a_WT:WhyType a},
  forall (w:list a),
  vlist_eq (concat (nil : list a) w) w /\
  vlist_eq (concat w (nil : list a)) w.

Axiom rw_nil_concat_left :
  forall {a:Type} {a_WT:WhyType a},
  forall (w:list a), ((concat (nil : list a) w) = w).

Axiom rw_nil_concat_right :
  forall {a:Type} {a_WT:WhyType a},
  forall (w:list a), ((concat w (nil : list a)) = w).

Axiom eq_cons_concat :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:a) (v:list a) (w:list a),
  vlist_eq (concat (cons x v) w) (cons x (concat v w)).

Axiom rw_cons_concat :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:a) (v:list a) (w:list a),
  ((concat (cons x v) w) = (cons x (concat v w))).

Axiom rw_nil_cons_concat :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:a) (w:list a), ((concat (cons x (nil : list a)) w) = (cons x w)).

Axiom eq_assoc_concat :
  forall {a:Type} {a_WT:WhyType a},
  forall (u:list a) (v:list a) (w:list a),
  vlist_eq (concat (concat u v) w) (concat u (concat v w)).

Axiom rw_nil_repeat :
  forall {a:Type} {a_WT:WhyType a},
  forall (n:Numbers.BinNums.Z), (0%Z <= n)%Z ->
  ((repeat (nil : list a) n) = (nil : list a)).

Axiom rw_repeat_zero :
  forall {a:Type} {a_WT:WhyType a},
  forall (w:list a), ((repeat w 0%Z) = (nil : list a)).

Axiom eq_repeat_one :
  forall {a:Type} {a_WT:WhyType a},
  forall (w:list a), vlist_eq (repeat w 1%Z) w.

Axiom rw_repeat_one :
  forall {a:Type} {a_WT:WhyType a}, forall (w:list a), ((repeat w 1%Z) = w).

Axiom eq_repeat_concat :
  forall {a:Type} {a_WT:WhyType a},
  forall (p:Numbers.BinNums.Z) (q:Numbers.BinNums.Z) (w:list a),
  (0%Z <= p)%Z -> (0%Z <= q)%Z ->
  vlist_eq (repeat w (p + q)%Z) (concat (repeat w p) (repeat w q)).

Axiom rw_repeat_concat :
  forall {a:Type} {a_WT:WhyType a},
  forall (p:Numbers.BinNums.Z) (q:Numbers.BinNums.Z) (w:list a),
  (0%Z <= p)%Z -> (0%Z <= q)%Z ->
  ((repeat w (p + q)%Z) = (concat (repeat w p) (repeat w q))).

Axiom rw_repeat_after :
  forall {a:Type} {a_WT:WhyType a},
  forall (p:Numbers.BinNums.Z) (w:list a), (0%Z <= p)%Z ->
  ((concat (repeat w p) w) = (repeat w (p + 1%Z)%Z)).

Axiom rw_repeat_before :
  forall {a:Type} {a_WT:WhyType a},
  forall (p:Numbers.BinNums.Z) (w:list a), (0%Z <= p)%Z ->
  ((concat w (repeat w p)) = (repeat w (p + 1%Z)%Z)).

Parameter repeat_box:
  forall {a:Type} {a_WT:WhyType a}, list a -> Numbers.BinNums.Z -> list a.

Axiom rw_repeat_box_unfold :
  forall {a:Type} {a_WT:WhyType a},
  forall (w:list a) (n:Numbers.BinNums.Z), ((repeat_box w n) = (repeat w n)).

Axiom rw_repeat_plus_box_unfold :
  forall {a:Type} {a_WT:WhyType a},
  forall (w:list a) (a1:Numbers.BinNums.Z) (b:Numbers.BinNums.Z),
  (0%Z <= a1)%Z -> (0%Z <= b)%Z ->
  ((repeat_box w (a1 + b)%Z) = (concat (repeat w a1) (repeat w b))).

Axiom rw_repeat_plus_one_box_unfold :
  forall {a:Type} {a_WT:WhyType a},
  forall (w:list a) (n:Numbers.BinNums.Z), (0%Z < n)%Z ->
  ((repeat_box w n) = (concat (repeat w (n - 1%Z)%Z) w)) /\
  ((repeat_box w (n + 1%Z)%Z) = (concat (repeat w n) w)).

Parameter L_to_list:
  (addr -> Numbers.BinNums.Z) -> addr -> Numbers.BinNums.Z ->
  Numbers.BinNums.Z -> list Numbers.BinNums.Z.

Axiom Q_to_list_concat :
  forall (Mint:addr -> Numbers.BinNums.Z) (a:addr) (i:Numbers.BinNums.Z)
    (k:Numbers.BinNums.Z) (n:Numbers.BinNums.Z),
  (i <= k)%Z -> (k <= n)%Z ->
  ((L_to_list Mint a i n) =
   (concat (L_to_list Mint a i k) (L_to_list Mint a k n))).

Axiom Q_to_list_length :
  forall (Mint:addr -> Numbers.BinNums.Z) (a:addr) (i:Numbers.BinNums.Z)
    (n:Numbers.BinNums.Z),
  (i <= n)%Z -> ((i + (length (L_to_list Mint a i n)))%Z = n).

Axiom Q_to_list_cons :
  forall (Mint:addr -> Numbers.BinNums.Z) (a:addr) (i:Numbers.BinNums.Z)
    (n:Numbers.BinNums.Z),
  let x := ((-1%Z)%Z + n)%Z in
  (i < n)%Z ->
  ((L_to_list Mint a i n) =
   (concat (L_to_list Mint a i x)
    (cons (Mint (shift a x)) (nil : list Numbers.BinNums.Z)))).

Axiom Q_to_list_empty :
  forall (Mint:addr -> Numbers.BinNums.Z) (a:addr) (i:Numbers.BinNums.Z)
    (n:Numbers.BinNums.Z),
  (n <= i)%Z -> ((L_to_list Mint a i n) = (nil : list Numbers.BinNums.Z)).

(* Why3 goal *)
Theorem wp_goal :
  forall (t:addr -> Numbers.BinNums.Z) (a:addr) (i:Numbers.BinNums.Z)
    (i1:Numbers.BinNums.Z) (i2:Numbers.BinNums.Z),
  let x := (i + i2)%Z in
  (0%Z <= i2)%Z -> (i < i1)%Z -> (x < i1)%Z ->
  ((t (shift a x)) = (nth (L_to_list t a i i1) i2)).
(* Why3 intros t a i i1 i2 x h1 h2 h3. *)
Proof.
intros.
unfold x.
unfold x in H1.
clear x.
generalize dependent i.
apply Zlt_lower_bound_ind with
  (P:= fun k => 
  forall i : int, (i < i1)%Z -> (i + k < i1)%Z ->
  t (shift a ( i + k)) = nth (L_to_list t a i i1) k)
  ( z:= 0%Z); [ | Lia.lia].
intros.
rewrite (Q_to_list_concat t a i (i+1)%Z i1) by Lia.lia.
assert ( H4: (0 = x \/ 0 < x)%Z) by Lia.lia.
assert (H5: (length (L_to_list t a i (i + 1)))%Z = 1%Z).
    { rewrite <- (Z.add_cancel_l _ _ i).
      rewrite Q_to_list_length by Lia.lia.
      reflexivity.
    }
destruct H4.
* rewrite <- H4.
  specialize (nth_concat(L_to_list t a i (i+1)) 
             ((L_to_list t a (i + 1) i1))
             0).
  intros H6 ;destruct H6 as (H6 & _).
  rewrite H6;[ | rewrite H5; Lia.lia].
  rewrite Q_to_list_cons by Lia.lia.
  rewrite Q_to_list_empty by Lia.lia.
  rewrite rw_nil_concat_left.
  replace (- (1) + (i + 1))%Z with (i)%Z by Lia.lia.
  specialize (nth_cons 0 (t (shift a i)) nil).
  intros H7 ;destruct H7 as (H7 & _).
  rewrite H7 by Lia.lia.
  replace (i + 0)%Z with i by Lia.lia.
  reflexivity.
* specialize (nth_concat(L_to_list t a i (i+1)) 
             ((L_to_list t a (i + 1) i1))
             x).
  intros H6 ;destruct H6 as (_ & H6).
  rewrite H6; [ | rewrite H5; Lia.lia].
  rewrite H5.
  rewrite <- H0; [ | Lia.lia | Lia.lia | Lia.lia].
  replace ((i + 1 + (x - 1)))%Z with (i + x)%Z by Lia.lia.
  reflexivity.
Qed.

