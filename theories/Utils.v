From Coq Require Import PrimString List NArith.BinNat Uint63.
Import ListNotations.
Open Scope pstring.

(** Convert a base-2 number to a string. *)
Definition string_of_binary (n : BinNums.N) : string :=
  let fix digits acc n :=
    match n with 
    | xH => "1" :: acc
    | xO n0 => digits ("0" :: acc) n0
    | xI n0 => digits ("1" :: acc) n0
    end
  in 
  match n with 
  | N0 => "0"
  | Npos n => List.fold_left PrimString.cat (digits [] n) ""
  end.

(** Convert a base-10 number to a string. *)
Fixpoint string_of_decimal (n : Decimal.uint) : string :=
  match n with
  | Decimal.Nil => ""
  | Decimal.D0 n0 => PrimString.cat  "0" (string_of_decimal n0)
  | Decimal.D1 n0 => PrimString.cat  "1" (string_of_decimal n0)
  | Decimal.D2 n0 => PrimString.cat  "2" (string_of_decimal n0)
  | Decimal.D3 n0 => PrimString.cat  "3" (string_of_decimal n0)
  | Decimal.D4 n0 => PrimString.cat  "4" (string_of_decimal n0)
  | Decimal.D5 n0 => PrimString.cat  "5" (string_of_decimal n0)
  | Decimal.D6 n0 => PrimString.cat  "6" (string_of_decimal n0)
  | Decimal.D7 n0 => PrimString.cat  "7" (string_of_decimal n0)
  | Decimal.D8 n0 => PrimString.cat  "8" (string_of_decimal n0)
  | Decimal.D9 n0 => PrimString.cat  "9" (string_of_decimal n0)
  end.

(** Convert a base-16 number to a string. *)
Fixpoint string_of_hexadecimal (n : Hexadecimal.uint) : string :=
  match n with
  | Hexadecimal.Nil => ""
  | Hexadecimal.D0 n0 => PrimString.cat  "0" (string_of_hexadecimal n0)
  | Hexadecimal.D1 n0 => PrimString.cat  "1" (string_of_hexadecimal n0)
  | Hexadecimal.D2 n0 => PrimString.cat  "2" (string_of_hexadecimal n0)
  | Hexadecimal.D3 n0 => PrimString.cat  "3" (string_of_hexadecimal n0)
  | Hexadecimal.D4 n0 => PrimString.cat  "4" (string_of_hexadecimal n0)
  | Hexadecimal.D5 n0 => PrimString.cat  "5" (string_of_hexadecimal n0)
  | Hexadecimal.D6 n0 => PrimString.cat  "6" (string_of_hexadecimal n0)
  | Hexadecimal.D7 n0 => PrimString.cat  "7" (string_of_hexadecimal n0)
  | Hexadecimal.D8 n0 => PrimString.cat  "8" (string_of_hexadecimal n0)
  | Hexadecimal.D9 n0 => PrimString.cat  "9" (string_of_hexadecimal n0)
  | Hexadecimal.Da n0 => PrimString.cat  "A" (string_of_hexadecimal n0)
  | Hexadecimal.Db n0 => PrimString.cat  "B" (string_of_hexadecimal n0)
  | Hexadecimal.Dc n0 => PrimString.cat  "C" (string_of_hexadecimal n0)
  | Hexadecimal.Dd n0 => PrimString.cat  "D" (string_of_hexadecimal n0)
  | Hexadecimal.De n0 => PrimString.cat  "E" (string_of_hexadecimal n0)
  | Hexadecimal.Df n0 => PrimString.cat  "F" (string_of_hexadecimal n0)
  end.

(** [utf8_length s] counts the number of code points that occur in [s],
    assuming a UTF8 encoding. In general this might be smaller than the number
    of bytes in [s] : each code point is encoded using 1 to 4 bytes. *)
Definition utf8_length (str : string) : nat :=
  let len := PrimString.length str in
  (* [i] is the index of the byte we are looking at.
     [fuel] is used to make [loop] structurally recursive. *)
  let fix loop (acc : nat) (i : int) (fuel : nat) :=
    match fuel with 
    | 0 => (* This should not happen. *) acc 
    | S fuel =>
      (* Check if we are done. *)
      if (len <=? i)%uint63 then acc else 
      (* Compute the number of bytes that the current code point spans. *)
      let byte_count := 
        let byte := get str i in
        if      (byte <? 128)%uint63 then 1%int63
        else if (byte <? 224)%uint63 then 2%int63
        else if (byte <? 240)%uint63 then 3%int63
        else 4%int63
      in 
      (* Continue on the next code point. *)
      loop (S acc) (i + byte_count)%uint63 fuel
    end
  in
  loop 0%nat 0%int63 (Uint63.to_nat (PrimString.length str)).
      
      