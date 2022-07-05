open Alcotest
open Pi4
open Syntax

let test_bit_list_of_string () =
  Alcotest.(check (list Testable.bit))
    "Same lists of bits"
    [ Bit.One; Bit.Zero; Bit.One; Bit.One ]
    (Bit.bit_list_of_string "1011")

let test_bitvec_of_bit_str () =
  Alcotest.(check Testable.bitvector)
    "Same bitvector"
    BitVector.(Cons (Bit.One, Cons (Bit.Zero, Nil)))
    (BitVector.of_bit_str "10")

let test_bitvec_of_hex_str () =
  Alcotest.(check Testable.bitvector)
    "Same bitvector"
    BitVector.(
      Cons
        ( Bit.Zero,
          Cons
            ( Bit.Zero,
              Cons
                ( Bit.One,
                  Cons
                    ( Bit.Zero,
                      Cons
                        ( Bit.Zero,
                          Cons (Bit.Zero, Cons (Bit.One, Cons (Bit.One, Nil)))
                        ) ) ) ) ))
    (BitVector.of_hex_str "23")

let test_concat_bitvec () =
  Alcotest.(check Testable.bitvector)
    "Same bitvector"
    BitVector.(
      Cons (Bit.One, Cons (Bit.One, Cons (Bit.Zero, Cons (Bit.One, Nil)))))
    (BitVector.concat
       BitVector.(Cons (Bit.One, Cons (Bit.One, Nil)))
       BitVector.(Cons (Bit.Zero, Cons (Bit.One, Nil))))

let test_set =
  [ test_case "Bit list of string" `Quick test_bit_list_of_string;
    test_case "Bitvector of bit string" `Quick test_bitvec_of_bit_str;
    test_case "Bitvector of hex string" `Quick test_bitvec_of_hex_str;
    test_case "Concat bitvectors" `Quick test_concat_bitvec
  ]
