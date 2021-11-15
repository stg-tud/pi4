open Alcotest
open Pi4
open Syntax
open Expression

let test_bv_l () =
  Alcotest.(check Testable.term)
    "terms are equal"
    (BvExpr (Bv (Cons (B 0, Cons (B 1, Cons (B 2, Nil))))))
    (BvExpr (bv_l [ B 0; B 1; B 2 ]))

let test_bv_s () =
  Alcotest.(check Testable.term)
    "terms are equal"
    (BvExpr
       (Bv
          (Cons
             ( One,
               Cons
                 ( Zero,
                   Cons
                     ( One,
                       Cons
                         ( One,
                           Cons (One, Cons (Zero, Cons (Zero, Cons (Zero, Nil))))
                         ) ) ) ))))
    (BvExpr (bv_s "10111000"))

let test_bv_x () =
  Alcotest.(check Testable.term)
    "terms are equal"
    (BvExpr
       (Bv
          (Cons
             ( One,
               Cons
                 ( Zero,
                   Cons
                     ( One,
                       Cons
                         ( Zero,
                           Cons (Zero, Cons (Zero, Cons (Zero, Cons (One, Nil))))
                         ) ) ) ))))
    (BvExpr (bv_x "a1"))

let test_bv_of_hex_str () =
  Alcotest.(check Testable.bitvector)
    "bitvectors are equal"
    (Cons
       ( One,
         Cons
           ( Zero,
             Cons
               ( One,
                 Cons
                   (Zero, Cons (Zero, Cons (Zero, Cons (Zero, Cons (One, Nil)))))
               ) ) ))
    (BitVector.of_hex_str "a1")

let test_bit_list_of_string () =
  Alcotest.(check (list Testable.bit))
    "lists are equal" [ One; Zero; One; One ]
    (Bit.bit_list_of_string "1011")

let test_bv_of_bit_list () =
  Alcotest.(check Testable.bitvector)
    "bitvectors are equal"
    (Cons (One, Cons (Zero, Cons (One, Cons (One, Nil)))))
    (BitVector.of_bit_list [ One; Zero; One; One ])

let test_bv_of_bit_str () =
  Alcotest.(check Testable.bitvector)
    "bitvectors are equal"
    (Cons (One, Cons (Zero, Cons (One, Cons (One, Nil)))))
    (BitVector.of_bit_str "1011")

let test_set =
  [ test_case "bv_l is correct" `Quick test_bv_l;
    test_case "bv_s is correct" `Quick test_bv_s;
    test_case "bv_x is correct" `Quick test_bv_x;
    test_case "bv_of_hex_str is correct" `Quick test_bv_of_hex_str;
    test_case "bit_list_of_string is correct" `Quick test_bit_list_of_string;
    test_case "bv_of_bit_list is correct" `Quick test_bv_of_bit_list;
    test_case "bv_of_bit_str is correct" `Quick test_bv_of_bit_str
  ]
