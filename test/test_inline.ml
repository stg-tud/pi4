open Alcotest

module TestConfig = struct
  let verbose = true
  let maxlen = 256
end

module Test = Test_utils.TestRunner (TestConfig)

let test_reassign_field () = 
  let program = {|
    header_type ether_t {
      dst: 48;
      src: 48;
      etherType: 16;
    }
    header ether : ether_t

    extract(ether);
    ether.etherType := (0x6@ether[100:112])
  |} in
  Test.check_program Test.typecheck program "(x:{x:ε|x.pkt_in.length > 111 ∧ x.pkt_in[96:112] == 0x0800}) → {y:ether|y.ether.etherType == 0x0806}"

let test_set = [
  test_case "Reassign field" `Quick test_reassign_field
]
