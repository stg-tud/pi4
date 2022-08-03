open Alcotest
open Pi4
open Syntax


let ether_inst =
  Test_utils.mk_inst "ether" 
  [
   ("dstAddr", 48);
   ("srcAddr", 48);
   ("etherType", 16);
 ]
let ipv4_inst =
 Test_utils.mk_inst "ipv4" 
 [
  ("version", 4);
  ("ihl", 4);
  ("tos", 8);
  ("len", 16);
  ("id", 16);
  ("flags", 3);
  ("frag", 13);
  ("ttl", 8);
  ("proto", 8);
  ("chksum", 16);
  ("src", 32);
  ("dst", 32);
]

let ipv4_opt_inst =
  Test_utils.mk_inst "ipv4opt" 
  [
   ("type", 8);
 ]

let header_table = HeaderTable.populate [ ether_inst; ipv4_inst; ipv4_opt_inst ]


module TestConfig = struct
 let verbose = true
 let maxlen = ref(1500)
end

module Test = Test_utils.TestRunner (TestConfig)

let test () =
 let input =
   Parsing.parse_heap_type header_table []
     {| 
     {y:ε | y.pkt_in.length > 280}
     |}
 in

 let hty =
   Parsing.parse_heap_type header_table
     [ ("x", Env.VarBind input) ]
     {|
     (({y'':
    ⊤
    | ((true ∧
       (((((true ∧
           y''.ipv4opt.valid) ∧
          y''.ipv4opt[0:8]@y''.pkt_in == y'.pkt_in) ∧
         (y''.pkt_in.length + 8) == y'.pkt_in.length) ∧
        ((true ∧
         ((¬(y''.ether.valid) ∧
          ¬(y'.ether.valid)) ∨
         ((y''.ether.valid ∧
          y'.ether.valid) ∧
         y''.ether[0:112] == y'.ether[0:112]))) ∧
        ((¬(y''.ipv4.valid) ∧
         ¬(y'.ipv4.valid)) ∨
        ((y''.ipv4.valid ∧
         y'.ipv4.valid) ∧
        y''.ipv4[0:160] == y'.ipv4[0:160])))) ∧
       (y''.pkt_out.length == y'.pkt_out.length ∧
       y''.pkt_out == y'.pkt_out))) ∧
      ¬(y'.ipv4[4:8] == 0b0101))}
  +
  {y'':
    ⊤
    | ((true ∧
       (((y''.pkt_in.length == y'.pkt_in.length ∧
         y''.pkt_in == y'.pkt_in) ∧
        (y''.pkt_out.length == y'.pkt_out.length ∧
        y''.pkt_out == y'.pkt_out)) ∧
       (((true ∧
         ((¬(y''.ether.valid) ∧
          ¬(y'.ether.valid)) ∨
         ((y''.ether.valid ∧
          y'.ether.valid) ∧
         y''.ether[0:112] == y'.ether[0:112]))) ∧
        ((¬(y''.ipv4.valid) ∧
         ¬(y'.ipv4.valid)) ∨
        ((y''.ipv4.valid ∧
         y'.ipv4.valid) ∧
        y''.ipv4[0:160] == y'.ipv4[0:160]))) ∧
       ((¬(y''.ipv4opt.valid) ∧
        ¬(y'.ipv4opt.valid)) ∨
       ((y''.ipv4opt.valid ∧
        y'.ipv4opt.valid) ∧
       y''.ipv4opt[0:8] == y'.ipv4opt[0:8]))))) ∧
      ¬(¬(y'.ipv4[4:8] == 0b0101)))})[y' ↦
                                          {y':
                                            ⊤
                                            | ((true ∧
                                               (((((true ∧
                                                   y'.ipv4.valid) ∧
                                                  y'.ipv4[0:160]@y'.pkt_in == y.pkt_in) ∧
                                                 (y'.pkt_in.length + 160) == y.pkt_in.length) ∧
                                                ((true ∧
                                                 ((¬(y'.ether.valid) ∧
                                                  ¬(y.ether.valid)) ∨
                                                 ((y'.ether.valid ∧
                                                  y.ether.valid) ∧
                                                 y'.ether[0:112] == y.ether[0:112]))) ∧
                                                ((¬(y'.ipv4opt.valid) ∧
                                                 ¬(y.ipv4opt.valid)) ∨
                                                ((y'.ipv4opt.valid ∧
                                                 y.ipv4opt.valid) ∧
                                                y'.ipv4opt[0:8] == y.ipv4opt[0:8])))) ∧
                                               (y'.pkt_out.length == y.pkt_out.length ∧
                                               y'.pkt_out == y.pkt_out))) ∧
                                              y.ether[96:112] == 0b0000100000000000)}]
 +
 {y':
   ⊤
   | ((true ∧
      (((y'.pkt_in.length == y.pkt_in.length ∧
        y'.pkt_in == y.pkt_in) ∧
       (y'.pkt_out.length == y.pkt_out.length ∧
       y'.pkt_out == y.pkt_out)) ∧
      (((true ∧
        ((¬(y'.ether.valid) ∧
         ¬(y.ether.valid)) ∨
        ((y'.ether.valid ∧
         y.ether.valid) ∧
        y'.ether[0:112] == y.ether[0:112]))) ∧
       ((¬(y'.ipv4.valid) ∧
        ¬(y.ipv4.valid)) ∨
       ((y'.ipv4.valid ∧
        y.ipv4.valid) ∧
       y'.ipv4[0:160] == y.ipv4[0:160]))) ∧
      ((¬(y'.ipv4opt.valid) ∧
       ¬(y.ipv4opt.valid)) ∨
      ((y'.ipv4opt.valid ∧
       y.ipv4opt.valid) ∧
      y'.ipv4opt[0:8] == y.ipv4opt[0:8]))))) ∧
     ¬(y.ether[96:112] == 0b0000100000000000))})[y ↦
                                                    {y:
                                                      ⊤
                                                      | (true ∧
                                                        (((((true ∧
                                                            y.ether.valid) ∧
                                                           y.ether[0:112]@y.pkt_in == x.pkt_in) ∧
                                                          (y.pkt_in.length + 112) == x.pkt_in.length) ∧
                                                         ((true ∧
                                                          ((¬(y.ipv4.valid) ∧
                                                           ¬(x.ipv4.valid)) ∨
                                                          ((y.ipv4.valid ∧
                                                           x.ipv4.valid) ∧
                                                          y.ipv4[0:160] == x.ipv4[0:160]))) ∧
                                                         ((¬(y.ipv4opt.valid) ∧
                                                          ¬(x.ipv4opt.valid)) ∨
                                                         ((y.ipv4opt.valid ∧
                                                          x.ipv4opt.valid) ∧
                                                         y.ipv4opt[0:8] == x.ipv4opt[0:8])))) ∧
                                                        (y.pkt_out.length == x.pkt_out.length ∧
                                                        y.pkt_out == x.pkt_out)))}]
     |}
 in

 let hty_smpl =
  Parsing.parse_heap_type header_table
    [ ("x", Env.VarBind input) ]
    {|
    {y':
  ⊤
  | ((true ∧
     ((true ∧
      (((((true ∧
          y'.ipv4opt.valid) ∧
         (y'.ipv4opt[0:8] == x.pkt_in[272:280] ∧
         x.pkt_in[0:280]@y'.pkt_in == x.pkt_in)) ∧
        (((y'.pkt_in.length + 8) + 160) + 112) == x.pkt_in.length) ∧
       ((true ∧
        (y'.ether.valid ∧
        ((y'.ether[0:48] == x.pkt_in[0:48] ∧
         true) ∧
        ((y'.ether[48:96] == x.pkt_in[48:96] ∧
         true) ∧
        y'.ether[96:112] == x.pkt_in[96:112])))) ∧
       (y'.ipv4.valid ∧
       (y'.ipv4[0:4] == x.pkt_in[112:116] ∧
       (y'.ipv4[4:8] == x.pkt_in[116:120] ∧
       (y'.ipv4[8:16] == x.pkt_in[120:128] ∧
       (y'.ipv4[16:32] == x.pkt_in[128:144] ∧
       (y'.ipv4[32:48] == x.pkt_in[144:160] ∧
       (y'.ipv4[48:51] == x.pkt_in[160:163] ∧
       (y'.ipv4[51:64] == x.pkt_in[163:176] ∧
       (y'.ipv4[64:72] == x.pkt_in[176:184] ∧
       (y'.ipv4[72:80] == x.pkt_in[184:192] ∧
       (y'.ipv4[80:96] == x.pkt_in[192:208] ∧
       (y'.ipv4[96:128] == x.pkt_in[208:240] ∧
       y'.ipv4[128:160] == x.pkt_in[240:272])))))))))))))) ∧
      (y'.pkt_out.length == x.pkt_out.length ∧
      y'.pkt_out == x.pkt_out))) ∧
     ¬(x.pkt_in[116:120] == 0b0101))) ∧
    x.pkt_in[96:112] == 0b0000100000000000)}
+
{y':
  ⊤
  | ((true ∧
     ((true ∧
      (((((y'.pkt_in.length + 160) + 112) == x.pkt_in.length ∧
        x.pkt_in[0:272]@y'.pkt_in == x.pkt_in) ∧
       (y'.pkt_out.length == x.pkt_out.length ∧
       y'.pkt_out == x.pkt_out)) ∧
      (((true ∧
        (y'.ether.valid ∧
        ((y'.ether[0:48] == x.pkt_in[0:48] ∧
         true) ∧
        ((y'.ether[48:96] == x.pkt_in[48:96] ∧
         true) ∧
        y'.ether[96:112] == x.pkt_in[96:112])))) ∧
       (y'.ipv4.valid ∧
       (y'.ipv4[0:4] == x.pkt_in[112:116] ∧
       (y'.ipv4[4:8] == x.pkt_in[116:120] ∧
       (y'.ipv4[8:16] == x.pkt_in[120:128] ∧
       (y'.ipv4[16:32] == x.pkt_in[128:144] ∧
       (y'.ipv4[32:48] == x.pkt_in[144:160] ∧
       (y'.ipv4[48:51] == x.pkt_in[160:163] ∧
       (y'.ipv4[51:64] == x.pkt_in[163:176] ∧
       (y'.ipv4[64:72] == x.pkt_in[176:184] ∧
       (y'.ipv4[72:80] == x.pkt_in[184:192] ∧
       (y'.ipv4[80:96] == x.pkt_in[192:208] ∧
       (y'.ipv4[96:128] == x.pkt_in[208:240] ∧
       y'.ipv4[128:160] == x.pkt_in[240:272]))))))))))))) ∧
      ((¬(y'.ipv4opt.valid) ∧
       ¬(x.ipv4opt.valid)) ∨
      ((y'.ipv4opt.valid ∧
       x.ipv4opt.valid) ∧
      true))))) ∧
     (x.pkt_in[116:120] == 0b0101 ∧
     true))) ∧
    x.pkt_in[96:112] == 0b0000100000000000)}
+
{y:
  ⊤
  | (true ∧
    ((true ∧
     ((((y.pkt_in.length + 112) == x.pkt_in.length ∧
       x.pkt_in[0:112]@y.pkt_in == x.pkt_in) ∧
      (y.pkt_out.length == x.pkt_out.length ∧
      y.pkt_out == x.pkt_out)) ∧
     (((true ∧
       (y.ether.valid ∧
       (y.ether[0:48] == x.pkt_in[0:48] ∧
       (y.ether[48:96] == x.pkt_in[48:96] ∧
       y.ether[96:112] == x.pkt_in[96:112])))) ∧
      ((¬(y.ipv4.valid) ∧
       ¬(x.ipv4.valid)) ∨
      ((y.ipv4.valid ∧
       x.ipv4.valid) ∧
      (y.ipv4[0:4] == x.ipv4[0:4] ∧
      (y.ipv4[4:8] == x.ipv4[4:8] ∧
      (y.ipv4[8:16] == x.ipv4[8:16] ∧
      (y.ipv4[16:32] == x.ipv4[16:32] ∧
      (y.ipv4[32:48] == x.ipv4[32:48] ∧
      (y.ipv4[48:51] == x.ipv4[48:51] ∧
      (y.ipv4[51:64] == x.ipv4[51:64] ∧
      (y.ipv4[64:72] == x.ipv4[64:72] ∧
      (y.ipv4[72:80] == x.ipv4[72:80] ∧
      (y.ipv4[80:96] == x.ipv4[80:96] ∧
      (y.ipv4[96:128] == x.ipv4[96:128] ∧
      y.ipv4[128:160] == x.ipv4[128:160])))))))))))))) ∧
     ((¬(y.ipv4opt.valid) ∧
      ¬(x.ipv4opt.valid)) ∨
     ((y.ipv4opt.valid ∧
      x.ipv4opt.valid) ∧
     true))))) ∧
    ¬(x.pkt_in[96:112] == 0b0000100000000000)))}
    |}
in
Test.is_equiv hty_smpl hty [ ("x", Env.VarBind input) ] header_table

let test1 () =
  let input =
    Parsing.parse_heap_type header_table []
      {| 
      {y:ε | y.pkt_in.length > 280}
      |}
  in

  let hty_1 = 
    Parsing.parse_heap_type header_table
    [ ("x", Env.VarBind input) ]
    {|
    (({y'':
    ⊤
    | ((true ∧
       (((((true ∧
           y''.ipv4opt.valid) ∧
          y''.ipv4opt[0:8]@y''.pkt_in == y'.pkt_in) ∧
         (y''.pkt_in.length + 8) == y'.pkt_in.length) ∧
        ((true ∧
         ((¬(y''.ether.valid) ∧
          ¬(y'.ether.valid)) ∨
         ((y''.ether.valid ∧
          y'.ether.valid) ∧
         y''.ether[0:112] == y'.ether[0:112]))) ∧
        ((¬(y''.ipv4.valid) ∧
         ¬(y'.ipv4.valid)) ∨
        ((y''.ipv4.valid ∧
         y'.ipv4.valid) ∧
        y''.ipv4[0:160] == y'.ipv4[0:160])))) ∧
       (y''.pkt_out.length == y'.pkt_out.length ∧
       y''.pkt_out == y'.pkt_out))) ∧
      ¬(y'.ipv4[4:8] == 0b0101))})[y' ↦
      {y':
        ⊤
        | ((true ∧
           (((((true ∧
               y'.ipv4.valid) ∧
              y'.ipv4[0:160]@y'.pkt_in == y.pkt_in) ∧
             (y'.pkt_in.length + 160) == y.pkt_in.length) ∧
            ((true ∧
             ((¬(y'.ether.valid) ∧
              ¬(y.ether.valid)) ∨
             ((y'.ether.valid ∧
              y.ether.valid) ∧
             y'.ether[0:112] == y.ether[0:112]))) ∧
            ((¬(y'.ipv4opt.valid) ∧
             ¬(y.ipv4opt.valid)) ∨
            ((y'.ipv4opt.valid ∧
             y.ipv4opt.valid) ∧
            y'.ipv4opt[0:8] == y.ipv4opt[0:8])))) ∧
           (y'.pkt_out.length == y.pkt_out.length ∧
           y'.pkt_out == y.pkt_out))) ∧
          y.ether[96:112] == 0b0000100000000000)}])[y ↦
          {y:
            ⊤
            | (true ∧
              (((((true ∧
                  y.ether.valid) ∧
                 y.ether[0:112]@y.pkt_in == x.pkt_in) ∧
                (y.pkt_in.length + 112) == x.pkt_in.length) ∧
               ((true ∧
                ((¬(y.ipv4.valid) ∧
                 ¬(x.ipv4.valid)) ∨
                ((y.ipv4.valid ∧
                 x.ipv4.valid) ∧
                y.ipv4[0:160] == x.ipv4[0:160]))) ∧
               ((¬(y.ipv4opt.valid) ∧
                ¬(x.ipv4opt.valid)) ∨
               ((y.ipv4opt.valid ∧
                x.ipv4opt.valid) ∧
               y.ipv4opt[0:8] == x.ipv4opt[0:8])))) ∧
              (y.pkt_out.length == x.pkt_out.length ∧
              y.pkt_out == x.pkt_out)))}]
    |}
   in

   let hty_1_smpl = 
    Parsing.parse_heap_type header_table
    [ ("x", Env.VarBind input) ]
    {|
    {y':
  ⊤
  | ((true ∧
     ((true ∧
      (((((true ∧
          y'.ipv4opt.valid) ∧
         (y'.ipv4opt[0:8] == x.pkt_in[272:280] ∧
         x.pkt_in[0:280]@y'.pkt_in == x.pkt_in)) ∧
        (((y'.pkt_in.length + 8) + 160) + 112) == x.pkt_in.length) ∧
       ((true ∧
        (y'.ether.valid ∧
        ((y'.ether[0:48] == x.pkt_in[0:48] ∧
         true) ∧
        ((y'.ether[48:96] == x.pkt_in[48:96] ∧
         true) ∧
        y'.ether[96:112] == x.pkt_in[96:112])))) ∧
       (y'.ipv4.valid ∧
       (y'.ipv4[0:4] == x.pkt_in[112:116] ∧
       (y'.ipv4[4:8] == x.pkt_in[116:120] ∧
       (y'.ipv4[8:16] == x.pkt_in[120:128] ∧
       (y'.ipv4[16:32] == x.pkt_in[128:144] ∧
       (y'.ipv4[32:48] == x.pkt_in[144:160] ∧
       (y'.ipv4[48:51] == x.pkt_in[160:163] ∧
       (y'.ipv4[51:64] == x.pkt_in[163:176] ∧
       (y'.ipv4[64:72] == x.pkt_in[176:184] ∧
       (y'.ipv4[72:80] == x.pkt_in[184:192] ∧
       (y'.ipv4[80:96] == x.pkt_in[192:208] ∧
       (y'.ipv4[96:128] == x.pkt_in[208:240] ∧
       y'.ipv4[128:160] == x.pkt_in[240:272])))))))))))))) ∧
      (y'.pkt_out.length == x.pkt_out.length ∧
      y'.pkt_out == x.pkt_out))) ∧
     ¬(x.pkt_in[116:120] == 0b0101))) ∧
    x.pkt_in[96:112] == 0b0000100000000000)}
    |}
   in
Test.is_equiv hty_1 hty_1_smpl [ ("x", Env.VarBind input) ] header_table


let test2 () =
  let input =
    Parsing.parse_heap_type header_table []
      {| 
      {y:ε | y.pkt_in.length > 280}
      |}
  in
  
  let hty_2 = 
    Parsing.parse_heap_type header_table
    [ ("x", Env.VarBind input) ]
    {|
    ({y'':
    ⊤
    | ((true ∧
       (((y''.pkt_in.length == y'.pkt_in.length ∧
         y''.pkt_in == y'.pkt_in) ∧
        (y''.pkt_out.length == y'.pkt_out.length ∧
        y''.pkt_out == y'.pkt_out)) ∧
       (((true ∧
         ((¬(y''.ether.valid) ∧
          ¬(y'.ether.valid)) ∨
         ((y''.ether.valid ∧
          y'.ether.valid) ∧
         y''.ether[0:112] == y'.ether[0:112]))) ∧
        ((¬(y''.ipv4.valid) ∧
         ¬(y'.ipv4.valid)) ∨
        ((y''.ipv4.valid ∧
         y'.ipv4.valid) ∧
        y''.ipv4[0:160] == y'.ipv4[0:160]))) ∧
       ((¬(y''.ipv4opt.valid) ∧
        ¬(y'.ipv4opt.valid)) ∨
       ((y''.ipv4opt.valid ∧
        y'.ipv4opt.valid) ∧
       y''.ipv4opt[0:8] == y'.ipv4opt[0:8]))))) ∧
      ¬(¬(y'.ipv4[4:8] == 0b0101)))}[y' ↦
      {y':
        ⊤
        | ((true ∧
           (((((true ∧
               y'.ipv4.valid) ∧
              y'.ipv4[0:160]@y'.pkt_in == y.pkt_in) ∧
             (y'.pkt_in.length + 160) == y.pkt_in.length) ∧
            ((true ∧
             ((¬(y'.ether.valid) ∧
              ¬(y.ether.valid)) ∨
             ((y'.ether.valid ∧
              y.ether.valid) ∧
             y'.ether[0:112] == y.ether[0:112]))) ∧
            ((¬(y'.ipv4opt.valid) ∧
             ¬(y.ipv4opt.valid)) ∨
            ((y'.ipv4opt.valid ∧
             y.ipv4opt.valid) ∧
            y'.ipv4opt[0:8] == y.ipv4opt[0:8])))) ∧
           (y'.pkt_out.length == y.pkt_out.length ∧
           y'.pkt_out == y.pkt_out))) ∧
          y.ether[96:112] == 0b0000100000000000)}])[y ↦
          {y:
            ⊤
            | (true ∧
              (((((true ∧
                  y.ether.valid) ∧
                 y.ether[0:112]@y.pkt_in == x.pkt_in) ∧
                (y.pkt_in.length + 112) == x.pkt_in.length) ∧
               ((true ∧
                ((¬(y.ipv4.valid) ∧
                 ¬(x.ipv4.valid)) ∨
                ((y.ipv4.valid ∧
                 x.ipv4.valid) ∧
                y.ipv4[0:160] == x.ipv4[0:160]))) ∧
               ((¬(y.ipv4opt.valid) ∧
                ¬(x.ipv4opt.valid)) ∨
               ((y.ipv4opt.valid ∧
                x.ipv4opt.valid) ∧
               y.ipv4opt[0:8] == x.ipv4opt[0:8])))) ∧
              (y.pkt_out.length == x.pkt_out.length ∧
              y.pkt_out == x.pkt_out)))}]
    |}
   in

   let hty_2_smpl = 
    Parsing.parse_heap_type header_table
    [ ("x", Env.VarBind input) ]
    {|
    {y':
  ⊤
  | ((true ∧
     ((true ∧
      (((((y'.pkt_in.length + 160) + 112) == x.pkt_in.length ∧
        x.pkt_in[0:272]@y'.pkt_in == x.pkt_in) ∧
       (y'.pkt_out.length == x.pkt_out.length ∧
       y'.pkt_out == x.pkt_out)) ∧
      (((true ∧
        (y'.ether.valid ∧
        ((y'.ether[0:48] == x.pkt_in[0:48] ∧
         true) ∧
        ((y'.ether[48:96] == x.pkt_in[48:96] ∧
         true) ∧
        y'.ether[96:112] == x.pkt_in[96:112])))) ∧
       (y'.ipv4.valid ∧
       (y'.ipv4[0:4] == x.pkt_in[112:116] ∧
       (y'.ipv4[4:8] == x.pkt_in[116:120] ∧
       (y'.ipv4[8:16] == x.pkt_in[120:128] ∧
       (y'.ipv4[16:32] == x.pkt_in[128:144] ∧
       (y'.ipv4[32:48] == x.pkt_in[144:160] ∧
       (y'.ipv4[48:51] == x.pkt_in[160:163] ∧
       (y'.ipv4[51:64] == x.pkt_in[163:176] ∧
       (y'.ipv4[64:72] == x.pkt_in[176:184] ∧
       (y'.ipv4[72:80] == x.pkt_in[184:192] ∧
       (y'.ipv4[80:96] == x.pkt_in[192:208] ∧
       (y'.ipv4[96:128] == x.pkt_in[208:240] ∧
       y'.ipv4[128:160] == x.pkt_in[240:272]))))))))))))) ∧
      ((¬(y'.ipv4opt.valid) ∧
       ¬(x.ipv4opt.valid)) ∨
      ((y'.ipv4opt.valid ∧
       x.ipv4opt.valid) ∧
      true))))) ∧
     (x.pkt_in[116:120] == 0b0101 ∧
     true))) ∧
    x.pkt_in[96:112] == 0b0000100000000000)}
    |}
   in
Test.is_equiv hty_2 hty_2_smpl [ ("x", Env.VarBind input) ] header_table



let test3 () =
  let input =
    Parsing.parse_heap_type header_table []
      {| 
      {y:ε | y.pkt_in.length > 280}
      |}
  in
  
  let hty_3 = 
    Parsing.parse_heap_type header_table
    [ ("x", Env.VarBind input) ]
    {|
    {y':
   ⊤
   | ((true ∧
      (((y'.pkt_in.length == y.pkt_in.length ∧
        y'.pkt_in == y.pkt_in) ∧
       (y'.pkt_out.length == y.pkt_out.length ∧
       y'.pkt_out == y.pkt_out)) ∧
      (((true ∧
        ((¬(y'.ether.valid) ∧
         ¬(y.ether.valid)) ∨
        ((y'.ether.valid ∧
         y.ether.valid) ∧
        y'.ether[0:112] == y.ether[0:112]))) ∧
       ((¬(y'.ipv4.valid) ∧
        ¬(y.ipv4.valid)) ∨
       ((y'.ipv4.valid ∧
        y.ipv4.valid) ∧
       y'.ipv4[0:160] == y.ipv4[0:160]))) ∧
      ((¬(y'.ipv4opt.valid) ∧
       ¬(y.ipv4opt.valid)) ∨
      ((y'.ipv4opt.valid ∧
       y.ipv4opt.valid) ∧
      y'.ipv4opt[0:8] == y.ipv4opt[0:8]))))) ∧
     ¬(y.ether[96:112] == 0b0000100000000000))}[y ↦
                                                    {y:
                                                      ⊤
                                                      | (true ∧
                                                        (((((true ∧
                                                            y.ether.valid) ∧
                                                           y.ether[0:112]@y.pkt_in == x.pkt_in) ∧
                                                          (y.pkt_in.length + 112) == x.pkt_in.length) ∧
                                                         ((true ∧
                                                          ((¬(y.ipv4.valid) ∧
                                                           ¬(x.ipv4.valid)) ∨
                                                          ((y.ipv4.valid ∧
                                                           x.ipv4.valid) ∧
                                                          y.ipv4[0:160] == x.ipv4[0:160]))) ∧
                                                         ((¬(y.ipv4opt.valid) ∧
                                                          ¬(x.ipv4opt.valid)) ∨
                                                         ((y.ipv4opt.valid ∧
                                                          x.ipv4opt.valid) ∧
                                                         y.ipv4opt[0:8] == x.ipv4opt[0:8])))) ∧
                                                        (y.pkt_out.length == x.pkt_out.length ∧
                                                        y.pkt_out == x.pkt_out)))}]
    |}
   in

   let hty_3_smpl = 
    Parsing.parse_heap_type header_table
    [ ("x", Env.VarBind input) ]
    {|
    {y:
  ⊤
  | (true ∧
    ((true ∧
     ((((y.pkt_in.length + 112) == x.pkt_in.length ∧
       x.pkt_in[0:112]@y.pkt_in == x.pkt_in) ∧
      (y.pkt_out.length == x.pkt_out.length ∧
      y.pkt_out == x.pkt_out)) ∧
     (((true ∧
       (y.ether.valid ∧
       (y.ether[0:48] == x.pkt_in[0:48] ∧
       (y.ether[48:96] == x.pkt_in[48:96] ∧
       y.ether[96:112] == x.pkt_in[96:112])))) ∧
      ((¬(y.ipv4.valid) ∧
       ¬(x.ipv4.valid)) ∨
      ((y.ipv4.valid ∧
       x.ipv4.valid) ∧
      (y.ipv4[0:4] == x.ipv4[0:4] ∧
      (y.ipv4[4:8] == x.ipv4[4:8] ∧
      (y.ipv4[8:16] == x.ipv4[8:16] ∧
      (y.ipv4[16:32] == x.ipv4[16:32] ∧
      (y.ipv4[32:48] == x.ipv4[32:48] ∧
      (y.ipv4[48:51] == x.ipv4[48:51] ∧
      (y.ipv4[51:64] == x.ipv4[51:64] ∧
      (y.ipv4[64:72] == x.ipv4[64:72] ∧
      (y.ipv4[72:80] == x.ipv4[72:80] ∧
      (y.ipv4[80:96] == x.ipv4[80:96] ∧
      (y.ipv4[96:128] == x.ipv4[96:128] ∧
      y.ipv4[128:160] == x.ipv4[128:160])))))))))))))) ∧
     ((¬(y.ipv4opt.valid) ∧
      ¬(x.ipv4opt.valid)) ∨
     ((y.ipv4opt.valid ∧
      x.ipv4opt.valid) ∧
     true))))) ∧
    ¬(x.pkt_in[96:112] == 0b0000100000000000)))}
    |}
   in
Test.is_equiv hty_3 hty_3_smpl [ ("x", Env.VarBind input) ] header_table


let test_set = 
  [ 
    test_case "Test 1" `Quick test1;
    test_case "Test 2" `Quick test2;
    test_case "Test 3" `Quick test3;
    test_case "Test Full" `Quick test;
  ]
    (* test_case "Test 2" `Quick test2 ] *)