(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next sevent bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in 
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instruction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) -> 
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | o -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* It might be useful to toggle printing of intermediate states of your 
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]

*)
let debug_simulator = ref false


let string_of_regv (regs:regs) (reg:reg) : string =
  match reg with
    | Rip -> Printf.sprintf "Rip: 0x%LX" regs.(rind reg)
    | Rax -> Printf.sprintf "Rax: 0x%LX" regs.(rind reg)
    | Rbx -> Printf.sprintf "Rbx: 0x%LX" regs.(rind reg)
    | Rcx -> Printf.sprintf "Rcx: 0x%LX" regs.(rind reg)
    | Rdx -> Printf.sprintf "Rdx: 0x%LX" regs.(rind reg)
    | Rsi -> Printf.sprintf "Rsi: 0x%LX" regs.(rind reg)
    | Rdi -> Printf.sprintf "Rdi: 0x%LX" regs.(rind reg)
    | Rbp -> Printf.sprintf "Rbp: 0x%LX" regs.(rind reg)
    | Rsp -> Printf.sprintf "Rsp: 0x%LX" regs.(rind reg)
    | R08 -> Printf.sprintf "R08: 0x%LX" regs.(rind reg)
    | R09 -> Printf.sprintf "R09: 0x%LX" regs.(rind reg)
    | R10 -> Printf.sprintf "R10: 0x%LX" regs.(rind reg)
    | R11 -> Printf.sprintf "R11: 0x%LX" regs.(rind reg)
    | R12 -> Printf.sprintf "R12: 0x%LX" regs.(rind reg)
    | R13 -> Printf.sprintf "R13: 0x%LX" regs.(rind reg)
    | R14 -> Printf.sprintf "R14: 0x%LX" regs.(rind reg)
    | R15 -> Printf.sprintf "R15: 0x%LX" regs.(rind reg)

let string_of_regs (regs:regs) (delim:string) : string = 
  (string_of_regv regs Rip) ^ delim ^ (string_of_regv regs Rsp) ^ delim ^ (string_of_regv regs Rax) ^ delim ^ (string_of_regv regs Rbx) ^ delim ^ (string_of_regv regs Rcx) ^ delim ^ (string_of_regv regs Rdx) ^ delim ^ (string_of_regv regs Rsi) ^ delim ^ (string_of_regv regs Rdi) ^ delim ^ (string_of_regv regs Rbp)

let string_of_regs_one (regs:regs) : string =
  string_of_regs regs " "


(* Interpret a condition code with respect to the given flags. *)
let interp_cnd {fo; fs; fz} : cnd -> bool = fun op ->
  let evalEq = fz in
  let evalNeq = not fz in
  let evalLt = (fs != fo) in
  let evalLe = evalLt || evalEq in
  let evalGt = not evalLe in
  let evalGe = not evalLt in

  match op with
    | Eq -> evalEq
    | Neq -> evalNeq
    | Gt -> evalGt
    | Ge -> evalGe
    | Lt -> evalLt
    | Le -> evalLe


(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option =
  if addr < mem_bot then
    None
  else if addr >= mem_top then
    None
  else
    Some (Int64.to_int (Int64.sub addr mem_bot))


let read_operand (m:mach) (op:operand) : int64 =
  let read_mem (addr:int64) : int64 = 
    match map_addr addr with
      | Some vaddr -> int64_of_sbytes (Array.to_list (Array.sub m.mem vaddr 8))
      | None -> raise X86lite_segfault
  in
  match op with
    | Imm (Lit lit) -> lit
    | Reg r -> m.regs.(rind r)
    | Ind1 (Lit addr) -> read_mem addr
    | Ind2 reg -> read_mem m.regs.(rind reg)
    | Ind3 (Lit base, offset) -> read_mem (Int64.add base m.regs.(rind offset))
    | _ -> failwith "Inavlid source operand"


let write_operand (m:mach) (op:operand) (v:int64) : unit =
  let write_mem (addr:int64) : unit = 
    let rec write_arr (me:mem) (offset:int) (v:sbyte list) : unit =
      match v with
        | v0::vl -> me.(offset) <- v0; write_arr me (offset + 1) vl
        | _ -> ()
    in
    match map_addr addr with
      | Some vaddr -> write_arr m.mem vaddr (sbytes_of_int64 v)
      | _ -> raise X86lite_segfault
  in
  match op with
    | Reg r -> m.regs.(rind r) <- v
    | Ind1 (Lit addr) -> write_mem addr
    | Ind2 reg -> write_mem m.regs.(rind reg)
    | Ind3 (Lit base, offset) -> write_mem (Int64.add base m.regs.(rind offset))
    | _ -> failwith "Invalid destination operand"


let exec_instr (m:mach) (i:ins) : bool = 
  let read_op (op:operand) : int64 = read_operand m op in
  let write_op (op:operand) (v:int64) : unit = write_operand m op v in

  let open Int64_overflow in

    let update_fs_fz (v:int64) : unit =
      if v < 0L then begin
        m.flags.fs <- true;
        m.flags.fz <- false
      end
      else if v > 0L then begin
        m.flags.fs <- false;
        m.flags.fz <- false
      end
      else begin
        m.flags.fs <- false;
        m.flags.fz <- true
      end
    in

    let apply_flags1 (op:int64 -> Int64_overflow.t) : (int64 -> int64) =
      fun v ->
        let {value=value; overflow=overflow} = op v in
        m.flags.fo <- overflow;
        update_fs_fz value;
        value
    in

    let apply_flags2 (op:int64 -> int64 -> Int64_overflow.t) : (int64 -> int64 -> int64) =
      fun v1 v2 ->
        let {value=value; overflow=overflow} = op v1 v2 in
        m.flags.fo <- overflow;
        update_fs_fz value;
        value
    in

    let apply_flags3 (op:int64 -> int64) : (int64 -> int64) =
      fun v1 ->
        let res = op v1 in
        m.flags.fo <- false;
        update_fs_fz res;
        res
    in

    let apply_flags4 (op:int64 -> int64 -> int64) : (int64 -> int64 -> int64) =
      fun v1 v2 ->
        let res = op v1 v2 in
        m.flags.fo <- false;
        update_fs_fz res;
        res
    in

    let shift_right_ar (value:int64) (amount:int64) : int64 =
      if amount != 0L then
        let res = Int64.shift_right value (Int64.to_int amount) in
        update_fs_fz res;
        if amount == 1L then begin
          m.flags.fo <- true;
        end;
        res
      else
        value
    in

    let shift_left (value:int64) (amount:int64) : int64 =
      if amount != 0L then
        let res = Int64.shift_left value (Int64.to_int amount) in
        update_fs_fz res;
        if amount == 1L then begin
          let low_mask = Int64.logand (Int64.lognot (Int64.shift_left 1L 63)) in
          if (Int64.logxor (low_mask value) (low_mask res)) != 0L then
            m.flags.fo <- true
          else
            m.flags.fo <- false
        end;
        res
      else
        value
    in

    let shift_right (value:int64) (amount:int64) : int64 =
      if amount != 0L then
        let res = Int64.shift_right_logical value (Int64.to_int amount) in
        update_fs_fz res;
        if res == 0L then begin
          m.flags.fz <- true
        end;
        m.flags.fs <- (Int64.logand (Int64.lognot (Int64.shift_left 1L 63)) res) == 0L;
        if amount == 1L then begin
          m.flags.fo <- (Int64.logand (Int64.lognot (Int64.shift_left 1L 63)) value) == 0L;
        end;
        res
      else
        value
    in
        
    let set_byte (value:int64) (cnd:bool) : int64 =
      let masked = Int64.logand (Int64.lognot 255L) value in
      if cnd then
        Int64.logor masked 1L
      else
        masked
    in

    let load_effective_address (op:operand) : int64 =
      match op with
        | Ind1 (Lit addr) -> addr
        | Ind2 reg -> m.regs.(rind reg)
        | Ind3 (Lit base, offset) -> Int64.add base m.regs.(rind offset)
        | _ -> failwith "Invalid operand"
    in

    let push (value:int64) : unit =
      m.regs.(rind Rsp) <- Int64.sub m.regs.(rind Rsp) 8L;
      write_op (Ind2 Rsp) value;
    in

    let pop unit : int64 =
      let res = read_op (Ind2 Rsp) in
      write_op (Reg Rsp) (Int64.add (read_op (Reg Rsp)) 8L);
      res
    in

    let return unit : bool =
      let value : int64 = pop () in
      m.regs.(rind Rip) <- value;
      if value <> exit_addr then
        true
      else 
        false
    in

    match i with
      | (Negq, [dst]) -> write_op dst (apply_flags1 (Int64_overflow.neg) (read_op dst)); true
      | (Addq, [src; dst]) -> write_op dst (apply_flags2 (Int64_overflow.add) (read_op dst) (read_op src)); true
      | (Subq, [src; dst]) -> write_op dst (apply_flags2 (Int64_overflow.sub) (read_op dst) (read_op src)); true
      | (Imulq, [src; dst]) -> write_op dst (apply_flags2 (Int64_overflow.mul) (read_op dst) (read_op src)); true
      | (Incq, [src]) -> write_op src (apply_flags1 (Int64_overflow.succ) (read_op src)); true
      | (Decq, [src]) -> write_op src (apply_flags1 (Int64_overflow.pred) (read_op src)); true
      | (Notq, [src]) -> write_op src (Int64.lognot (read_op src)); true
      | (Andq, [src; dst]) -> write_op dst (apply_flags4 (Int64.logand) (read_op dst) (read_op src)); true
      | (Orq, [src; dst]) -> write_op dst (apply_flags4 (Int64.logor) (read_op dst) (read_op src)); true
      | (Xorq, [src; dst]) -> write_op dst (apply_flags4 (Int64.logxor) (read_op dst) (read_op src)); true
      | (Sarq, [amt; dst]) -> write_op dst (shift_right_ar (read_op dst) (read_op amt)); true
      | (Shlq, [amt; dst]) -> write_op dst (shift_left (read_op dst) (read_op amt)); true
      | (Shrq, [amt; dst]) -> write_op dst (shift_right (read_op dst) (read_op amt)); true
      | (Set cnd, [dst]) -> write_op dst (set_byte (read_op dst) (interp_cnd m.flags cnd)); true
      | (Leaq, [ind; dst]) -> write_op dst (load_effective_address ind); true
      | (Movq, [src; dst]) -> write_op dst (read_op src); true
      | (Pushq, [src]) -> push (read_op src); true
      | (Popq, [dst]) -> write_op dst (pop ()); true
      | (Cmpq, [src1; src2]) -> (apply_flags2 (Int64_overflow.sub) (read_op src2) (read_op src1)); true
      | (Jmp, [src]) -> m.regs.(rind Rip) <- read_op src; false
      | (Callq, [src]) -> push m.regs.(rind Rip); m.regs.(rind Rip) <- read_op src; false
      | (Retq, []) -> return ()
      | (J cnd, [src]) -> if interp_cnd m.flags cnd then begin m.regs.(rind Rip) <- read_op src; false end else true
      | _ -> failwith "Invalid operand"


(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)
let step (m:mach) : unit =
  let instruction =
    match map_addr m.regs.(rind Rip) with
      | None -> raise X86lite_segfault
      | Some iaddr -> 
      match m.mem.(iaddr) with
        | InsB0 instr -> instr
        | _ -> failwith "%Rip does not point to a valid instruction"
  in
  if exec_instr m instruction then
    m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L


(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the 
   machine halts. *)
let run (m:mach) : int64 = 
  while m.regs.(rind Rip) <> exit_addr do step m done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* starting address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl


module LabelValues = Map.Make(struct type t = lbl let compare = compare end)


let patch_immediate (mapping:int64 LabelValues.t) (imm:imm) =
  match imm with
    | Lbl lbl -> begin match LabelValues.find_opt lbl mapping with
      | Some value -> Lit value
      | None -> raise (Undefined_sym lbl)
    end
    | other -> other

let patch_instruction mapping ((code, ops):ins) =
  let patch_operands (op:operand) : operand =
    match op with
      | Imm imm -> Imm (patch_immediate mapping imm)
      | Ind1 imm -> Ind1 (patch_immediate mapping imm)
      | Ind3 (imm, reg) -> Ind3 (patch_immediate mapping imm, reg)
      | other -> other
  in
  (code, List.map (patch_operands) ops)

let patch_data mapping (data:data) =
  match data with
    | Quad imm -> Quad (patch_immediate mapping imm)
    | other -> other

let patch_text_labels mapping (text:ins list) : ins list =
  List.map (patch_instruction mapping) text

let patch_data_labels mapping (data:data list) : data list =
  List.map (patch_data mapping) data

let patch_asm_labels mapping (asm:asm) : asm =
  match asm with
    | Text instr -> Text (patch_text_labels mapping instr)
    | Data data -> Data (patch_data_labels mapping data)


let text_byte_length (text:ins list) : int64 =
  Int64.mul (Int64.of_int (List.length text)) 8L

let data_byte_length (data:data list) : int64 =
  let fold_length (current:int64) (d:data) : int64 =
    let len = match d with
      | Asciz str -> Int64.of_int ((List.length (sbytes_of_string str)) + 1)
      | Quad imm -> 8L
    in
    Int64.add current len
  in
  List.fold_left fold_length 0L data

let elem_byte_length {lbl; global; asm} : int64 = 
  match asm with
    | Text instr -> text_byte_length instr
    | Data data -> data_byte_length data

let is_text_elem {lbl; global; asm} : bool =
  match asm with
    | Text _ -> true
    | Data _ -> false

let is_data_elem {lbl; global; asm} : bool =
  match asm with
    | Text _ -> false
    | Data _ -> true


let assemble_text (text: ins list) : sbyte list =
  let foldfunc (current:sbyte list) (instr:ins) : sbyte list =
    current @ (sbytes_of_ins instr)
  in
  List.fold_left (foldfunc) [] text

let assemble_data (data: data list) : sbyte list =
  let foldfunc (current:sbyte list) (d:data) : sbyte list = 
    match d with
      | Asciz str -> current @ (sbytes_of_string str)
      | Quad (Lit value) -> current @ (sbytes_of_int64 value)
      | _ -> failwith "Who forgot to remove the lit?"
  in
  List.fold_left (foldfunc) [] data


(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)
            due to the null terminator

   - resolve the labels to concrete addresses and 'patch' the instructions to 
     replace Lbl values with the corresponding Imm values.

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

  HINT: List.fold_left and List.fold_right are your friends.
 *)
let assemble (p:prog) : exec =
  let text = List.filter (is_text_elem) p in
  let data = List.filter (is_data_elem) p in

  let add_offsets = 
    List.fold_left (fun (map, offset) el -> begin
      let size = elem_byte_length el in 
      (LabelValues.add el.lbl offset map, Int64.add offset size)
    end)
  in
  let (text_mapping, data_offset) = add_offsets (LabelValues.empty, mem_bot) text in
  let (mapping, _) = add_offsets (text_mapping, data_offset) data in

  let patch_elem_labels (elems:elem list) =
    let patch_map {lbl; global; asm} = {lbl=lbl; global=global; asm=patch_asm_labels mapping asm} in
    List.map (patch_map) elems
  in 
  let patched_text = patch_elem_labels text in
  let patched_data = patch_elem_labels data in

  let assembled_text = List.fold_left (fun (current:sbyte list) {lbl; global; asm} -> begin
    match asm with
      | Text instr -> current @ (assemble_text instr)
      | _ -> failwith "Data in text segment..."
  end) [] patched_text
  in
  let assmebled_data = List.fold_left (fun (current:sbyte list) {lbl; global; asm} -> begin
    match asm with
      | Data data -> current @ (assemble_data data)
      | _ -> failwith "Text in data segment..."
  end) [] patched_data
  in

  match LabelValues.find_opt ("main") mapping with
    | Some entry -> {entry=entry; text_pos=mem_bot; data_pos=data_offset; text_seg=assembled_text; data_seg=assmebled_data}
    | None -> raise (Undefined_sym "main")

(* Convert an object file into an executable machine state. 
    - allocate the mem array
    - set up the memory state by writing the symbolic bytes to the 
      appropriate locations 
    - create the inital register state
      - initialize rip to the entry point address
      - initializes rsp to the last word in memory 
      - the other registers are initialized to 0
    - the condition code flags start as 'false'

  Hint: The Array.make, Array.blit, and Array.of_list library functions 
  may be of use.
*)
let load {entry; text_pos; data_pos; text_seg; data_seg} : mach = 
  let mapped_text = match map_addr text_pos with
    | Some addr -> addr
    | None -> failwith "text_pos out of range"
  in
  let mapped_data = match map_addr data_pos with
    | Some addr -> addr
    | None -> failwith "data_pos out of range"
  in

  let mem = (Array.make mem_size (Byte '\x00')) in
  Array.blit (Array.of_list text_seg) 0 mem mapped_text (List.length text_seg);
  Array.blit (Array.of_list data_seg) 0 mem mapped_data (List.length data_seg);
  Array.blit (Array.of_list (sbytes_of_int64 exit_addr)) 0 mem (mem_size - 8) 8;

  let regs = Array.make nregs 0L in
  regs.(rind Rip) <- entry;
  regs.(rind Rsp) <- Int64.sub mem_top 8L;

  {flags={fo=false; fs=false; fz=false}; regs=regs; mem=mem}
