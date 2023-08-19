/// main.rs is purely for examples and quick tests.
fn main() {
    println!("== Hello from Intel's 8086 ==");

    /* ===============================================
     *  ============= From Machine Code ===============
     *  ===============================================
     */
    let single_register_mov = include_bytes!("../data/binary/single_register_mov.txt");

    // Convert raw inst to type representation
    let inst = intel_8086::read_instruction(single_register_mov[0], single_register_mov[1]).unwrap();

    // Dissasemble
    let asm_from_inst = inst.dissasemble();

    // Assemble back to raw instruction
    let inst_from_inst = inst.assemble().unwrap();

    // Display.
    println!("ASM: {}", asm_from_inst);
    println!(
        "assembled: {:#b} {:#b}",
        inst_from_inst[0], inst_from_inst[1]
    );
    println!("assembled:     {:?}", inst_from_inst);
    println!("from text file {:?}", single_register_mov);

    /* ===============================================
     *  =============== From ASM ======================
     *  ===============================================
     */
    let single_asm_inst = include_str!("../data/asm/single_register_mov.asm");
    let inst_from_asm = intel_8086::read_asm(single_asm_inst).unwrap();
    let asm_from_inst = inst_from_asm.dissasemble();
    let inst_to_raw = inst_from_asm.assemble().unwrap();

    // Display.
    println!("ASM from reconstructed: {}", asm_from_inst);
    println!("assembled: {:#b} {:#b}", inst_to_raw[0], inst_to_raw[1]);
    println!("assembled:     {:?}", inst_to_raw);
}