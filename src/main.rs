use intel_8086::Instructionable;
/// main.rs is purely for examples and quick tests.
fn main() {
    println!("== Hello from Intel's 8086 ==");

    /* ===============================================
     *  ============= From Machine Code ===============
     *  ===============================================
     */
    let single_register_mov = include_bytes!("../data/binary/single_register_mov.txt");

    let inst = intel_8086::read_instructions(single_register_mov).unwrap();

    // disassemble
    let asm_from_inst = inst[0].disassemble();

    // Assemble back to raw instruction
    let inst_from_inst = inst[0].assemble().unwrap();

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
    // let single_asm_inst = include_str!("../data/asm/single_register_mov.asm");
    let inst2 = &inst[0];
    let asm_from_inst = inst2.disassemble();
    let inst_to_raw = inst2.assemble().unwrap();

    // Display.
    println!("ASM from reconstructed: {}", asm_from_inst);
    println!("assembled: {:#b} {:#b}", inst_to_raw[0], inst_to_raw[1]);
    println!("assembled:     {:?}", inst_to_raw);
}
