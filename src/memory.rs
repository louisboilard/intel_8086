/* ===============================================
*  ===============   MEMORY   ====================
*  ===============================================
*/

/// Size of the memory. i.e number of byte slots.
const MEM_SIZE: usize = 1024 * 1024; // 1mb

/// An array representing memory and it's basic load(read)/store(write) operations
#[derive(Debug)]
pub struct Memory {
    mem: [u8; MEM_SIZE],
}

impl Memory {
    /// Initializes memory
    pub fn new() -> Self {
        Self { mem: [0; MEM_SIZE] }
    }

    /// A memory read/load
    pub fn read(&self, index: usize) -> u8 {
        self.mem[index]
    }

    /// A memory write/store
    pub fn write(&mut self, value: u8, index: usize) {
        self.mem[index] = value;
    }
}
