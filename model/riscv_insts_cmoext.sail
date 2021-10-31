/* ****************************************************************** */
/* This file specifies the instructions in the cmo extension */


/* ****************************************************************** */
union clause ast = RISCV_CBO : (cbop, regidx)

mapping encdec_cbop : cbop <-> bits(12) = {
  CBO_CLEAN <-> 0b000000000001,
  CBO_FLUSH <-> 0b000000000010,
  CBO_INVAL <-> 0b000000000000,
  CBO_ZERO  <-> 0b000000000100
}

mapping clause encdec = RISCV_CBO(cbop, rs1)
  <-> encdec_cbop(cbop) @ rs1 @ 0b010 @ 0b00000 @ 0b0001111

mapping cbo_mnemonic : cbop <-> string = {
  CBO_CLEAN <-> "cbo.clean",
  CBO_FLUSH <-> "cbo.flush",
  CBO_INVAL <-> "cbo.inval",
  CBO_ZERO  <-> "cbo.zero"
}

mapping clause assembly = RISCV_CBO(cbop, rs1)
  <-> cbo_mnemonic(cbop) ^ spc() ^ reg_name(rs1)

val process_cbo_zero : (xlenbits, xlenbits) -> Retired effect {eamem, escape, rmem, rmemt, rreg, wmv, wmvt, wreg}
function process_cbo_zero(vaddr, width)  = {
  let ret : bool = match ext_data_get_addr(to_bits(5, 0), vaddr, Write(Data), DOUBLE) {
        Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); false },
        Ext_DataAddr_OK(vaddr) =>
          match translateAddr(vaddr, Write(Data)) {
            TR_Failure(e, _)    => { handle_mem_exception(vaddr, e); false },
            TR_Address(paddr, _) => {
              let eares : MemoryOpResult(unit) = mem_write_ea(paddr, 8, false, false, false);
              match (eares) {
                MemException(e) => { handle_mem_exception(vaddr, e); false },
                MemValue(_) => {
                  let res : MemoryOpResult(bool) = mem_write_value(paddr, 8, to_bits(64, 0), false, false, false);
                  match (res) {
                    MemValue(true)  => true,
                    MemValue(false) => internal_error("store got false from mem_write_value"),
                    MemException(e) => { handle_mem_exception(vaddr, e); false }
                  }
                }
              }
            }
          }
  };
  if ret then
    if (unsigned(width) > 8) then
      process_cbo_zero(vaddr + EXTZ(0b1000), width - EXTZ(0b1000))
    else
      RETIRE_SUCCESS
  else
    RETIRE_FAIL
}

function check_clean_flush(p : Privilege) -> bool = {
  let ret : bool = ~(((p != Machine) & (menvcfg.CBCFE() == 0b0)) |
                    ((p == User) & (senvcfg.CBCFE() == 0b0)));
  ret
}

function check_inval(p : Privilege) -> bits(2) = {
  let bit0 : bool = ((p != Machine) & (menvcfg.CBIE() == 0b00)) |
                    ((p == User) & (senvcfg.CBIE() == 0b00));
  let bit1 : bool = ((p != Machine) & (menvcfg.CBIE() == 0b01)) |
                    ((p == User) & (senvcfg.CBIE() == 0b01));
  if bit0 then EXTZ(0b0)
  else if bit1 then EXTZ(0b1)
  else EXTZ(0b11)
}

function check_zero(p : Privilege) -> bool = {
  let ret : bool = ~(((p != Machine) & (menvcfg.CBZE() == 0b0)) |
                    ((p == User) & (senvcfg.CBZE() == 0b0)));
  ret
}

function clause execute(RISCV_CBO(cbop, rs1)) = {
  let rs1_val = X(rs1);
  let cache_block_size : xlenbits = plat_cache_block_size() ;
  let vaddr: xlenbits = rs1_val ^ (cache_block_size - EXTZ(to_bits(1,1)));
  match cbop {
  CBO_CLEAN => {
      if (check_clean_flush(cur_privilege)) then
        /* perform clean*/
        RETIRE_SUCCESS
      else {
        handle_illegal();
        RETIRE_FAIL
      }
    },
  CBO_FLUSH => {
      if (check_clean_flush(cur_privilege)) then
        /* perform flush*/
        RETIRE_SUCCESS
      else {
        handle_illegal();
        RETIRE_FAIL
      }
    },
  CBO_INVAL => {
      match (check_inval(cur_privilege)) {
        0b00 => {
          handle_illegal();
          RETIRE_FAIL
          },
        0b01 => RETIRE_SUCCESS, /*perform flush*/
        0b10 => RETIRE_SUCCESS /*perform inval*/
      }
    },
  CBO_ZERO  => {
      if (check_zero(cur_privilege)) then
        process_cbo_zero(vaddr, cache_block_size)
      else {
        handle_illegal();
        RETIRE_FAIL
      }
    }
  }
}

union clause ast = RISCV_PREFETCH : (preop, regidx, bits(7))

mapping encdec_prefetch : preop <-> bits(5) = {
  PREFETCH_I <-> 0b00000,
  PREFETCH_R <-> 0b00001,
  PREFETCH_W <-> 0b00011
}

mapping clause encdec = RISCV_PREFETCH(op, rs1, offset)
  <-> offset @ encdec_prefetch(op) @ rs1 @ 0b110 @ 0b00000 @ 0b0010011

mapping pre_mnemonic : preop <-> string = {
  PREFETCH_I <-> "prefetch.i",
  PREFETCH_R <-> "prefetch.r",
  PREFETCH_W <-> "prefetch.w"
}

mapping clause assembly = RISCV_PREFETCH(op, rs1, offset)
  <-> pre_mnemonic(op) ^ spc() ^ hex_bits_12(offset @ 0b00000) ^ "(" ^ reg_name(rs1) ^ ")" 

function clause execute(RISCV_PREFETCH(preop, rs1, offset)) = {
  /* do nothing for prefetch.i/r/w */
  RETIRE_SUCCESS
}