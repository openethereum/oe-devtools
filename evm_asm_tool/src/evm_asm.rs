// Copyright 2020 Gnosis Ltd.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Context, Error, Result};
use std::collections::HashMap;
pub struct EvmAssembler {
    code: Vec<u8>,
    labels: HashMap<String, usize>,
    pending_labels: HashMap<String, Vec<usize>>,
}

impl EvmAssembler {
    fn new() -> Self {
        Self {
            code: Vec::new(),
            labels: HashMap::new(),
            pending_labels: HashMap::new(),
        }
    }

    fn op_stop(&mut self) {
        self.code.push(0x00);
    }
    fn op_add(&mut self) {
        self.code.push(0x01);
    }
    fn op_mul(&mut self) {
        self.code.push(0x02);
    }
    fn op_sub(&mut self) {
        self.code.push(0x03);
    }
    fn op_div(&mut self) {
        self.code.push(0x04);
    }
    fn op_sdiv(&mut self) {
        self.code.push(0x05);
    }
    fn op_mod(&mut self) {
        self.code.push(0x06);
    }
    fn op_smod(&mut self) {
        self.code.push(0x07);
    }
    fn op_addmod(&mut self) {
        self.code.push(0x08);
    }
    fn op_mulmod(&mut self) {
        self.code.push(0x09);
    }
    fn op_exp(&mut self) {
        self.code.push(0x0a);
    }
    fn op_signextend(&mut self) {
        self.code.push(0x0b);
    }

    fn op_lt(&mut self) {
        self.code.push(0x10);
    }
    fn op_gt(&mut self) {
        self.code.push(0x11);
    }
    fn op_slt(&mut self) {
        self.code.push(0x12);
    }
    fn op_sgt(&mut self) {
        self.code.push(0x13);
    }
    fn op_eq(&mut self) {
        self.code.push(0x14);
    }
    fn op_iszero(&mut self) {
        self.code.push(0x15);
    }
    fn op_and(&mut self) {
        self.code.push(0x16);
    }
    fn op_or(&mut self) {
        self.code.push(0x17);
    }
    fn op_xor(&mut self) {
        self.code.push(0x18);
    }
    fn op_not(&mut self) {
        self.code.push(0x19);
    }
    fn op_byte(&mut self) {
        self.code.push(0x1a);
    }

    fn op_keccak(&mut self) {
        self.code.push(0x20);
    }
    fn op_sha3(&mut self) {
        self.code.push(0x20);
    } // alias

    fn op_address(&mut self) {
        self.code.push(0x30);
    }
    fn op_balance(&mut self) {
        self.code.push(0x31);
    }
    fn op_origin(&mut self) {
        self.code.push(0x32);
    }
    fn op_caller(&mut self) {
        self.code.push(0x33);
    }
    fn op_callvalue(&mut self) {
        self.code.push(0x34);
    }
    fn op_calldataload(&mut self) {
        self.code.push(0x35);
    }
    fn op_calldatasize(&mut self) {
        self.code.push(0x36);
    }
    fn op_calldatacopy(&mut self) {
        self.code.push(0x37);
    }
    fn op_codesize(&mut self) {
        self.code.push(0x38);
    }
    fn op_codecopy(&mut self) {
        self.code.push(0x39);
    }
    fn op_gasprice(&mut self) {
        self.code.push(0x3a);
    }
    fn op_extcodesize(&mut self) {
        self.code.push(0x3b);
    }
    fn op_extcodecopy(&mut self) {
        self.code.push(0x3c);
    }
    fn op_returndatasize(&mut self) {
        self.code.push(0x3d);
    }
    fn op_returndatacopy(&mut self) {
        self.code.push(0x3e);
    }

    fn op_blockhash(&mut self) {
        self.code.push(0x40);
    }
    fn op_coinbase(&mut self) {
        self.code.push(0x41);
    }
    fn op_timestamp(&mut self) {
        self.code.push(0x42);
    }
    fn op_number(&mut self) {
        self.code.push(0x43);
    }
    fn op_difficulty(&mut self) {
        self.code.push(0x44);
    }
    fn op_gaslimit(&mut self) {
        self.code.push(0x45);
    }

    fn op_pop(&mut self) {
        self.code.push(0x50);
    }
    fn op_mload(&mut self) {
        self.code.push(0x51);
    }
    fn op_mstore(&mut self) {
        self.code.push(0x52);
    }
    fn op_mstore8(&mut self) {
        self.code.push(0x53);
    }
    fn op_sload(&mut self) {
        self.code.push(0x54);
    }
    fn op_sstore(&mut self) {
        self.code.push(0x55);
    }

    fn op_jump(&mut self, label: &str) -> Result<()> {
        let offset = self.ref_label(label, 1);
        self.op_push(&offset)?;
        self.code.push(0x56);
        Ok(())
    }

    fn op_jumpi(&mut self, label: &str) -> Result<()> {
        let offset = self.ref_label(label, 1);
        self.op_push(&offset)?;
        self.code.push(0x57);
        Ok(())
    }

    fn op_pc(&mut self) {
        self.code.push(0x58);
    }
    fn op_msize(&mut self) {
        self.code.push(0x59);
    }
    fn op_gas(&mut self) {
        self.code.push(0x5a);
    }

    fn op_jumpdest(&mut self, name: &str) -> Result<()> {
        ensure!(
            !self.labels.contains_key(name),
            format!("Label '{}' already defined", name)
        );
        self.labels.insert(name.to_string(), self.code.len());
        self.code.push(0x5b);

        self.fill_label(name);

        Ok(())
    }

    fn op_beginsub(&mut self, name: &str) -> Result<()> {
        ensure!(
            !self.labels.contains_key(name),
            format!("Label '{}' already defined", name)
        );
        self.labels.insert(name.to_string(), self.code.len());
        self.code.push(0x5c);

        self.fill_label(name);

        Ok(())
    }

    fn op_jumpsub(&mut self, label: &str) -> Result<()> {
        let offset = self.ref_label(label, 1);
        self.op_push(&offset)?;
        self.code.push(0x5e);

        Ok(())
    }

    fn op_returnsub(&mut self) {
        self.code.push(0x5d);
    }

    fn op_push(&mut self, data: &[u8]) -> Result<()> {
        // push n-bytes item into the stack
        ensure!(data.len() >= 1 && data.len() <= 32, "bad push");
        self.code.push(0x5f + data.len() as u8);
        self.code.extend_from_slice(data);

        Ok(())
    }

    fn op_dup(&mut self, n: u8) -> Result<()> {
        ensure!(n > 0 && n <= 16, "bad dup");
        self.code.push(0x80 + n - 1);

        Ok(())
    }

    fn op_swap(&mut self, n: u8) -> Result<()> {
        ensure!(n > 0 && n <= 16, "bad swap");
        self.code.push(0x8f + n);

        Ok(())
    }

    fn op_log0(&mut self) {
        self.code.push(0xa0);
    }
    fn op_log1(&mut self) {
        self.code.push(0xa1);
    }
    fn op_log2(&mut self) {
        self.code.push(0xa2);
    }
    fn op_log3(&mut self) {
        self.code.push(0xa3);
    }
    fn op_log4(&mut self) {
        self.code.push(0xa4);
    }

    fn op_create(&mut self) {
        self.code.push(0xf0);
    }
    fn op_call(&mut self) {
        self.code.push(0xf1);
    }
    fn op_callcode(&mut self) {
        self.code.push(0xf2);
    }
    fn op_return(&mut self) {
        self.code.push(0xf3);
    }
    fn op_delegatecall(&mut self) {
        self.code.push(0xf4);
    }

    fn op_staticcall(&mut self) {
        self.code.push(0xfa);
    }
    fn op_revert(&mut self) {
        self.code.push(0xfd);
    }
    fn op_invalid(&mut self) {
        self.code.push(0xfe);
    }
    fn op_selfdestruct(&mut self) {
        self.code.push(0xff);
    }

    fn push_data_segment(&mut self, label: &str) {
        self.code.push(0x5f + 3);
        let offset = self.ref_label(label, 0);
        self.code.extend_from_slice(&offset);
    }

    fn data_segment(&mut self, label: &str, data: &[u8]) {
        self.labels.insert(label.to_string(), self.code.len());
        self.fill_label(label);
        self.code.extend_from_slice(data);
    }

    fn ref_label(&mut self, label: &str, offset: usize) -> Vec<u8> {
        if let Some(loc) = self.labels.get(label) {
            let loc_bytes = if *loc == 0 {
                vec![0u8]
            } else {
                loc.to_be_bytes()
                    .to_vec()
                    .iter()
                    .skip_while(|n| *n == &0u8)
                    .cloned()
                    .collect::<Vec<_>>()
            };
            loc_bytes
        } else {
            self.pending_labels
                .entry(label.to_string())
                .or_insert_with(Vec::new)
                .push(self.code.len() + offset);
            vec![0, 0, 0]
        }
    }

    fn fill_label(&mut self, label: &str) {
        if let Some(locations) = self.pending_labels.remove(label) {
            let dst = self.labels[label];
            let (dst0, dst1, dst2) = (
                (dst >> 16) as u8,
                ((dst >> 8) & 0xff) as u8,
                (dst & 0xff) as u8,
            );
            locations.iter().for_each(|loc| {
                self.code[loc + 0] = dst0;
                self.code[loc + 1] = dst1;
                self.code[loc + 2] = dst2;
            });
        }
    }

    fn gen_code(&self) -> Result<&Vec<u8>> {
        if self.pending_labels.is_empty() {
            Ok(&self.code)
        } else {
            let list = self.pending_labels.keys().collect::<Vec<_>>();
            bail!(format!("pending_labels {:?}", list))
        }
    }

    #[allow(dead_code)]
    pub fn asm_contract_creation_txdata(&self) -> Result<Vec<u8>> {
        let code = self.gen_code()?;

        let mut tx = EvmAssembler::new();

        // reserve data
        tx.op_push(&[0x80])?;
        tx.op_push(&[0x40])?;
        tx.op_mstore();

        // copy contract code to memory [] -> []
        tx.op_push(&[code.len() as u8])?; // code length
        tx.push_data_segment("code"); // code offset
        tx.op_push(&[0])?; // mem destOffset
        tx.op_codecopy();

        // return memory offset + len
        tx.op_push(&[code.len() as u8])?; // code length
        tx.op_push(&[0])?; // mem destOffset
        tx.op_return();

        tx.op_stop();

        tx.data_segment("code", code);

        Ok(tx.gen_code()?.clone())
    }

    pub fn asm(code: &str) -> Result<Vec<u8>> {
        let mut segments: HashMap<String, EvmAssembler> = HashMap::new();
        let mut current_segment = EvmAssembler::new();
        let mut current_segment_name = String::from("main");

        for (line_no, original_line) in code.split('\n').enumerate() {
            let current_context = || format!("'{}' at :{}", original_line, line_no);
            let mut line = String::from(original_line.trim());
            if line.contains('#') {
                line = line.splitn(2, '#').next().unwrap().trim().to_string();
            }
            if line.starts_with('.') {
                let mut new_segment = EvmAssembler::new();
                std::mem::swap(&mut current_segment, &mut new_segment);
                segments.insert(current_segment_name, new_segment);
                current_segment_name = line.splitn(2, '.').nth(1).unwrap().to_string();
                continue;
            }
            if line.starts_with(':') {
                // jumdest
                let label_rest = &line[1..].split_ascii_whitespace().collect::<Vec<_>>();
                let label = label_rest[0].trim().to_string();
                current_segment
                    .op_jumpdest(&label)
                    .context(current_context())?;
                line = if label_rest.len() > 1 {
                    label_rest[1].trim().to_string()
                } else {
                    continue;
                };
            }
            if line.len() == 0 {
                continue;
            }
            let mut op_extra = line.split_ascii_whitespace();
            let op = op_extra.next().unwrap().to_string();
            let extra: Option<&str> = op_extra.next();

            match (op.as_str(), extra) {
                ("STOP", None) => current_segment.op_stop(),
                ("ADD", None) => current_segment.op_add(),
                ("MUL", None) => current_segment.op_mul(),
                ("SUB", None) => current_segment.op_sub(),
                ("DIV", None) => current_segment.op_div(),
                ("SDIV", None) => current_segment.op_sdiv(),
                ("MOD", None) => current_segment.op_mod(),
                ("SMOD", None) => current_segment.op_smod(),
                ("ADDMOD", None) => current_segment.op_addmod(),
                ("MULMOD", None) => current_segment.op_mulmod(),
                ("EXP", None) => current_segment.op_exp(),
                ("SIGNEXTEND", None) => current_segment.op_signextend(),
                ("LT", None) => current_segment.op_lt(),
                ("GT", None) => current_segment.op_gt(),
                ("SLT", None) => current_segment.op_slt(),
                ("SGT", None) => current_segment.op_sgt(),
                ("EQ", None) => current_segment.op_eq(),
                ("ISZERO", None) => current_segment.op_iszero(),
                ("AND", None) => current_segment.op_and(),
                ("OR", None) => current_segment.op_or(),
                ("XOR", None) => current_segment.op_xor(),
                ("NOT", None) => current_segment.op_not(),
                ("BYTE", None) => current_segment.op_byte(),
                ("KECCACK", None) => current_segment.op_keccak(),
                ("SHA3", None) => current_segment.op_sha3(),
                ("ADDRESS", None) => current_segment.op_address(),
                ("BALANCE", None) => current_segment.op_balance(),
                ("ORIGIN", None) => current_segment.op_origin(),
                ("CALLER", None) => current_segment.op_caller(),
                ("CALLVALUE", None) => current_segment.op_callvalue(),
                ("CALLDATALOAD", None) => current_segment.op_calldataload(),
                ("CALLDATASIZE", None) => current_segment.op_calldatasize(),
                ("CALLDATACOPY", None) => current_segment.op_calldatacopy(),
                ("CODESIZE", None) => current_segment.op_codesize(),
                ("CODECOPY", None) => current_segment.op_codecopy(),
                ("GASPRICE", None) => current_segment.op_gasprice(),
                ("EXTCODESIZE", None) => current_segment.op_extcodesize(),
                ("EXTCODECOPY", None) => current_segment.op_extcodecopy(),
                ("RETURNDATASIZE", None) => current_segment.op_returndatasize(),
                ("RETURNDATACOPY", None) => current_segment.op_returndatacopy(),
                ("BLOCKHASH", None) => current_segment.op_blockhash(),
                ("COINBASE", None) => current_segment.op_coinbase(),
                ("TIMESTAMP", None) => current_segment.op_timestamp(),
                ("NUMBER", None) => current_segment.op_number(),
                ("DIFFICULTY", None) => current_segment.op_difficulty(),
                ("GASLIMIT", None) => current_segment.op_gaslimit(),
                ("POP", None) => current_segment.op_pop(),
                ("MLOAD", None) => current_segment.op_mload(),
                ("MSTORE", None) => current_segment.op_mstore(),
                ("MSTORE8", None) => current_segment.op_mstore8(),
                ("SLOAD", None) => current_segment.op_sload(),
                ("SSTORE", None) => current_segment.op_sstore(),
                ("JUMP", Some(label)) => {
                    current_segment.op_jump(&label).context(current_context())?
                }
                ("JUMPI", Some(label)) => current_segment
                    .op_jumpi(&label)
                    .context(current_context())?,
                ("PC", None) => current_segment.op_pc(),
                ("MSIZE", None) => current_segment.op_msize(),
                ("GAS", None) => current_segment.op_gas(),
                ("JUMPDEST", Some(label)) => current_segment
                    .op_jumpdest(&label)
                    .context(current_context())?,
                ("BEGINSUB", Some(label)) => current_segment
                    .op_beginsub(&label)
                    .context(current_context())?,
                ("JUMPSUB", Some(label)) => current_segment
                    .op_jumpsub(&label)
                    .context(current_context())?,
                ("RETURNSUB", None) => current_segment.op_returnsub(),
                ("PUSH", Some(data)) => {
                    if data.starts_with("0x") {
                        current_segment
                            .op_push(&hex::decode(&data[2..]).unwrap())
                            .context(current_context())?;
                    } else if data.ends_with(".len") {
                        let label = &data[..data.len() - ".len".len()];
                        let len = segments[label].gen_code()?.len();
                        if len > 255 {
                            return Err(Error::msg(format!("Segment too big {}", len)));
                        }
                        current_segment
                            .op_push(&[len as u8])
                            .context(current_context())?;
                    } else if data.ends_with(".offset") {
                        let label = &data[..data.len() - ".offset".len()];
                        current_segment.push_data_segment(label);
                    } else {
                        return Err(Error::msg(format!(
                            "Unable to process line {}",
                            original_line
                        )));
                    }
                }
                ("DUP1", None) => current_segment.op_dup(1).unwrap(),
                ("DUP2", None) => current_segment.op_dup(2).unwrap(),
                ("DUP3", None) => current_segment.op_dup(3).unwrap(),
                ("DUP4", None) => current_segment.op_dup(4).unwrap(),
                ("DUP5", None) => current_segment.op_dup(5).unwrap(),
                ("DUP6", None) => current_segment.op_dup(6).unwrap(),
                ("DUP7", None) => current_segment.op_dup(7).unwrap(),
                ("DUP8", None) => current_segment.op_dup(8).unwrap(),
                ("DUP9", None) => current_segment.op_dup(9).unwrap(),
                ("DUP10", None) => current_segment.op_dup(10).unwrap(),
                ("DUP11", None) => current_segment.op_dup(11).unwrap(),
                ("DUP12", None) => current_segment.op_dup(12).unwrap(),
                ("DUP13", None) => current_segment.op_dup(13).unwrap(),
                ("DUP14", None) => current_segment.op_dup(14).unwrap(),
                ("DUP15", None) => current_segment.op_dup(15).unwrap(),
                ("DUP16", None) => current_segment.op_dup(16).unwrap(),
                ("SWAP", None) => current_segment.op_swap(1).unwrap(),
                ("SWAP2", None) => current_segment.op_swap(2).unwrap(),
                ("SWAP3", None) => current_segment.op_swap(3).unwrap(),
                ("SWAP4", None) => current_segment.op_swap(4).unwrap(),
                ("SWAP5", None) => current_segment.op_swap(5).unwrap(),
                ("SWAP6", None) => current_segment.op_swap(6).unwrap(),
                ("SWAP7", None) => current_segment.op_swap(7).unwrap(),
                ("SWAP8", None) => current_segment.op_swap(8).unwrap(),
                ("SWAP9", None) => current_segment.op_swap(9).unwrap(),
                ("SWAP10", None) => current_segment.op_swap(10).unwrap(),
                ("SWAP11", None) => current_segment.op_swap(11).unwrap(),
                ("SWAP12", None) => current_segment.op_swap(12).unwrap(),
                ("SWAP13", None) => current_segment.op_swap(13).unwrap(),
                ("SWAP14", None) => current_segment.op_swap(14).unwrap(),
                ("SWAP15", None) => current_segment.op_swap(15).unwrap(),
                ("SWAP16", None) => current_segment.op_swap(16).unwrap(),
                ("LOG0", None) => current_segment.op_log0(),
                ("LOG1", None) => current_segment.op_log1(),
                ("LOG2", None) => current_segment.op_log2(),
                ("LOG3", None) => current_segment.op_log3(),
                ("LOG4", None) => current_segment.op_log4(),
                ("CREATE", None) => current_segment.op_create(),
                ("CALL", None) => current_segment.op_call(),
                ("CALLCODE", None) => current_segment.op_callcode(),
                ("RETURN", None) => current_segment.op_return(),
                ("DELEGATECALL", None) => current_segment.op_delegatecall(),
                ("STATICCALL", None) => current_segment.op_staticcall(),
                ("REVERT", None) => current_segment.op_revert(),
                ("INVALID", None) => current_segment.op_invalid(),
                ("SELFDESTRUCT", None) => current_segment.op_selfdestruct(),
                _ => {
                    return Err(Error::msg(format!(
                        "Unable to process line {}",
                        original_line
                    )))
                }
            }
        }
        let mut new_segment = EvmAssembler::new();
        std::mem::swap(&mut current_segment, &mut new_segment);
        segments.insert(current_segment_name, new_segment);

        let mut main = segments.remove("main").unwrap();
        for (label, value) in segments.into_iter() {
            main.data_segment(&label, value.gen_code()?);
        }

        Ok(main.gen_code()?.clone())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn assert_code_eq(code: &[u8], input: &str) {
        let mut trimmed = String::with_capacity(input.len());
        for l in input.split('\n') {
            l.chars()
                .take_while(|ch| *ch != '#')
                .filter(|ch| *ch != ' ')
                .for_each(|ch| trimmed.push(ch));
        }
        assert_eq!(hex::encode(code), trimmed);
    }

    #[test]
    fn test_simple_asm() {
        assert_code_eq(
            &EvmAssembler::asm(
                "
                PUSH 0x01
                PUSH 0x03
                DUP2
                STOP
            ",
            )
            .unwrap(),
            "
                60 01  # PUSH1 01
                60 03  # PUSH1 03
                81     # DUP2
                00     # STOP
            ",
        );
    }

    #[test]
    fn test_call_a() {
        assert_code_eq(
            &EvmAssembler::asm(
                "
                :loop
                PUSH 0x00
                PUSH 0x00
                PUSH 0x00
                PUSH 0x00
                PUSH 0x00
                PUSH 0xff0b                
                GAS
                CALL
                JUMP loop
            ",
            )
            .unwrap(),
            "5b 6000 6000 6000 6000 6000 61ff0b 5a f1 60 00 56",
        );
    }

    #[test]
    fn test_data_segment() {
        let code = "
            .contract
            PC
            DUP1
            DUP1
            DUP1
            DUP1
            ADDRESS
            GAS
            CALL
            
            .main
            # copy contract code to memory [] -> []
            PUSH contract.len  
            PUSH contract.offset
            PUSH 0x00  # mem destOffset
            CODECOPY

            # create contract [] -> [addr]
            PUSH contract.len
            PUSH 0x00 # mem offset
            PUSH 0x00 # value
            CREATE

            # store contract address to memory[0..31] [addr] -> []
            PUSH 0x00 #  [offset=0,value]
            MSTORE

            :loop
              PUSH 0x00 # retLen
              PUSH 0x00 # retOffset
              PUSH 0x00 # argsLen
              PUSH 0x00 # argsOffset
              PUSH 0x00 # value
              PUSH 0x00 # mload contract addr
                MLOAD
              GAS
              CALL
            JUMP loop
        ";

        assert_code_eq(
            &EvmAssembler::asm(code).unwrap(),
            "600862000026600039600860006000f06000525b600060006000600060006000515af16013565880808080305af1"
        );
    }

    #[test]
    fn test_sub() {
        let code = "
            JUMPSUB sub
            STOP
            BEGINSUB sub
            RETURNSUB
        ";

        assert_code_eq(&EvmAssembler::asm(code).unwrap(), "62000006 5e 00 5c 5d");
    }
}
