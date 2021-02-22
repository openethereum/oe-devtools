// Copyright 2020 Gnosis Ltd.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde::{de::Error, Deserialize, Deserializer}; // 1.0.94
use serde_json; // 1.0.40
use std::{borrow::Cow, collections::HashMap, fs::File, io::BufRead, path::Path};
use tabular::{Row, Table};

#[derive(Clone, Debug, PartialEq)]
struct U64Hex(u64);

impl<'de> Deserialize<'de> for U64Hex {
    fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s: &str = Deserialize::deserialize(deserializer)?;
        u64::from_str_radix(&s[2..], 16)
            .map(|u| U64Hex(u))
            .map_err(D::Error::custom)
    }
}

#[derive(Debug, Deserialize)]
struct EvmStep {
    #[serde(skip_deserializing)]
    original: String,
    depth: usize,
    gas: U64Hex,
    op: u8,
    #[serde(rename = "opName")]
    op_name: String,
    pc: usize,
    stack: Vec<String>,
    #[serde(rename = "gasCost")]
    gas_cost: Option<U64Hex>,
    error: Option<String>,
}

fn read_file(path: &std::path::Path) -> Result<Vec<EvmStep>> {
    let mut v = Vec::new();
    let file = File::open(path)?;
    for line in std::io::BufReader::new(file).lines() {
        let line = line?;
        if line.contains("opName") {
            let mut evmstep: EvmStep = serde_json::from_str(&line)?;
            evmstep.original = line;
            v.push(evmstep);
        }
    }
    Ok(v)
}

fn it_diff<T, I1, I2>(first_it: I1, second_it: I2) -> Vec<(T, bool, bool)>
where
    T: PartialOrd + Ord + Copy,
    I1: IntoIterator<Item = T>,
    I2: IntoIterator<Item = T>,
{
    let mut v = Vec::new();

    let mut first = first_it.into_iter().collect::<Vec<_>>();
    let mut second = second_it.into_iter().collect::<Vec<_>>();
    first.sort();
    second.sort();
    let mut first_it = first.iter();
    let mut second_it = second.iter();

    let mut maybe_first = first_it.next();
    let mut maybe_second = second_it.next();
    loop {
        match (maybe_first.is_some(), maybe_second.is_some()) {
            (true, true) => {
                let first = maybe_first.unwrap();
                let second = maybe_second.unwrap();
                match first.cmp(second) {
                    std::cmp::Ordering::Equal => {
                        v.push((*first, true, true));
                        maybe_first = first_it.next();
                        maybe_second = second_it.next();
                    }
                    std::cmp::Ordering::Greater => {
                        v.push((*second, false, true));
                        maybe_second = second_it.next();
                    }
                    std::cmp::Ordering::Less => {
                        v.push((*first, true, false));
                        maybe_first = first_it.next();
                    }
                }
            }
            (true, false) => {
                v.push((*maybe_first.unwrap(), true, false));
                maybe_first = first_it.next();
            }
            (false, true) => {
                v.push((*maybe_second.unwrap(), false, true));
                maybe_second = second_it.next();
            }
            (false, false) => {
                break;
            }
        }
    }
    v
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    let first_file = Path::new(&args[1]);
    let second_file = Path::new(&args[2]);

    println!("diffin' {:?} {:?}", first_file, second_file);
    let first = read_file(first_file)?;
    let second = read_file(second_file)?;

    let gas_diff = |v: &Vec<EvmStep>, n: usize| {
        if n == 0 {
            Cow::Borrowed("")
        } else {
            if v[n].depth == v[n - 1].depth {
                Cow::Owned(format!("{}", v[n].gas.0 as i64 - v[n - 1].gas.0 as i64))
            } else if v[n].depth < v[n - 1].depth {
                let mut diff = -1000;
                for k in (0..=n - 1).rev() {
                    if v[k].depth == v[n].depth {
                        diff = v[n].gas.0 as i64 - v[k].gas.0 as i64;
                        break;
                    }
                }
                Cow::Owned(format!("{}", diff))
            } else {
                Cow::Borrowed("")
            }
        }
    };

    let mut table = Table::new("{:>} {:>} {:>}  {:<} {:>} {:>} {:>} {:<}     {:<}");
    table.add_row(
        Row::new()
            .with_cell("")
            .with_cell("DEPTH")
            .with_cell("PC")
            .with_cell("OP")
            .with_cell("GAS")
            .with_cell("ΔGAS")
            .with_cell("GCOST")
            .with_cell("ERR")
            .with_cell("STACK"),
    );

    for n in 0..std::cmp::min(first.len(), second.len()) {
        let (f, s) = (&first[n], &second[n]);
        let mut diff = Vec::new();
        if f.pc != s.pc {
            diff.push(format!("pc=({},{})\n", f.pc, s.pc));
        }
        if f.op != s.op {
            diff.push(format!("op=({},{})\n", f.op_name, s.op_name));
        }
        if f.depth != s.depth {
            diff.push(format!("depth=({},{})\n", f.depth, s.depth));
        }
        if f.gas.0 != s.gas.0 {
            let f_gas_used = f.gas.0 as i64 - first[n - 1].gas.0 as i64;
            let s_gas_used = s.gas.0 as i64 - second[n - 1].gas.0 as i64;

            diff.push(format!(
                "gas_used=({},{}) diff={}",
                f_gas_used,
                s_gas_used,
                f_gas_used - s_gas_used
            ));
        }
        for stackn in 0..std::cmp::max(f.stack.len(), s.stack.len()) {
            match (stackn < f.stack.len(), stackn < s.stack.len()) {
                (true, true) if f.stack[stackn] != s.stack[stackn] => diff.push(format!(
                    "stack_{}=({},{}) ",
                    stackn, f.stack[stackn], s.stack[stackn]
                )),
                (true, false) => diff.push(format!("stack_{}=({},none) ", stackn, f.stack[stackn])),
                (false, true) => diff.push(format!("stack_{}=(none,{}) ", stackn, s.stack[stackn])),
                _ => {}
            }
        }

        if diff.len() > 0 {
            table.add_row(
                Row::new()
                    .with_cell("F")
                    .with_cell(f.depth)
                    .with_cell(f.pc)
                    .with_cell(&f.op_name)
                    .with_cell(format!("{:?}", f.gas.0))
                    .with_cell(gas_diff(&first, n))
                    .with_cell(format!("{:?}", f.gas_cost.clone().unwrap().0))
                    .with_cell(format!("{}", f.error.as_ref().unwrap_or(&String::from(""))))
                    .with_cell(format!("{:?}", f.stack)),
            );

            table.add_row(
                Row::new()
                    .with_cell("S")
                    .with_cell(s.depth)
                    .with_cell(s.pc)
                    .with_cell(&s.op_name)
                    .with_cell(format!("{:?}", s.gas.0))
                    .with_cell(gas_diff(&second, n))
                    .with_cell(format!("-"))
                    .with_cell(format!("{}", s.error.as_ref().unwrap_or(&String::from(""))))
                    .with_cell(format!("{:?}", s.stack)),
            );

            println!("{}", table);
            println!("-------------------------------------------------------------");
            println!("{}", diff.join("\n"));
            println!("FIRST  {}", f.original);
            println!("SECOND {}", s.original);
            println!("-------------------------------------------------------------");
            return Ok(());
        } else {
            table.add_row(
                Row::new()
                    .with_cell("=")
                    .with_cell(f.depth)
                    .with_cell(f.pc)
                    .with_cell(&f.op_name)
                    .with_cell(format!("{:?}", f.gas.0))
                    .with_cell(gas_diff(&first, n))
                    .with_cell(format!("{:?}", f.gas_cost.clone().unwrap().0))
                    .with_cell(format!("{}", f.error.as_ref().unwrap_or(&String::from(""))))
                    .with_cell(format!("{:?}", f.stack)),
            );
        }
    }
    println!("{}", table);
    println!("No diff.");
    Ok(())
}

#[test]
fn test_diff() {
    let empty: Vec<&str> = Vec::new();
    assert_eq!(
        it_diff(&["a", "b", "c"], &["a", "b", "c"]),
        vec![(&"a", true, true), (&"b", true, true), (&"c", true, true)]
    );
    assert_eq!(
        it_diff(&["a", "b"], &["b", "c"]),
        vec![(&"a", true, false), (&"b", true, true), (&"c", false, true)]
    );
    assert_eq!(it_diff(&["a"], &empty), vec![(&"a", true, false)]);
    assert_eq!(it_diff(&empty, &["b"]), vec![(&"b", false, true)]);
}
