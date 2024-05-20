// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

//**************************************************************************************************
// Abstract state
//**************************************************************************************************

use crate::{cfgir::absint::*, parser::ast::Var};
use std::{cmp::Ordering, collections::BTreeSet};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LivenessState(pub BTreeSet<Var>);

//**************************************************************************************************
// impls
//**************************************************************************************************

impl LivenessState {
    pub fn initial() -> Self {
        LivenessState(BTreeSet::new())
    }

    pub fn extend(&mut self, other: &Self) {
        self.0.extend(other.0.iter().cloned());
    }
}

impl AbstractDomain for LivenessState {
    fn join(&mut self, other: &Self) -> JoinResult {
        // 交汇函数的作用是：我们在编译期无法确定实际执行时，运行期实际运行的是哪个分支，所以直接认为所有分支都可能会运行
        // 那么就需要把两个分支的状态，交汇为一个状态
        // 代码中做并集只是其中一种选择，也可能做交集，或者其他运算方式，具体是哪种方式和实际的数据流问题相关

        // 在数据流执行框架中发现分支结构，或者循环结构，就会执行交汇函数
        // 不论是分支还是循环，都会执行交汇函数
        // 但是循环在执行了交汇函数之后，会再执行一遍循环体代码

        // 取得需要与当前基本块交汇的基本块的 OUT 状态
        // 例如 1 和 2 在基本块 3 交汇，这里的 self 是 3.pre
        // 3.pre 的内容是从 1.out 而来，是在执行基本块 1 时插入的
        // other 是基本块 2 执行后的 OUT 状态，所以交汇的内容本质是 1 和 2 的 OUT 状态
        // (因为数据流分析框架只有一个，如果是逆向数据流先把流图直接逆向，包括基本块的命令顺序也逆向)
        //（就不需要一个前向的数据流框架，一个逆向的框架了）
        // before 是计算出 3.pre 的长度
        let before = self.0.len();
        // 然后将 2.out 和 3.pre(1.out) 做 extend 并集运算
        // 这里执行了交汇之后，交汇的数据保存到了 3.pre 之中
        // 就不需要再在数据流框架中，根据 Changed 再次执行所有区块，效率更高
        self.extend(other);
        // after 是计算出做并集(2.out 并 1.out)后的长度
        // 如果并集后之前的内容，小于做并集之后的内容，说明两个分支交汇，发生了内容变化
        // 如果相等，则说明没有发生变化
        // 如果大于，则说明发生内部错误，实际不可能变大
        let after = self.0.len();
        match before.cmp(&after) {
            Ordering::Less => JoinResult::Changed,
            Ordering::Equal => JoinResult::Unchanged,
            Ordering::Greater => panic!("ICE set union made a set smaller than before"),
        }
    }
}
