// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use super::cfg::CFG;
use crate::{cfgir, diagnostics::Diagnostics, hlir::ast::*};
use std::collections::BTreeMap;
use std::fmt::Debug;

/// Trait for finite-height abstract domains. Infinite height domains would require a more complex
/// trait with widening and a partial order.
pub trait AbstractDomain: Clone + Sized {
    fn join(&mut self, other: &Self) -> JoinResult;
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum JoinResult {
    Unchanged,
    Changed,
}

#[derive(Clone)]
enum BlockPostcondition {
    /// Unprocessed block
    Unprocessed,
    /// Analyzing block was successful
    Success,
    /// Analyzing block ended in an error
    Error(Diagnostics),
}

#[derive(Clone)]
struct BlockInvariant<State> {
    /// Precondition of the block
    pre: State,
    /// Postcondition of the block---just success/error for now
    post: BlockPostcondition,
}

/// A map from block id's to the pre/post of each block after a fixed point is reached.
type InvariantMap<State> = BTreeMap<Label, BlockInvariant<State>>;

fn collect_states_and_diagnostics<State>(
    map: InvariantMap<State>,
) -> (BTreeMap<Label, State>, Diagnostics) {
    let mut diags = Diagnostics::new();
    let final_states = map
        .into_iter()
        .map(|(lbl, BlockInvariant { pre, post })| {
            if let BlockPostcondition::Error(ds) = post {
                diags.extend(ds)
            }
            (lbl, pre)
        })
        .collect();
    (final_states, diags)
}

/// Take a pre-state + instruction and mutate it to produce a post-state
/// Auxiliary data can be stored in self.
pub trait TransferFunctions {
    type State: AbstractDomain;

    /// Execute local@instr found at index local@index in the current basic block from pre-state
    /// local@pre.
    /// Should return an AnalysisError if executing the instruction is unsuccessful, and () if
    /// the effects of successfully executing local@instr have been reflected by mutatating
    /// local@pre.
    /// Auxilary data from the analysis that is not part of the abstract state can be collected by
    /// mutating local@self.
    /// The last instruction index in the current block is local@last_index. Knowing this
    /// information allows clients to detect the end of a basic block and special-case appropriately
    /// (e.g., normalizing the abstract state before a join).
    fn execute(
        &mut self,
        pre: &mut Self::State,
        lbl: Label,
        idx: usize,
        command: &Command,
    ) -> Diagnostics;
}

pub trait AbstractInterpreter: TransferFunctions {
    /// Analyze procedure local@function_view starting from pre-state local@initial_state.
    fn analyze_function(
        &mut self,
        cfg: &dyn CFG,
        initial_state: Self::State,
    ) -> (BTreeMap<Label, Self::State>, Diagnostics) where <Self as TransferFunctions>::State: Debug {
        let mut inv_map: InvariantMap<Self::State> = InvariantMap::new();
        let start = cfg.start_block();
        let mut next_block = Some(start);

        // 循环处理每个基本块
        while let Some(block_label) = next_block {
            println!("analyze_function process block_label {:?}, inv_map {:?}", block_label, inv_map.keys());

            let block_invariant = inv_map
                .entry(block_label)
                .or_insert_with(||  {
                    println!("inv_map.entry.or_insert_with");
                    BlockInvariant {
                    pre: initial_state.clone(),
                    post: BlockPostcondition::Unprocessed,
                }});

            //println!("start label {:?} state {:?}", block_label, block_invariant.pre);
            // 执行 transfer 函数处理基本块
            // cfg 当前函数的基本块，用于在执行传递函数时从中查找指令
            // block_invariant.pre 是基本块的 IN 值集合
            // block_label 是当前基本块的 label
            let (post_state, errors) = self.execute_block(cfg, &block_invariant.pre, block_label);
            // 返回值 post_state 是基本块的 OUT 值集
            block_invariant.post = if errors.is_empty() {
                BlockPostcondition::Success
            } else {
                BlockPostcondition::Error(errors)
            };

            //println!("label processed, state {:?}", post_state);

            // propagate postcondition of this block to successor blocks
            // 一个基本块的传递函数执行完成后，传播执行后的 OUT 值到它的每个后继，作为每个后继的 IN
            // 这样在执行后继基本块传递函数的时候，就直接使用 block_invariant.pre 作为其 IN 值集合
            let mut next_block_candidate = cfg.next_block(block_label);
            for next_block_id in cfg.successors(block_label) {  // 找到当前基本块的每个后继
                // 在 inv_map 中查找后继基本块
                // 如果能找到，说明两个基本块有共同的后继基本块
                // 例如有 0, 1, 2, 3 共 4 个基本块
                //     --0--
                //   /       \
                //  /         \
                // 1           2
                //  \         /
                //   \       /
                //     --3--
                // 执行了 0 的传递函数，循环 0 的所有后继 1 和 2，并从 inv_map 查找，发现都找不到，就把 1 和 2 加入到 inv_map
                // 执行了 1 的传递函数，循环 1 的所有后继 3，并从 inv_map 查找，发现都找不到，就把 3 加入到 inv_map
                // 执行了 2 的传递函数，循环 2 的所有后继 3，并从 inv_map 查找，找到了 3，说明要在 3 号基本块执行交汇函数
                // 然后用 3 的 IN 值集，也就是 next_block_invariant.pre
                // 而且因为在 insert 到 inv_map 时，设置了 next_block_invariant.pre 是当前已处理基本块（1号基本块）的 post（复制了一份）
                // 所以这里是用了 1 的 OUT 值集 和 2 的 OUT 值集做交汇运算
                // 结果保存在了 3 的 IN 值集当中
                match inv_map.get_mut(next_block_id) {
                    Some(next_block_invariant) => {  // 如果 inv_map 中存在后继基本块
                        println!("inv_map got next_block_id {:?}", next_block_id);
                        let join_result = {
                            let old_pre = &mut next_block_invariant.pre;
                            old_pre.join(&post_state)
                        };
                        // 接上面的内容：
                        // 如果执行了交汇函数，1 和 2 的 OUT 值集交汇的结果发生了改变
                        // 例如对于 liveness 的对比方式：
                        // 1. 保存 1 的 out 值的集合，即 self.len() 当前的活跃变量列表的长度，作为 before
                        // 2. 执行交汇函数，self.extend(基本块 2 的 out 值集)，
                        // 3. 取得 self.len() 即交汇后的活跃变量列表的长度，作为 after
                        // 4. 如果 before < after，则说明发生了变化
                        // 5. 如果 before == after，则说明未发生变化
                        // 1 和 2 的 OUT 值集交汇的结果是 3 的 IN
                        // 如果 3 的 IN 发生了变化，同样说明 1 和 2 的 OUT 发生变化，需要重新计算
                        // 那么发生变化的原因可能是在数据流中存在循环
                        // 所以下面的代码中检测如果当前基本块和下一个基本块之间存在回边，则说明有循环存在，需要多次执行
                        // cfg.is_back_edge(block_label, *next_block_id) => cfg.is_back_edge(2, 3)
                        // next_block_candidate = Some(*next_block_id) => next_block_candidate = Some(3)
                        // 需要代码测试是否如此
                        match join_result {
                            JoinResult::Unchanged => {
                                // Pre is the same after join. Reanalyzing this block would produce
                                // the same post
                            },
                            JoinResult::Changed => {
                                // If the cur->successor is a back edge, jump back to the beginning
                                // of the loop, instead of the normal next block
                                // 如果 cur->successor 是一个回变，就跳转回循环开始的地方
                                // 而不是下一个基本块
                                if cfg.is_back_edge(block_label, *next_block_id) {
                                    next_block_candidate = Some(*next_block_id);
                                }
                                // Pre has changed, the post condition is now unknown for the block
                                next_block_invariant.post = BlockPostcondition::Unprocessed
                            },
                        }
                    },
                    None => {
                        println!("inv_map insert next_block_id {:?}", next_block_id);
                        // 如果 inv_map 中不存在这个后继基本块，就将这个基本块的后继加入到 inv_map
                        // Haven't visited the next block yet. Use the post of the current block as
                        // its pre
                        // 还没访问这个后继基本块，使用当前基本块的 Post 当作它的 Pre
                        inv_map.insert(*next_block_id, BlockInvariant {
                            pre: post_state.clone(),
                            post: BlockPostcondition::Success,
                        });
                    },
                }
            }
            next_block = next_block_candidate;
        }
        collect_states_and_diagnostics(inv_map)
    }

    fn execute_block(
        &mut self,
        cfg: &dyn CFG,
        pre_state: &Self::State,
        block_lbl: Label,
    ) -> (Self::State, Diagnostics) {
        let mut state = pre_state.clone();
        let mut diags = Diagnostics::new();
        for (idx, cmd) in cfg.commands(block_lbl) {
            diags.extend(self.execute(&mut state, block_lbl, idx, cmd));
        }
        (state, diags)
    }
}
