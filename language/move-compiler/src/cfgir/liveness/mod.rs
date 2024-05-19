// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use super::{
    absint::*,
    cfg::{BlockCFG, ReverseBlockCFG, CFG},
    locals,
};
use crate::{
    diagnostics::Diagnostics,
    hlir::ast::{self as H, *},
    parser::ast::Var,
    shared::{unique_map::UniqueMap, CompilationEnv},
};
use move_ir_types::location::*;
use state::*;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use crate::cfgir::locals::state::LocalState;
use crate::shared::ast_debug::{display, print, print_verbose};

mod state;

//**************************************************************************************************
// Entry and trait bindings
//**************************************************************************************************

type PerCommandStates = BTreeMap<Label, VecDeque<LivenessState>>;
type ForwardIntersections = BTreeMap<Label, BTreeSet<Var>>;
type FinalInvariants = BTreeMap<Label, LivenessState>;

struct Liveness {
    states: PerCommandStates,
}

impl Liveness {
    fn new(cfg: &super::cfg::ReverseBlockCFG) -> Self {
        let states = cfg
            .blocks()
            .iter()
            .map(|(lbl, block)| {
                let init = block.iter().map(|_| LivenessState::initial()).collect();
                (*lbl, init)
            })
            .collect();
        Liveness { states }
    }
}

impl TransferFunctions for Liveness {
    type State = LivenessState;

    fn execute(
        &mut self,
        state: &mut Self::State,
        label: Label,
        idx: usize,
        cmd: &Command,
    ) -> Diagnostics {
        command(state, cmd);
        // set current [label][command_idx] data with the new liveness data
        // 设置每个 [基本块][命令idx] 的状态
        let cur_label_states = self.states.get_mut(&label).unwrap();
        cur_label_states[idx] = state.clone();
        println!("liveness execute command {:?} {:?} -> state {:?}", label, display(cmd), state.clone());
        Diagnostics::new()
    }
}

impl AbstractInterpreter for Liveness {}

//**************************************************************************************************
// Analysis
//**************************************************************************************************

fn analyze(
    cfg: &mut BlockCFG,
    infinite_loop_starts: &BTreeSet<Label>,
) -> (FinalInvariants, PerCommandStates) {
    println!("\n000000000 !!!!!!!!!! cfg");
    print_verbose(cfg);
    println!("\n");
    // 将 CFG 逆向
    let reverse = &mut ReverseBlockCFG::new(cfg, infinite_loop_starts);
    println!("\n1111111111 reverse_cfg");
    print_verbose(reverse);
    println!("\n");
    // 初始状态，用于在数据流分析中保存所有活跃的变量
    let initial_state = LivenessState::initial();
    // 初始化每个基本块中每个命令的初始状态，每个命令的初始状态是一个 BtreeSet
    let mut liveness = Liveness::new(reverse);
    // 执行数据流分析，并拿到过程中所有基本块的状态
    let (final_invariants, errors) = liveness.analyze_function(reverse, initial_state);
    // final_invariants 是每个基本块对应的变量活跃状态
    assert!(errors.is_empty());
    println!("\n\nfinal_invariants");
    for (k, v) in final_invariants.iter() {
        print!("Label: {:?}\n", k);
        for var in v.0.iter() {
            print!("    {:?}\n", var);
        }
        print!("\n");
    }
    println!("\nliveness.states");
    for (k, v) in liveness.states.iter() {
        print!("Label: {:?}\n", k);
        for (cmd_idx, cmds_state) in v.iter().enumerate() {
            print!("    cmd index: {:?} <- ", cmd_idx);
            for var in cmds_state.0.iter() {
                print!(" {:?}", var);
            }
            print!("\n");
        }
        print!("\n");
    }
    // liveness.states 保存了 [基本块][命令idx] 的状态
    // 也就是保存了每个命令执行后，命令所在的基本块的状态
    (final_invariants, liveness.states)
}

/*
是 Assign 命令：
左值：如果是 let 在 state 中删除变量
右值：调用表达式处理函数

如果是表达式：
借用、copy、move：在 state 中插入变量
其他类型的表达式递归调用。
 */
fn command(state: &mut LivenessState, sp!(_, cmd_): &Command) {
    use Command_ as C;
    match cmd_ {
        // 赋值命令
        // 左值：如果是 let 则在 state 中删除变量
        C::Assign(ls, e) => {
            lvalues(state, ls);
            exp(state, e);
        },
        C::Mutate(el, er) => {
            exp(state, er);
            exp(state, el)
        },
        C::Return { exp: e, .. }
        | C::Abort(e)
        | C::IgnoreAndPop { exp: e, .. }
        | C::JumpIf { cond: e, .. } => exp(state, e),

        C::Jump { .. } => (),
        C::Break | C::Continue => panic!("ICE break/continue not translated to jumps"),
    }
}

fn lvalues(state: &mut LivenessState, ls: &[LValue]) {
    ls.iter().for_each(|l| lvalue(state, l))
}

fn lvalue(state: &mut LivenessState, sp!(_, l_): &LValue) {
    use LValue_ as L;
    match l_ {
        L::Ignore => (),
        L::Var(v, _) => {
            state.0.remove(v);  // 如果是变量定义 let 则从状态中移除变量
        },
        L::Unpack(_, _, fields) => fields.iter().for_each(|(_, l)| lvalue(state, l)),
    }
}

fn exp(state: &mut LivenessState, parent_e: &Exp) {
    use UnannotatedExp_ as E;
    match &parent_e.exp.value {
        E::Unit { .. } | E::Value(_) | E::Constant(_) | E::UnresolvedError => (),

        E::BorrowLocal(_, var) | E::Copy { var, .. } | E::Move { var, .. } => {
            // 如果是借用、copy、move变量
            // 则在 state 中插入变量
            state.0.insert(*var);
        },

        E::Spec(anchor) => anchor.used_locals.values().for_each(|(_, v)| {
            state.0.insert(*v);
        }),

        E::ModuleCall(mcall) => exp(state, &mcall.arguments),
        E::Builtin(_, e)
        | E::Vector(_, _, _, e)
        | E::Freeze(e)
        | E::Dereference(e)
        | E::UnaryExp(_, e)
        | E::Borrow(_, e, _)
        | E::Cast(e, _) => exp(state, e),

        E::BinopExp(e1, _, e2) => {
            exp(state, e1);
            exp(state, e2)
        },

        E::Pack(_, _, fields) => fields.iter().for_each(|(_, _, e)| exp(state, e)),

        E::ExpList(es) => es.iter().for_each(|item| exp_list_item(state, item)),

        E::Unreachable => panic!("ICE should not analyze dead code"),
    }
}

fn exp_list_item(state: &mut LivenessState, item: &ExpListItem) {
    match item {
        ExpListItem::Single(e, _) | ExpListItem::Splat(_, e, _) => exp(state, e),
    }
}

//**************************************************************************************************
// Copy Refinement
//**************************************************************************************************

/// This pass:
/// - Switches the last inferred `copy` to a `move`.
///   It will error if the `copy` was specified by the user
/// - Reports an error if an assignment/let was not used
///   Switches it to an `Ignore` if it has the drop ability (helps with error messages for borrows)

pub fn last_usage(
    compilation_env: &mut CompilationEnv,
    locals: &UniqueMap<Var, SingleType>,
    cfg: &mut BlockCFG,
    infinite_loop_starts: &BTreeSet<Label>,
) {
    println!("\n\n!!!!!! liveness::last_usage start !!!!!!");
    // 使用基于逆向数据流分析的方式得到活跃变量列表
    // final_invariants 是每个基本块出口的活跃变量列表
    // per_command_states 是每个基本块中每个命令执行之前的活跃变量列表
    let (final_invariants, per_command_states) = analyze(cfg, infinite_loop_starts);
    // 循环 CFG 中的每个基本块
    // 根据每个基本块的出口的活跃变量列表，以及每个基本块中每个命令执行前的活跃变量列表
    // 找到基本块中不再活跃的变量，根据它是左值还是右值来做不同的处理
    for (lbl, block) in cfg.blocks_mut() {
        let final_invariant = final_invariants
            .get(lbl)
            .unwrap_or_else(|| panic!("ICE no liveness states for {}", lbl));
        let command_states = per_command_states.get(lbl).unwrap();
        last_usage::block(
            compilation_env,
            locals,
            final_invariant,
            command_states,
            block,
        )
    }
    println!("\n!!!!!! liveness::last_usage end !!!!!!\n\n");
}

mod last_usage {
    use crate::{
        cfgir::liveness::state::LivenessState,
        diag,
        hlir::{
            ast::*,
            translate::{display_var, DisplayVar},
        },
        parser::ast::{Ability_, Var},
        shared::{unique_map::*, *},
    };
    use std::collections::{BTreeSet, VecDeque};
    use crate::shared::ast_debug::display;

    struct Context<'a, 'b> {
        env: &'a mut CompilationEnv,
        locals: &'a UniqueMap<Var, SingleType>,
        next_live: &'b BTreeSet<Var>,
        dropped_live: BTreeSet<Var>,
    }

    impl<'a, 'b> Context<'a, 'b> {
        fn new(
            env: &'a mut CompilationEnv,
            locals: &'a UniqueMap<Var, SingleType>,
            next_live: &'b BTreeSet<Var>,
            dropped_live: BTreeSet<Var>,
        ) -> Self {
            Context {
                env,
                locals,
                next_live,
                dropped_live,
            }
        }

        fn has_drop(&self, local: &Var) -> bool {
            let ty = self.locals.get(local).unwrap();
            ty.value.abilities(ty.loc).has_ability_(Ability_::Drop)
        }
    }

    pub fn block(
        compilation_env: &mut CompilationEnv,
        locals: &UniqueMap<Var, SingleType>,
        final_invariant: &LivenessState,
        command_states: &VecDeque<LivenessState>,
        block: &mut BasicBlock,
    ) {
        let len = block.len();
        let last_cmd = block.get(len - 1).unwrap();
        assert!(
            last_cmd.value.is_terminal(),
            "ICE malformed block. missing jump"
        );
        for idx in 0..len {
            let cmd = block.get_mut(idx).unwrap();
            // 取当前命令执行时，当前基本块的活跃变量列表
            let cur_data = &command_states.get(idx).unwrap().0;
            // 取下一条命令执行时，当前基本块的活跃变量列表
            // 如果下一条命令不存在，就取当前基本块全部指令执行之后的活跃变量列表
            // 用来检查如果某个变量 var
            // 在左值中如果在 next_data 中检测不到它了，说明它不再使用
            // 就需要提示使用 _ = var 销毁它
            // 原理是当 let a = 123; 被定义时，使用逆向数据流可以分析出 a 到 某个 p 点被使用的路径
            // a 刚被定义，如果 let a 后面的语句使用了 a，那么在使用路径中每个点都能查到 a
            // 查不到说明 a 不再被使用，原来的 a 被设置为 Ignore
            // 这是活跃变量分析在删除无用赋值的一种变换使用
            let next_data = match command_states.get(idx + 1) {
                Some(s) => &s.0,
                None => &final_invariant.0,
            };

            // 当前指令和下一条指令执行时的基本块状态的区别内容
            // 说明哪些变量被丢弃了
            // 用来检查如果指令是 Copy(var)
            // 检测到 var 被丢弃了，就可以把 Copy 转换为 Move 指令
            // 比如有:
            // cur_data: {Var("a"), Var("s0")}
            // next_data: {Var("a"), Var("s0")}
            // 那么 dropped_live 就是空
            // 如果有:
            // cur_data: {Var("a"), Var("s0")}
            // next_data: {Var("a"), Var("s2")}
            // 那么 dropped_live 就是 s0
            // 如果恰巧这条是 Copy 命令，就把 Copy 转换为 Move
            // 也就是说提前知道某个变量不再被使用了
            let dropped_live = cur_data
                .difference(next_data)
                .cloned()
                .collect::<BTreeSet<_>>();

            // 在左值中提示一个变量下面的代码中没有使用：是假设下个状态中 "存在" 这个变量，如果不存在就报错。
            // 把右边值中，把 Copy 转换为 Move，是假设下个状态中这个变量已经 "消失"
            // 但是其实也可以通过查询 next_data 来判断某个右值变量是否 "存在"，不存在则认为 "消失"？
            // 因为 dropped_live 其实是将当前和下个状态做了一个交集，查询哪些变量消失了。
            // 这么做的原因，可能是因为要提前传入一个 dropped_live 集合
            // 用于在左值声明是插入到 dropped_live 集合，有借用和move时，从这个集合删除。
            // 但是目前看起来这样的做法没有必要？因为每次命令执行，都是全新的 dropped_live 集合，并没有累积上次的结果。
            // 而且也不可能存在一个命令中声明左值，然后立刻操作它的这种语句。从语法上就不存在？

            print!("\n33333333333 cmd: {:?}\ncur_data: {:?}\nnext_data: {:?}\ndropped_live{:?}\n\n",
                   display(cmd), cur_data, next_data, dropped_live);

            command(
                &mut Context::new(compilation_env, locals, next_data, dropped_live),
                cmd,
            )
        }
    }

    fn command(context: &mut Context, sp!(_, cmd_): &mut Command) {
        use Command_ as C;
        match cmd_ {
            C::Assign(ls, e) => {
                lvalues(context, ls);
                exp(context, e);
            },
            C::Mutate(el, er) => {
                exp(context, el);
                exp(context, er)
            },
            C::Return { exp: e, .. }
            | C::Abort(e)
            | C::IgnoreAndPop { exp: e, .. }
            | C::JumpIf { cond: e, .. } => exp(context, e),

            C::Jump { .. } => (),
            C::Break | C::Continue => panic!("ICE break/continue not translated to jumps"),
        }
    }

    fn lvalues(context: &mut Context, ls: &mut [LValue]) {
        ls.iter_mut().for_each(|l| lvalue(context, l))
    }

    fn lvalue(context: &mut Context, l: &mut LValue) {
        use LValue_ as L;
        match &mut l.value {
            L::Ignore => (),
            L::Var(v, _) => {
                context.dropped_live.insert(*v);
                print!("\n        4444444444 lvalue\n        dropped_live: {:?}\n        next_live: {:?}\n        v: {:?}\n\n\n",
                       context.dropped_live, context.next_live, v);
                if !context.next_live.contains(v) {
                    match display_var(v.value()) {
                        DisplayVar::Tmp => (),
                        DisplayVar::Orig(v_str) => {
                            if !v.starts_with_underscore() {
                                print!("\n        4444444444.11111111111111 lvalue\n        dropped_live: {:?}\n        next_live: {:?}\n        v: {:?}\n\n\n",
                                       context.dropped_live, context.next_live, v);
                                let msg = format!(
                                    "Unused assignment or binding for local '{}'. Consider \
                                     removing, replacing with '_', or prefixing with '_' (e.g., \
                                     '_{}')",
                                    v_str, v_str
                                );
                                context
                                    .env
                                    .add_diag(diag!(UnusedItem::Assignment, (l.loc, msg)));
                            }
                            if context.has_drop(v) {
                                l.value = L::Ignore
                            }
                        },
                    }
                }
            },
            L::Unpack(_, _, fields) => fields.iter_mut().for_each(|(_, l)| lvalue(context, l)),
        }
    }

    fn exp(context: &mut Context, parent_e: &mut Exp) {
        use UnannotatedExp_ as E;
        match &mut parent_e.exp.value {
            E::Unit { .. } | E::Value(_) | E::Constant(_) | E::UnresolvedError => (),

            E::BorrowLocal(_, var) | E::Move { var, .. } => {
                // remove it from context to prevent accidental dropping in previous usages
                // 从上下文中移除它，以防止在先前的使用中意外丢弃
                println!("        E::BorrowLocal E::Move 5555555555.0000000000 exp dropped_live.remove({:?})\n\n", var);
                context.dropped_live.remove(var);
            },

            E::Spec(anchor) => {
                // remove it from context to prevent accidental dropping in previous usages
                anchor.used_locals.values().for_each(|(_, var)| {
                    context.dropped_live.remove(var);
                })
            },

            E::Copy { var, from_user } => {
                // Even if not switched to a move:
                // remove it from dropped_live to prevent accidental dropping in previous usages
                // 在变量 let 定义中插入 context.dropped_live.insert(*v);
                // 如果是
                let var_is_dead = context.dropped_live.remove(var);
                println!("\n\n        E::Copy 5555555555.1111111111111 dropped_live.remove({:?})", var);
                // Non-references might still be borrowed, but that error will be caught in borrow
                // checking with a specific tip/message
                if var_is_dead && !*from_user {
                    println!("        5555555555.222222222222222 E::Copy var_is_dead {:?}, from_user {:?}", var_is_dead, from_user);
                    parent_e.exp.value = E::Move {
                        var: *var,
                        annotation: MoveOpAnnotation::InferredLastUsage,
                    }
                }
            },

            E::ModuleCall(mcall) => exp(context, &mut mcall.arguments),
            E::Builtin(_, e)
            | E::Vector(_, _, _, e)
            | E::Freeze(e)
            | E::Dereference(e)
            | E::UnaryExp(_, e)
            | E::Borrow(_, e, _)
            | E::Cast(e, _) => exp(context, e),

            E::BinopExp(e1, _, e2) => {
                exp(context, e2);
                exp(context, e1)
            },

            E::Pack(_, _, fields) => fields
                .iter_mut()
                .rev()
                .for_each(|(_, _, e)| exp(context, e)),

            E::ExpList(es) => es
                .iter_mut()
                .rev()
                .for_each(|item| exp_list_item(context, item)),

            E::Unreachable => panic!("ICE should not analyze dead code"),
        }
    }

    fn exp_list_item(context: &mut Context, item: &mut ExpListItem) {
        match item {
            ExpListItem::Single(e, _) | ExpListItem::Splat(_, e, _) => exp(context, e),
        }
    }
}

//**************************************************************************************************
// Refs Refinement
//**************************************************************************************************

/// This refinement releases dead reference values by adding a move + pop. In other words, if a
/// reference `r` is dead, it will insert `_ = move r` after the last usage
///
/// However, due to the previous `last_usage` analysis. Any last usage of a reference is a move.
/// And any unused assignment to a reference holding local is switched to a `Ignore`.
/// Thus the only way a reference could still be dead is if it was live in a loop
/// Additionally, the borrow checker will consider any reference to be released if it was released
/// in any predecessor.
/// As such, the only references that need to be released by an added `_ = move r` are references
/// at the beginning of a block given that
/// (1) The reference is live in the predecessor and the predecessor is a loop
/// (2)  The reference is live in ALL predecessors (otherwise the borrow checker will release them)
///
/// Because of this, `build_forward_intersections` intersects all of the forward post states of
/// predecessors.
/// Then `release_dead_refs_block` adds a release at the beginning of the block if the reference
/// satisfies (1) and (2)

pub fn release_dead_refs(
    locals_pre_states: &BTreeMap<Label, locals::state::LocalStates>,
    locals: &UniqueMap<Var, SingleType>,
    cfg: &mut BlockCFG,
    infinite_loop_starts: &BTreeSet<Label>,
) {
    println!("\n\n!!!!!! liveness::release_dead_refs start !!!!!!");
    // 每个基本块的出口的活跃变量
    let (liveness_pre_states, _per_command_states) = analyze(cfg, infinite_loop_starts);
    // 基于每个基本块的出口的活跃变量，取得每个基本块的所有前驱的状态的交集
    let forward_intersections = build_forward_intersections(cfg, &liveness_pre_states);
    println!("aaaaaaaaaaaaa forward_intersections");
    for (k, v) in forward_intersections.iter() {
        print!("    Label: {:?} -> ", k);
        for var in v.iter() {
            print!("{:?} ", var);
        }
        println!("");
    }
    // 基本块的前驱基本块中的可用变量集合
    println!("\nbbbbbbbbbbb locals_pre_states");
    for (k, v) in locals_pre_states.iter() {
        print!("Label: {:?} -> \n", k);
        for (var, local_state) in v.iter() {
            print!("    {:?} -> {:?}\n", var, state_to_str(local_state));
        }
        println!("");
    }
    for (lbl, block) in cfg.blocks_mut() {
        let locals_pre_state = locals_pre_states.get(lbl).unwrap();
        let liveness_pre_state = liveness_pre_states.get(lbl).unwrap();
        let forward_intersection = forward_intersections.get(lbl).unwrap();
        release_dead_refs_block(
            locals,
            locals_pre_state,
            liveness_pre_state,
            forward_intersection,
            block,
            lbl,
        )
    }
    println!("\n!!!!!! liveness::release_dead_refs end !!!!!!\n\n");
}

fn state_to_str(state: &LocalState) -> String {
    match state {
        LocalState::Unavailable(_, _) => "Unavailable".to_string(),
        LocalState::Available(_) => "Available".to_string(),
        LocalState::MaybeUnavailable { .. } => "MaybeUnavailable".to_string(),
    }
}

/*
每个基本块的所有前驱的状态的交集
 */
fn build_forward_intersections(
    cfg: &BlockCFG,
    final_invariants: &FinalInvariants,
) -> ForwardIntersections {
    cfg.blocks()
        .keys()
        .map(|lbl| {
            // 取得这个 block 的前驱，然后获取所有前驱基本块的 OUT 状态
            let mut states = cfg
                .predecessors(*lbl)
                .iter()
                .map(|pred| &final_invariants.get(pred).unwrap().0);
            println!("build_forward_intersections {:?} states {:?}", lbl, states);
            let intersection = states
                .next() // 当前基本块的第一个前驱
                .map(|init| {   // 的状态
                    println!("init {:?}", init);
                    // 以第一个前驱的状态作为第一个值
                    // 将剩下的前驱的状态做 and 运算
                    // BTreeSet 类型做 and 运算就是求交集
                    states.clone().fold(init.clone(), |acc, s| {
                        println!("acc {:?} s {:?} -> acc & s {:?}", acc, s, &acc & s);
                        &acc & s
                    })
                })
                .unwrap_or_else(BTreeSet::new);
            println!("build_forward_intersections intersection {:?}\n", intersection);
            (*lbl, intersection)
        })
        .collect()
}

fn release_dead_refs_block(
    locals: &UniqueMap<Var, SingleType>,
    locals_pre_state: &locals::state::LocalStates,
    liveness_pre_state: &LivenessState,
    forward_intersection: &BTreeSet<Var>,
    block: &mut BasicBlock,
    lbl: &Label,
) {
    if forward_intersection.is_empty() {
        return;
    }

    let cmd_loc = block.get(0).unwrap().loc;
    let cur_state = {
        let mut s = liveness_pre_state.clone();
        for cmd in block.iter().rev() {
            command(&mut s, cmd);
        }
        s
    };
    println!("ccccccccccc cur_state");
    print!("Label {:?} -> ", lbl);
    for var in cur_state.0.iter() {
        print!(" {:?}", var);
    }
    print!("\n\n");
    // Free references that were live in ALL predecessors and that have a value
    // (could not have a value due to errors)
    // 当前基本块的所有前驱的状态交集后的值集
    // 和当前状态的差异内容
    // 并且在当前基本块的可用变量列表中是可用变量
    // 并且存在于局部变量列表中
    // 并且是引用
    // 需要在当前基本块的开始，插入对这些引用变量的释放
    // 也就是说，这些变量在当前基本块不活跃了
    // 但是在所有前驱中都活跃
    // 而且有一个值（在当前基本块的入口处，也是前驱基本块的出口处，是可用的，即在当前基本块的 IN 值集中)
    // 而且是一个引用类型的值
    // 问题：
    // 1. 分析 locals_pre_state 获取每个基本块的 IN 值集合的过程
    // 简单看了一下，是正常的正向数据流分析过程，得到就是 IN 值集的过程
    let dead_refs = forward_intersection
        .difference(&cur_state.0)
        .filter(|var| locals_pre_state.get_state(var).is_available())
        .map(|var| (var, locals.get(var).unwrap()))
        .filter(is_ref);
    // i 和 ss2 都是需要释放的，但是只有 ss2 是引用
    println!("\nbefore <push pop_ref> {:?}", lbl);
    for cmd in block.iter() {
        println!("{:?}", display(cmd));
    }
    println!("");
    for (dead_ref, ty) in dead_refs {
        println!("dddddddddddd dead_ref {:?} type {:?}", dead_ref, ty);
        block.push_front(pop_ref(cmd_loc, *dead_ref, ty.clone()));
    }
    println!("");
    println!("after <push pop_ref> {:?}", lbl);
    for cmd in block.iter() {
        println!("{:?}", display(cmd));
    }
    println!("");
}

fn is_ref((_local, sp!(_, local_ty_)): &(&Var, &SingleType)) -> bool {
    match local_ty_ {
        SingleType_::Ref(_, _) => true,
        SingleType_::Base(_) => false,
    }
}

fn pop_ref(loc: Loc, var: Var, ty: SingleType) -> Command {
    use Command_ as C;
    use UnannotatedExp_ as E;
    let move_e_ = E::Move {
        annotation: MoveOpAnnotation::InferredLastUsage,
        var,
    };
    let move_e = H::exp(Type_::single(ty), sp(loc, move_e_));
    let pop_ = C::IgnoreAndPop {
        pop_num: 1,
        exp: move_e,
    };
    sp(loc, pop_)
}
