import random
import time

from utils import *
from main import check_satis, log_run_info

MUT_APPLY_TIME_LIMIT = 10
trans_n = 0


class MutType(Enum):
    ID = 1

    """And(a, b) -> And(b, a)"""
    SWAP_AND = 2
    """And(a, b) -> And(a, b, a)"""
    DUP_AND = 3
    """
    And(a, b, c) -> And(a, And(b, c))
    And(a, b) -> And(a, And(a, b))
    """
    BREAK_AND = 4
    SWAP_OR = 5
    DUP_OR = 6
    BREAK_OR = 7

    MIX_BOUND_VARS = 8
    UNION = 9


class Mutation(object):

    def __init__(self, prev_mutation):
        self.type = MutType.ID
        self.number = prev_mutation.number + 1 if prev_mutation else 0
        self.path = []
        self.snd_inst = None
        self.prev_mutation = prev_mutation
        self.kind_ind = 0

    def clear(self):
        self.type = MutType.ID
        self.path.clear()
        self.number = 0
        self.snd_inst = None
        self.prev_mutation = None

    def apply(self, instance):
        """Return mutated instances."""
        self.next_mutation(instance.info)
        if self.type == MutType.ID:
            mut_instance = instance

        elif self.type in {MutType.SWAP_AND, MutType.SWAP_OR,
                           MutType.DUP_AND, MutType.DUP_OR,
                           MutType.BREAK_AND, MutType.BREAK_OR,
                           MutType.MIX_BOUND_VARS}:
            mut_instance = self.transform_rand(instance)

        elif self.type == MutType.UNION:
            mut_instance = self.unite(instance)

        else:
            assert False
        return mut_instance

    def next_mutation(self, info):
        """
        Return the next mutation based on the instance,
        type of the previous mutation etc.
        """
        if self.snd_inst:
            self.type = MutType.UNION
        else:
            if info.expr_exists[Z3_OP_AND] and info.expr_exists[Z3_OP_OR]:
                value = random.randrange(2, 8)
            elif info.expr_exists[Z3_OP_AND]:
                value = random.randrange(2, 5)
            elif info.expr_exists[Z3_OP_OR]:
                value = random.randrange(5, 8)
            else:
                value = 1
            if info.expr_exists[Z3_QUANTIFIER_AST]:
                value = random.choice([value, 8]) if value > 1 else 8

            if value == 8:
                self.kind_ind = 2
            elif value > 4:
                self.kind_ind = 1
            self.type = MutType(value)

    def unite(self, fst_inst):
        """Unite formulas of two independent instances."""
        fst_group = fst_inst.get_group()
        snd_group = self.snd_inst.get_group()
        fst_group.uninter_pred = \
            fst_group.uninter_pred.union(snd_group.uninter_pred)
        fst_group.bound_vars = \
            fst_group.bound_vars.union(snd_group.bound_vars)
        fst_inst.info += self.snd_inst.info

        new_instance = AstVector()
        for clause in fst_inst.chc:
            new_instance.push(clause)
        for clause in self.snd_inst.chc:
            new_instance.push(clause)
        return new_instance

    def transform_rand(self, instance):
        """Transform random and/or-expression."""
        global trans_n
        info = instance.info
        chc = instance.chc
        mut_instance = AstVector()
        kind = info_kinds[self.kind_ind]

        ind = np.where(info.expr_num[self.kind_ind] != 0)[0]
        i = int(random.choice(ind))
        if self.type in {MutType.BREAK_AND, MutType.BREAK_OR}:
            info.expr_num[self.kind_ind][i] += 1
        clause = chc[i]
        num = info.expr_num[self.kind_ind][i]
        trans_n = random.randint(1, num)
        self.path = [i]
        mut_clause = self.transform_nth(clause, kind, time.perf_counter(), [i])
        for j, clause in enumerate(chc):
            if j == i:
                mut_instance.push(mut_clause)
            else:
                mut_instance.push(chc[j])
        return mut_instance

    def transform_nth(self, expr, expr_kind, st_time, path):
        """Transform nth and/or-expression in dfs-order."""
        global trans_n
        if time.perf_counter() - st_time >= MUT_APPLY_TIME_LIMIT:
            raise TimeoutError('Timeout of applying mutation')
        if not len(expr.children()):
            return expr
        mut_children = []
        for i, child in enumerate(expr.children()):
            new_path = path + [i]
            mut_children.append(self.transform_nth(child, expr_kind, st_time, new_path))
        is_and_expr = expr_kind == Z3_OP_AND and is_and(expr)
        is_or_expr = expr_kind == Z3_OP_OR and is_or(expr)
        is_quant_expr = expr_kind == Z3_QUANTIFIER_AST and is_quantifier(expr)
        if is_and_expr or is_or_expr or is_quant_expr:
            trans_n -= 1
            if trans_n == 0:
                if self.type in {MutType.SWAP_AND, MutType.SWAP_OR}:
                    mut_children = mut_children[1:] + mut_children[:1]
                elif self.type in {MutType.DUP_AND, MutType.DUP_OR}:
                    mut_children.append(mut_children[0])
                elif self.type in {MutType.BREAK_AND, MutType.BREAK_OR}:
                    if len(mut_children) == 2:
                        mut_children.pop()
                        mut_children.append(expr)
                    else:
                        subchildren = mut_children[-2:]
                        mut_children = mut_children[:-2]
                        if is_and_expr:
                            mut_children.append(And(subchildren))
                        else:
                            mut_children.append(Or(subchildren))
                if is_and_expr:
                    mut_expr = And(mut_children)
                elif is_or_expr:
                    mut_expr = Or(mut_children)
                else:
                    vars = get_bound_vars(expr)
                    random.shuffle(vars)
                    mut_expr = update_expr(expr, mut_children, vars)
                self.path = path
                return mut_expr
        return update_expr(expr, mut_children)

    # def undo(self, instances, ind, last_instance):
    #     """Undo the mutation and return the resulting instance."""
    #     global trans_n
    #     new_inst = deepcopy(last_instance)
    #     for i in reversed(ind):
    #         # TODO -- for union
    #         path = self.paths[i]
    #         cur_clause_ind = path[0]
    #         cur_clause = instances[i].chc[cur_clause_ind]
    #         last_inst_clause = last_instance.chc[cur_clause_ind]
    #         changed_clause = rec_undo(path[1:], cur_clause, last_inst_clause) \
    #             if len(path) > 1 else cur_clause
    #
    #         new_inst.chc = AstVector()
    #         for j, clause in enumerate(last_instance.chc):
    #             if j == i:
    #                 new_inst.chc.push(changed_clause)
    #             else:
    #                 new_inst.chc.push(last_instance.chc[j])
    #     return new_inst
    #
    # def reduce(self, instances, last_instance):
    #     """
    #     Search for a reduced version of mutation chain that is
    #     the minimal set of bug-triggering transformations.
    #     """
    #     chunk_size = self.number // 2
    #     seed = instances[0]
    #     while chunk_size:
    #         for i in range(self.number - 1, 0, -chunk_size):
    #             length = len(instances)
    #             from_ind = max(i - chunk_size + 1, 1)
    #             ind_chunk = range(from_ind, i + 1)
    #             new_instance = self.undo(instances, ind_chunk, last_instance)
    #             try:
    #                 res = check_equ(seed, new_instance)
    #             except AssertionError as err:
    #                 group = seed.get_group()
    #                 log_run_info(group.filename,
    #                              'reduce_problem',
    #                              repr(err),
    #                              None,
    #                              group, new_instance)
    #                 continue
    #             if not res and length > chunk_size:
    #                 self.cut_out(from_ind, i)
    #                 for j in range(from_ind, length):
    #                     if j < length - chunk_size:
    #                         instances[j] = instances[j + chunk_size]
    #                     else:
    #                         instances.pop(j)
    #                 last_instance.chc = new_instance.chc
    #         chunk_size //= 2

    def get_chain(self):
        """Return the full mutation chain."""
        chain = self.type.name
        cur_mutation = self
        for i in range(self.number, 0, -1):
            cur_mutation = cur_mutation.prev_mutation
            chain = cur_mutation.type.name + '->' + chain
        return chain

    def debug_print(self, instance: AstVector, mut_instance: AstVector):
        print(instance[self.path[0]], '\n->\n', mut_instance[self.path[0]])


def rec_undo(path, cur_expr, target_expr):
    """Undo the mutation with recursive descent along mutation's path."""

    child_ind = path[0]
    cur_child = cur_expr.children()[child_ind]
    target_children = target_expr.children()
    new_children = []
    if len(path) > 1:
        undo_child = rec_undo(path[1:], cur_child, target_children[child_ind])
    else:
        undo_child = cur_child
    for i, child in enumerate(target_children):
        if i == child_ind:
            new_children.append(undo_child)
        else:
            new_children.append(child)
    return update_expr(target_expr, new_children)
