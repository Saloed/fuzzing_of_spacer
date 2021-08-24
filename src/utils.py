from z3 import *
from collections import defaultdict
from scipy.sparse import dok_matrix
import numpy as np


TRACE_FILE = '.z3-trace'

trace_states = defaultdict(int)
trans_offset = 0
start_state = 0


class ClauseInfo(object):

    def __init__(self, number):
        self.expr_exists = defaultdict(bool)
        self.expr_num = np.zeros((3, number), dtype=int)
        self.got = False

    def __add__(self, other):
        sum = ClauseInfo(1)
        for key in self.expr_exists:
            sum.expr_exists[key] = self.expr_exists[key] | other.expr_exists[key]
        sum.expr_num = np.concatenate((self.expr_num, other.expr_num), axis=1)
        sum.got = self.got | other.got
        return sum


class TransMatrix(object):

    def __init__(self):
        self.matrix = dok_matrix((1, 1), dtype=int)
        self.sum_num = 0
        self.states_num = defaultdict(int)

    def __add__(self, other):
        """Return the sum of two transition matrices."""
        sum = TransMatrix()
        size = len(trace_states)
        shape = (size, size)
        self.matrix.resize(shape)
        other.matrix.resize(shape)
        sum.matrix = self.matrix
        sum.matrix += other.matrix
        sum.sum_num += 1
        return sum

    def __eq__(self, other):
        comparison = self.matrix != other.matrix
        res = comparison if isinstance(comparison, bool) \
            else comparison.data.any()
        return not res

    def __hash__(self):
        return hash(str(self.matrix))

    def add_trans(self, i, j):
        """Add transition to matrix."""
        global trace_states
        i_ind = trace_states[i]
        j_ind = trace_states[j]
        self.matrix[i_ind, j_ind] += 1

    def read_from_trace(self):
        """Read z3-trace from last read line."""
        global trans_offset, start_state
        trace = open(TRACE_FILE, 'r')
        trace.seek(trans_offset)
        lines = trace.readlines()
        states = [state.rstrip() for state in lines]
        if not start_state:
            start_state = states[0]
        for state in states:
            if state not in trace_states:
                trace_states[state] = len(trace_states)
        size = len(trace_states)
        self.matrix = dok_matrix((size, size), dtype=int)

        state = states[0]
        for next_state in states[1:]:
            self.add_trans(state, next_state)
            state = next_state
        trans_offset = trace.tell()
        trace.close()

    def get_probability_matrix(self):
        """Return the transition matrix in probabilistic form."""
        prob_matrix = dok_matrix(self.matrix.shape, dtype=float)
        trans_num = self.matrix.sum(axis=1)
        not_zero_ind = [tuple(item)
                        for item in np.transpose(self.matrix.nonzero())]
        for i, j in not_zero_ind:
            prob_matrix[i, j] = self.matrix[i, j] / trans_num[i]
        return prob_matrix

    def count_states(self):
        """Return the number of states in z3-trace."""

        sum_matrix = self.matrix.sum(axis=0)
        for state in trace_states:
            ind = trace_states[state]
            self.states_num[state] = sum_matrix[0, ind]
        for _ in range(self.sum_num):
            self.states_num[start_state] += 1


def get_weight_matrix(prob_matrix):
    """
    Return the matrix whose values are reverse to the
    values of the probability matrix.
    """

    weight_matrix = dok_matrix(prob_matrix.shape, dtype=float)
    not_zero_ind = [tuple(item)
                    for item in np.transpose(prob_matrix.nonzero())]
    for i in not_zero_ind:
        weight_matrix[i] = 1 / prob_matrix[i]
    return weight_matrix


def get_bound_vars(expr):
    """Return bound variables."""

    vars = []
    if is_not(expr):
        expr = expr.children()[0]
    assert expr.is_forall() or expr.is_exists(), \
        'А quantifier-free expression is given'
    for i in range(expr.num_vars()):
        name = expr.var_name(i)
        sort = expr.var_sort(i)
        var = Const(name, sort)
        vars.append(var)
    return vars


def update_expr(expr, children, vars=None):
    """Return the expression with new children."""

    upd_expr = expr
    old_children = upd_expr.children()
    while len(children) > len(old_children):
        old_children.append(children[0])
    if not is_quantifier(expr):
        for i in range(len(children)):
            upd_expr = substitute(upd_expr, (old_children[i], children[i]))
    else:
        if vars is None:
            vars = get_bound_vars(expr)
        if expr.is_forall():
            upd_expr = ForAll(vars, children[0])
        else:
            upd_expr = Exists(vars, children[0])
    return upd_expr


def expr_exists(instance, kind):
    """Return if there is a subexpression of the specific kind."""

    length = len(instance) if isinstance(instance, AstVector) else 1
    for i in range(length):
        expr = instance[i] if isinstance(instance, AstVector) else instance
        expr_set = {expr}
        while len(expr_set):
            cur_expr = expr_set.pop()
            ctx_ref = cur_expr.ctx.ref()
            ast = cur_expr.as_ast()
            if Z3_get_ast_kind(ctx_ref, ast) == kind:
                return True
            elif not is_var(expr) and not is_const(expr):
                if is_app(cur_expr) and cur_expr.decl().kind() == kind:
                    return True
                for child in cur_expr.children():
                    expr_set.add(child)
    return False


def count_expr(instance, kind, is_unique=False):
    """Return the number of subexpressions of the specific kind."""

    if is_unique:
        unique_expr = set()
    else:
        expr_num = 0
    length = len(instance) if isinstance(instance, AstVector) else 1
    for i in range(length):
        expr = instance[i] if isinstance(instance, AstVector) else instance
        expr_set = {expr}
        while len(expr_set):
            cur_expr = expr_set.pop()
            ctx_ref = cur_expr.ctx.ref()
            ast = cur_expr.as_ast()
            if Z3_get_ast_kind(ctx_ref, ast) == kind:
                expr_num += 1
                for child in cur_expr.children():
                    expr_set.add(child)
            elif not is_var(expr) and not is_const(expr):
                if is_app(cur_expr) and cur_expr.decl().kind() == kind:
                    if is_unique:
                        unique_expr.add(cur_expr.decl())
                    else:
                        expr_num += 1
                for child in cur_expr.children():
                    expr_set.add(child)
    if is_unique:
        return len(unique_expr), unique_expr
    else:
        return expr_num
