from mutations import *
import sys
import time
import logging

time_limit = int(2 * 1e3)
logging.basicConfig(format='%(message)s', filename='logfile', level=logging.INFO)


class Example(object):

    def __init__(self, filename, chc, mut, time):
        self.filename = filename
        self.chc = chc
        self.satis = unknown
        self.mutation = mut
        self.time = time


def get_seed(argv):
    """Return the parsed seeds given by files in smt2-format"""

    seeds = [
        z3.parse_smt2_file(seed)
        for seed in argv
    ]
    return seeds


def check_equ(example, mut_example):
    """Return True if the test suites have the same satisfiability and False otherwise"""

    solver = SolverFor('HORN')
    solver.set('engine', 'spacer')
    solver.set('timeout', time_limit)

    mut = example.mutation
    if mut.number == 1:
        st_time = time.perf_counter()
        solver.add(example.chc)
        example.satis = solver.check()
        solver.reset()
        example.time.append(time.perf_counter() - st_time)
        assert example.satis != unknown, solver.reason_unknown()
        logging.info("%s %s %s %s",
                     'Seed:',
                     str(example.satis) + ',',
                     'time(sec):', example.time[0])

    mut_st_time = time.perf_counter()
    solver.add(mut_example.chc)
    mut_example.satis = solver.check()
    mut_example.time.append(time.perf_counter() - mut_st_time)
    assert mut_example.satis != unknown, solver.reason_unknown()

    logging.info("%s %s %s %s",
                 'Mutant #' + str(mut.number) + ' (' + str(mut.cur_type().name) + '):',
                 str(mut_example.satis) + ',',
                 'time(sec):', mut_example.time[-1])
    return example.satis == mut_example.satis


def main(argv):
    # help_simplify()
    seed_num = len(argv)
    assert seed_num > 0, 'Seeds not found'
    enable_trace("spacer")
    seeds = get_seed(argv)

    queue = []
    for i, seed in enumerate(seeds):
        example = Example(argv[i], seed, Mutation(), [])
        queue.append(example)
    used = []

    while True and queue:
        cur_example = queue.pop(0)
        used.append(cur_example)
        cur_name = cur_example.filename
        print(cur_name)
        logging.info(cur_name)
        mut = cur_example.mutation
        mut_chc = mut.apply(cur_example.chc)
        mut_example = Example(cur_name, mut_chc, mut, cur_example.time)
        res = True
        try:
            res = check_equ(cur_example, mut_example)
        except AssertionError as err:
            if err == 'timeout' or cur_example.satis == unknown:
                print(repr(err))
                logging.info(repr(err))
                if cur_example.satis != unknown:
                    logging.info("%s %s\n%s %s",
                                 'Seed\'s time(sec):',
                                 mut_example.time[0],
                                 'Mutant\'s time(sec):',
                                 mut_example.time[-1])
            else:
                print('Problem --', repr(err))
                logging.error("%s -- %s",
                              'Problem',
                              repr(err))

        if not res:
            chain = mut.get_chain()
            print('Problem in this chain of mutations:\n', chain)
            logging.error("%s\n%s",
                          'Problem in this chain of mutations:',
                          chain)
            problem_id = mut.trans_clause_id
            logging.error("%s\n->\n%s",
                          cur_example.chc[problem_id].sexpr(),
                          mut_example.chc[problem_id].sexpr())
        elif mut_example.satis != unknown:
            queue.append(mut_example)
            logging.info('No problems found')
        print()
        logging.info('\n')


if __name__ == '__main__':
    main(sys.argv[1:])
