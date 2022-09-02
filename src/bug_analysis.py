import argparse
import os.path

from typing import Tuple

import instances
import log_analysis
import csv

from main import check_satis
from instances import *
from seeds import get_filenames
import tqdm

sys.setrecursionlimit(1000)

all_params = []

DEFAULT_FALSE_PARAMS = {
    'SPACER.P3.SHARE_INVARIANTS',
    'SPACER.P3.SHARE_LEMMAS',
    # 'SPACER.PUSH_POB', -- takes a long time
    'SPACER.USE_LIM_NUM_GEN',
    'SPACER.RESET_POB_QUEUE',
    'SPACER.SIMPLIFY_LEMMAS_POST',
    'SPACER.SIMPLIFY_LEMMAS_PRE',
    'SPACER.SIMPLIFY_POB',
    'SPACER.USE_BG_INVS',
    'SPACER.USE_EUF_GEN',
    'SPACER.USE_LEMMA_AS_CTI',
    'XFORM.ARRAY_BLAST_FULL',
    'XFORM.COALESCE_RULES',
    'XFORM.ELIM_TERM_ITE',
    # 'XFORM.FIX_UNBOUND_VARS', -- often causes unknown
    'XFORM.INLINE_LINEAR_BRANCH',
    'XFORM.INSTANTIATE_ARRAYS',
    'XFORM.INSTANTIATE_ARRAYS.ENFORCE',
    'XFORM.INSTANTIATE_QUANTIFIERS',
    # 'XFORM.MAGIC', -- often causes unknown
    # 'XFORM.SCALE', -- often causes unknown
    'XFORM.QUANTIFY_ARRAYS',
    'XFORM.TRANSFORM_ARRAYS'
}

DEFAULT_TRUE_PARAMS = {
    'SPACER.CTP',
    'SPACER.ELIM_AUX',
    'SPACER.EQ_PROP',
    'SPACER.GROUND_POBS',
    'SPACER.KEEP_PROXY',
    'SPACER.MBQI',
    'SPACER.PROPAGATE',
    'SPACER.REACH_DNF',
    'SPACER.USE_ARRAY_EQ_GENERALIZER',
    'SPACER.USE_DERIVATIONS',
    'SPACER.USE_INC_CLAUSE',
    'SPACER.USE_INDUCTIVE_GENERALIZER',
    'XFORM.COI',
    'XFORM.COMPRESS_UNBOUND',
    'XFORM.INLINE_EAGER',
    'XFORM.INLINE_LINEAR',
    'XFORM.SLICE',
    'XFORM.TAIL_SIMPLIFIER_PVE'
}

INT_PARAMS = {
    'SPACER.ORDER_CHILDREN': 0,
    'SPACER.RANDOM_SEED': 0
}

ALL_PARAMS = DEFAULT_FALSE_PARAMS | DEFAULT_TRUE_PARAMS | INT_PARAMS.keys()


def is_same_res(instance: Instance, result: bool = False, message: str = None) -> bool:
    """
    Return True if solving an instance returns
    the expected result and False otherwise.
    """

    try:
        same_res = result == check_satis(instance, instance.get_group(),
                                         get_stats=False)
        if not result and same_res:
            return True
        instance.check_model()
        if instance.model_info[0] == unsat:
            instance.model_info = (sat, 0)
            return True

        instance.model_info = (sat, 0)
        return False
    except AssertionError as err:
        same_res = repr(err) == message
    return same_res


def reduce_instance(seed: Instance, bug_instance: Instance,
                    message: str = None) -> Tuple[Instance, bool]:
    """Reduce the chc-system causing the problem."""

    print('Instance reducing')
    start_instance = deepcopy(bug_instance)
    instance = deepcopy(bug_instance)

    for i, clause in enumerate(instance.chc):
        print('Clause:', i)
        expr_queue = [clause]
        trans_number = -1
        expr_number = -1

        while len(expr_queue):
            cur_expr = expr_queue.pop()

            trans_number += 1
            expr_number += 1
            mutation = Mutation()
            mutation.set_remove_mutation(trans_number)

            try:
                reduced_chc = mutation.transform(instance)
                instance.set_chc(reduced_chc)
            except Exception:
                # print(traceback.format_exc())
                instance.set_chc(bug_instance.chc)
                for child in cur_expr.children():
                    expr_queue.append(child)
                continue

            is_eq = equivalence_check(seed.chc,
                                      instance.chc)
            if is_same_res(instance, message=message) and is_eq:
                bug_instance.set_chc(instance.chc)
                print('Reduced:', expr_number)
                trans_number -= 1
            else:
                instance.set_chc(bug_instance.chc)
                for child in cur_expr.children():
                    expr_queue.append(child)
                # print('Cannot be reduced:', trans_number)
    is_reduced = start_instance.chc.sexpr() != bug_instance.chc.sexpr()

    return bug_instance, is_reduced


def reduce_mut_chain(group: InstanceGroup, message: str = None) -> Instance:
    """
    Search for a reduced version of mutation chain that is
    the minimal set of bug-triggering transformations.
    """
    initial_size = len(group.instances)
    chunk_size = initial_size // 2

    while chunk_size:
        print(f'\nChunk size: {chunk_size}.')
        for i in range(initial_size - 1, 0, -chunk_size):
            from_ind = max(i - chunk_size + 1, 1)
            ind_chunk = range(from_ind, i + 1)
            try:
                new_group = undo_mutations(group, ind_chunk)
            except Z3Exception:
                continue
            new_instance = new_group[-1]
            if len(group.instances) != len(new_group.instances) and \
                    is_same_res(new_instance, message=message):
                group = new_group
                initial_size -= chunk_size
                print(f'{chunk_size} mutation can be removed.')

            # if chunk_size == 1:
            #     mut_type = group[ind_chunk[0]].mutation.type
            #     if mut_type.is_simplification():
            #         group[ind_chunk[0]] = reduce_simplify(group[ind_chunk[0] - 1], mut_type, message)
        chunk_size //= 2

    instance = group.pop()
    print(instance.mutation.get_chain())
    return instance


def undo_mutations(group: InstanceGroup, ind: range) -> InstanceGroup:
    """Undo the mutations from a given interval."""
    group_len = len(group.instances)
    new_group = InstanceGroup(len(instance_groups), group.filename)
    new_group.copy_info(group)
    for i in range(ind[0]):
        new_group.push(group[i])
        # mut = group[i].mutation
        # if i > 0:
        #     print(i, mut.prev_mutation.get_name(), mut.get_name())

    last_instance = new_group[ind[0] - 1]
    for i in range(ind[-1] + 1, group_len):
        mut_instance = Instance()
        mut_instance.mutation = deepcopy(group[i].mutation)
        mut = mut_instance.mutation
        try:
            mut.apply(last_instance, mut_instance)
        except AssertionError:
            return group
        new_group.push(mut_instance)
        last_instance = mut_instance

    return new_group


def reduce_simplify(instance: Instance, mut_type: str, message: str = None) -> Instance:
    """Reduce the applying of SIMPLIFY"""

    mut_instance = Instance(instance.group_id)
    mut = mut_instance.mutation
    mut.type = mut_type

    mut.path[0] = [i for i in range(len(instance.chc))]
    for i in range(len(instance.chc)):
        mut.path[0].remove(i)
        mut.apply(instance, mut_instance)
        if not is_same_res(mut_instance, message=message):
            mut.path[0].append(i)
        mut_instance.set_chc(instance.chc)
    if mut.path[0] == range(len(instance.chc)):
        mut.path[0] = None

    mut.apply(instance, mut_instance)
    return mut_instance


def reduce_declarations(instance: Instance):
    def get_pred_name(decl: str):
        name = decl.split(' ', 1)[0].rstrip()
        return name[1:-1] if name[0] == '|' else name

    group = instance.get_group()
    filename = group.filename
    decl_path = 'output/decl/' + filename
    with open(decl_path, 'r') as decl_file:
        declarations = decl_file.read()
    predicates = get_predicates(instance.chc)
    decl_chunks = declarations.split('(declare-fun ')
    i = 0
    for chunk in decl_chunks[1:]:
        i += 1
        pred_decl = get_pred_name(chunk)
        str_predicates = {str(item) for item in predicates}
        if pred_decl not in str_predicates:
            decl_chunks.pop(i)
            i -= 1
    new_declarations = '(declare-fun '.join(decl_chunks)
    return new_declarations


def reduce(filename: str = None, reduce_chain: bool = False, reduce_inst: bool = True) -> Instance:
    mutations, message, seed_name = get_bug_info(filename)
    group_id = len(instance_groups)
    group = InstanceGroup(group_id, seed_name)
    if reduce_chain:
        group.restore(group_id, mutations)
        mut_instance = group[-1]
        try:
            assert is_same_res(mut_instance, message=message), \
                'Incorrect mutant-restoration'
        except AssertionError:
            print(traceback.format_exc())
            return None
        mut_instance = reduce_mut_chain(group, message)
    else:
        group.restore(group_id, {})
        mut_system = parse_smt2_file(filename,
                                     ctx=instances.current_ctx)
        mut_instance = Instance(group_id, mut_system)
        for entry in mutations:
            type_name = entry['type']
            type = mut_types[type_name]
            if type.is_solving_param():
                mut_instance.add_param(type)

        assert is_same_res(mut_instance, message=message), \
            'Incorrect mutant-restoration'

    reduce_dir = 'output/reduced/'
    if not os.path.exists(reduce_dir):
        os.mkdir(reduce_dir)
    for dir in {'spacer-benchmarks/', 'chc-comp21-benchmarks/',
                'sv-benchmarks-clauses/'}:
        for subdir in os.walk(dir):
            dir_path = reduce_dir + subdir[0]
            if not os.path.exists(dir_path):
                os.mkdir(dir_path)

    if reduce_inst:
        try:
            is_reduced = True
            while is_reduced:
                mut_instance, is_reduced = reduce_instance(group[0],
                                                           mut_instance,
                                                           message)
                declarations = reduce_declarations(mut_instance) \
                    if not is_reduced else None
                mut_instance.dump('output/reduced',
                                  seed_name,
                                  declarations=declarations,
                                  clear=False)

        except Exception:
            print(traceback.format_exc())

    return mut_instance


def get_bug_info(filename: str):
    with open(filename) as file:
        mut_line = file.readline()
        mut_line = mut_line[2:] if mut_line[0] == ';' else None
        message = file.readline()
        message = message[2:] if message[0] == ';' else None

    if mut_line:
        if mut_line[0] == '[':
            mutations = json.loads(mut_line)
        else:
            mutations = mut_line.split('->')
            if len(mutations) == 1:
                mutations = []
    else:
        mutations = []

    if filename.startswith('out'):
        filename = '/'.join(filename.split('/')[2:])
        seed_name = '_'.join(filename.split('_')[:-1]) + '.smt2'
    else:
        seed_name = filename

    return mutations, message, seed_name


def redo_mutations(filename: str):
    """Reproduce the bug."""
    mutations, message, seed_name = get_bug_info(filename)
    id = 0
    group = InstanceGroup(id, seed_name)
    group.restore(id, mutations)
    instance = group[-1]
    if is_same_res(instance, message=message):
        instance.dump('output/bugs',
                      group.filename,
                      0,
                      to_name=instance.id)
    else:
        print('Bug not found')


def expand_params(params):
    result = {}
    for param in all_params:
        name = param.name.lower()
        if name in params:
            result[name] = {
                'value': params[name],
                'is_default': False
            }
        else:
            result[name] = {
                'value': param.default_value,
                'is_default': True
            }
    return result


def deduplicate(files, bug_files: str, logfile: str) -> dict:
    # def param_to_str(param: str, params: defaultdict) -> str:
    #     name = 'not ' if not params[param] else ''
    #     name += param + ' '
    #     return name
    #
    # bug_groups = defaultdict(set)
    # if bug_files:
    #     if not os.path.isdir(bug_files):
    #         return {'': bug_files}
    #     else:
    #         files = get_filenames(bug_files)
    # elif logfile:
    #     stats = log_analysis.analyze([logfile], [], None, None)
    #     start_time = stats.df.iloc[1]['current_time']
    #     ind = stats.df['status'] == 'wrong_model'
    #     files = set()
    #     for i, entry in stats.df.loc[ind].iterrows():
    #         if entry['current_time'] - start_time > \
    #                 log_analysis.DAY * log_analysis.SEC_IN_HOUR:
    #             break
    #
    #         if entry['model_state'] == -1:
    #             filename = entry['filename']
    #             bug_id = str(int(entry['id']))
    #             bug_name = 'output/bugs/' + filename[:-5] + \
    #                        '_' + bug_id + '.smt2'
    #             files.add(bug_name)
    previous_cases = set()
    result_report = {}
    for file in tqdm.tqdm(sorted(files)):
        file_report = {}
        result_report[file] = file_report
        # print(file)
        # instance = reduce(file, True, False)
        mutations, message, seed_name = get_bug_info(file)
        group_id = len(instance_groups)
        group = InstanceGroup(group_id, seed_name)
        group.restore(group_id, mutations)
        instance = group[-1]

        chc = parse_smt2_file(file, ctx=instances.current_ctx)
        instance.set_chc(chc)

        if instance is None:
            continue

        cur_params = deepcopy(instance.params)

        file_report['reproduce'] = {
            'check': is_same_res(instance),
            'params': expand_params(instance.params)
        }
        # continue

        instance.params = {}
        file_report['default_params'] = {
            'check': is_same_res(instance),
            'params': expand_params(instance.params)
        }

        instance.params = deepcopy(cur_params)
        for param in {'xform.coi',
                      'xform.compress_unbound',
                      'xform.inline_eager',
                      'xform.inline_linear',
                      'xform.slice',
                      'xform.tail_simplifier_pve',
                      'datalog.subsumption'}:
            instance.params[param] = False
        file_report['without_transformations'] = {
            'check': is_same_res(instance),
            'params': expand_params(instance.params)
        }

        instance.params = {}
        for param in {'xform.coi',
                      'xform.compress_unbound',
                      'xform.inline_eager',
                      'xform.inline_linear',
                      'xform.slice',
                      'xform.tail_simplifier_pve'
                      }:
            if param in cur_params:
                instance.params[param] = cur_params[param]

        file_report['transformations_only'] = {
            'check': is_same_res(instance),
            'params': expand_params(instance.params)
        }

        instance.params = deepcopy(cur_params)
        file_report['reproduce_check'] = {
            'check': is_same_res(instance),
            'params': expand_params(instance.params)
        }
    return result_report

    #     reproduce = True
    #     if instance.mutation.number == 1:
    #         new_instance = reduce(file, True, False)
    #         if new_instance is not None:
    #             instance = new_instance
    #         else:
    #             reproduce = False
    #     last_mutation = instance.mutation
    #     if last_mutation.number <= 1 and reproduce:
    #         bug_groups[last_mutation.type.name.lower()].add(instance)
    #     else:
    #         inline_name = ''
    #         if 'xform.inline_linear_branch' in cur_params:
    #             inline_name += param_to_str('xform.inline_linear_branch', cur_params)
    #         if 'xform.inline_eager' in cur_params:
    #             inline_name += param_to_str('xform.inline_eager', cur_params)
    #         if 'xform.inline_linear' in cur_params:
    #             inline_name += param_to_str('xform.inline_linear', cur_params)
    #         if inline_name:
    #             bug_groups[inline_name].add(instance)
    #         else:
    #             old_case = False
    #             for prev_mutation in previous_cases:
    #                 if last_mutation.same_chain_start(prev_mutation):
    #                     old_case = True
    #             if not old_case:
    #                 bug_groups['other'].add(instance)
    #                 previous_cases.add(last_mutation)
    #                 print(last_mutation.get_chain())
    #
    # for key in sorted(bug_groups):
    #     print(key, len(bug_groups[key]))


def group_by(data, key_getter):
    result = defaultdict(list)
    for it in data:
        key = key_getter(it)
        result[key].append(it)
    return result


def param_diff(left: dict, right: dict, left_name=None, right_name=None):
    if left.keys() != right.keys():
        raise Exception("bad params")

    result = {}
    for param in left.keys():
        l_value = left[param]['value']
        r_value = right[param]['value']
        if l_value == r_value:
            result[param] = {
                'equal': l_value
            }
            continue
        result[param] = {
            (left_name or 'left'): l_value,
            (right_name or 'right'): r_value,
        }

    return result


def analyze_transformations(sample: dict):
    classification = sample['classification']
    if classification['type'] != 'transformation_dependent':
        return
    file = sample['file']
    mutations, message, seed_name = get_bug_info(file)
    group_id = len(instance_groups)
    group = InstanceGroup(group_id, seed_name)
    group.restore(group_id, mutations)
    instance = group[-1]

    chc = parse_smt2_file(file, ctx=instances.current_ctx)
    instance.set_chc(chc)

    params = {name: p['equal'] for name, p in classification['params'].items() if 'equal' in p}
    for param, value in classification['params'].items():
        if 'equal' in value:
            continue
        params[param] = value['true_check']

    required_params = {}
    for param, value in classification['params'].items():
        if 'equal' in value:
            continue
        tp = value['true_check']
        fp = value['false_check']
        instance.params = deepcopy(params)
        instance.params[param] = fp
        check = is_same_res(instance)
        if not check:
            params[param] = tp
            required_params[param] = tp
    classification['required'] = required_params


def analyze_samples(sample: dict):
    keys = ['reproduce', 'default_params', 'without_transformations', 'transformations_only']
    if not sample['without_transformations']['check'] and sample['transformations_only']['check']:
        pd = param_diff(
            sample['without_transformations']['params'], sample['transformations_only']['params'],
            'false_check', 'true_check'
        )
        sample['classification'] = {
            'type': 'transformation_dependent',
            'params': pd
        }
        return
    if sample['default_params']['check'] and not sample['without_transformations']['check']:
        pd = param_diff(sample['default_params']['params'], sample['without_transformations']['params'], 'true_check',
                        'false_check')
        sample['classification'] = {
            'type': 'transformation_dependent',
            'params': pd
        }
        return
    if not sample['default_params']['check'] and sample['without_transformations']['check']:
        pd = param_diff(
            sample['default_params']['params'], sample['without_transformations']['params'],
            'false_check', 'true_check'
        )
        sample['classification'] = {
            'type': 'solver_params_dependent',
            'params': pd
        }
        return

    if not sample['default_params']['check'] and not sample['without_transformations']['check'] and not \
            sample['transformations_only']['check']:
        pd = param_diff(
            sample['default_params']['params'], sample['reproduce']['params'],
            'false_check', 'true_check'
        )
        sample['classification'] = {
            'type': 'other',
            'params': pd
        }
        return

    sample['classification'] = {
        'type': 'unclassified',
        'params': {}
    }
    return


def classify_data():
    with open('/data/04.json') as f:
        data = json.load(f)

    reproduced_data = {
        f: data
        for f, data in data.items()
        if data['reproduce']['check'] and data['reproduce_check']['check']
    }
    for f, data in reproduced_data.items():
        data['file'] = f

    for data in reproduced_data.values():
        analyze_samples(data)

    for data in tqdm.tqdm(reproduced_data.values()):
        analyze_transformations(data)

    classified_data = group_by(reproduced_data.values(), key_getter=lambda it: it['classification']['type'])

    with open('/data/04_x.json', 'w') as f:
        json.dump(reproduced_data, f)


def postprocess_classified():
    with open('02_x.json') as f:
        data = json.load(f)
    classified_data = group_by(data.values(), key_getter=lambda it: it['classification']['type'])
    classified_transformations = group_by(
        classified_data['transformation_dependent'],
        key_getter=lambda it: tuple(
            sorted([(k, v) for k, v in it['classification']['required'].items() if k != 'xform.coi'])
        )
    )
    classified_transformations_data = [
        {
            'required_parameters': {
                p: v for p, v in key
            },
            'data': value
        }
        for key, value in classified_transformations.items()
    ]
    classified_data['transformation_dependent'] = classified_transformations_data
    with open('02_classified.json', 'w') as f:
        json.dump(classified_data, f)
    return


def group_classified_entries(report0):
    return {
        'other': [it['reproduce']['params'] for it in report0['other']],
        'solver_params_dependent': [it['reproduce']['params'] for it in report0['solver_params_dependent']],
        'transformation_dependent': [
            (it['required_parameters'], len(it['data']))
            for it in report0['transformation_dependent']
        ],
    }


def aggregate_report_stats(report1):
    transformation_inline_linear = 0
    transformation_inline_eager = 0
    transformation_other = 0
    for (params, size) in report1['transformation_dependent']:
        if params == {'xform.inline_linear': True}:
            transformation_inline_linear += size
            continue
        if params == {'xform.inline_eager': True}:
            transformation_inline_eager += size
            continue
        transformation_other += size

    report2 = {
        'unclassified': len(report1['other']),
        'solver_params_dependent': len(report1['solver_params_dependent']),
        'transformation_inline_linear': transformation_inline_linear,
        'transformation_inline_eager': transformation_inline_eager,
        'transformation_other': transformation_other,
    }
    report2['total'] = sum(report2.values())
    return report2


def split_runs(report0):
    reportx = defaultdict(dict)
    for sample in report0['other']:
        key = sample['file'].split('work-dir-')[1].split('/bugs/')[0]
        data = reportx[key].setdefault('other', [])
        data.append(sample)
    for sample in report0['solver_params_dependent']:
        key = sample['file'].split('work-dir-')[1].split('/bugs/')[0]
        data = reportx[key].setdefault('solver_params_dependent', [])
        data.append(sample)
    for samples in report0['transformation_dependent']:
        params = samples['required_parameters']
        params_x = defaultdict(list)
        for sample in samples['data']:
            key = sample['file'].split('work-dir-')[1].split('/bugs/')[0]
            params_x[key].append(sample)
        for key, samples in params_x.items():
            data = reportx[key].setdefault('transformation_dependent', [])
            data.append({'required_parameters': params, 'data': samples})
    return reportx


def gather_stats():
    with open('05_classified.json') as f:
        data = json.load(f)
    report0 = {
        'other': data.get('other', []),
        'solver_params_dependent': data.get('solver_params_dependent', []),
        'transformation_dependent': []
    }
    for sample in data.get('transformation_dependent', []):
        if not sample['required_parameters']:
            report0['other'].extend(sample['data'])
            continue
        report0['transformation_dependent'].append(sample)

    reportx = split_runs(report0)
    report1 = group_classified_entries(report0)
    report1_x = {key: group_classified_entries(report0) for key, report0 in reportx.items()}

    report2 = aggregate_report_stats(report1)
    report2_x = {key: aggregate_report_stats(report1) for key, report1 in report1_x.items()}

    with open('05_report.json', 'w') as f:
        json.dump(report2, f)

    with open('05_report_detailed.json', 'w') as f:
        json.dump(report2_x, f)

    return


def main():
    global all_params

    parser = argparse.ArgumentParser()
    parser.add_argument('bug_file',
                        nargs='?',
                        default=None)
    parser.add_argument('seed_file',
                        nargs='?',
                        default=None)
    parser.add_argument('-logfile',
                        nargs='?',
                        default=None)
    parser.add_argument('-reduce_chain', action='store_true')
    parser.add_argument('-reproduce', action='store_true')
    parser.add_argument('-deduplicate', action='store_true')
    argv = parser.parse_args()
    instances.set_ctx(Context())

    init_mut_types([])
    all_params = [m for m in mut_types.values() if m.name in ALL_PARAMS]

    # classify_data()
    # return
    #
    # postprocess_classified()
    # return
    #
    # gather_stats()
    # return

    # base = '/data/bugs2/bugs/work-dir-02'
    #
    # bug_data = {}
    # for work_dir in os.listdir(base):
    #    bugs_dir = os.path.join(base, work_dir, 'bugs')
    #    files = get_filenames(bugs_dir)
    #    bug_data[work_dir] = [it for it in files if os.path.exists(it)]
    #
    # all_bug_files = [f for files in bug_data.values() for f in files]
    # all_bug_files = [argv.bug_file]

    # with open('/data/04_data.json') as f:
    #     bug_data = json.load(f)
    # all_bug_files = [bug_file for bug_file, data in bug_data.items() if data['reproduce']['check']]
    #
    # result_report = deduplicate(all_bug_files, None, None)
    #
    # with open('04.json', 'w') as f:
    #     json.dump(result_report, f)
    #
    # return

    return
    if not argv.seed_file:
        if argv.reduce_chain:
            filenames = get_filenames('output/bugs') if not argv.bug_file else [argv.bug_file]
            for filename in filenames:
                print(filename)
                reduce(filename, argv.reduce_chain)
        elif argv.reproduce:
            redo_mutations(argv.bug_file)
        else:
            all_params = get_solving_params()
            if os.stat(csv_file.name).st_size == 0:
                # header = ['bug_file'] + [param.name.lower() for param in all_params]
                header = ['bug_file', 'with_datalog.subsumption']
                writer.writerow(header)
            deduplicate(argv.bug_file, argv.logfile)
            csv_file.close()
    else:
        seed = parse_smt2_file(argv.seed_file,
                               ctx=instances.current_ctx)
        mutant = parse_smt2_file(argv.bug_file,
                                 ctx=instances.current_ctx)
        if equivalence_check(seed, mutant):
            print('Equivalent')
        else:
            assert False, 'The mutant is not equivalent to its seed'


if __name__ == '__main__':
    main()
