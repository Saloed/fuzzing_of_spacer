import json
import argparse
import math
import os

import pandas as pd
import matplotlib.pyplot as plt

from collections import defaultdict
from statistics import mean

INPUTS_GROUP_NUM = 1
MUT_TABLE_COLUMN_NUMBER = 8

unique_traces = 0
colors = ['crimson', 'teal', 'darkorange', 'darkblue']
markers = ['d', 's', '^', 'o', '+']
graph_i = 0


class Stats:

    def __init__(self, filename):
        self.logfile = filename
        file = open(filename, 'r')
        self.lines = file.readlines()
        file.close()
        self.df = None
        self.seed_num = 0

    def create_time_graph(self, fig: plt.Figure, y: str, with_mut_type_times: bool):
        num_axis = []
        time_axis = []
        total_mut_time = 0
        total_solve_time = 0
        ax = fig.gca()
        num = 0
        time_ind = self.df['current_time'].notnull()
        status_ind = self.df['status'].notnull()
        status_rows = self.df[status_ind]

        solve_times = []
        mut_times = []

        if with_mut_type_times:
            mut_type_times = defaultdict(float)
            mut_type_ind = self.df['mut_type'].notnull()
            mut_type_rows = self.df[mut_type_ind]
            j = -1

        k = -self.seed_num
        entry = self.df[time_ind].iloc[0]
        fst_time = entry['current_time']

        for i, entry in self.df[time_ind].iterrows():
            if not math.isnan(entry['solve_time']):

                if with_mut_type_times and not math.isnan(entry['mut_type']):
                    j += 1
                    mut_type = mut_type_rows.iloc[j]['mut_type']
                    mut_type = mut_type.split('(')[0]
                    mut_type_times[mut_type] += entry['mut_time'] / 3600

                if not math.isnan(entry['mut_time']):
                    mut_times.append(entry['mut_time'] / 3600)
                    total_mut_time += entry['mut_time'] / 3600
                solve_times.append(entry['solve_time'] / 3600)
                total_solve_time += entry['solve_time'] / 3600
            time = (entry['current_time'] - fst_time) / 3600
            time_axis.append(time)
            if y == 'bugs':
                k += 1
                if 0 < k and status_rows.iloc[k]['status'] in {'bug', 'wrong_model'}:
                    num += 1
            else:
                num = entry[y]
            num_axis.append(num)

        entry = self.df[time_ind].iloc[-1]
        last_time = entry['current_time']
        total_time = (last_time - fst_time) / 3600

        ax.set_xlabel('Time, h')
        if y == 'bugs':
            ax.set_ylabel('Bugs')
        else:
            ax.set_ylabel('Inputs solved')
        ax.plot(time_axis, num_axis)
        print('Mutation time to total time:',
              round(total_mut_time / total_time, 5))
        print("Mutation time:", round(total_mut_time, 5))
        print('Solving time to total time:',
              round(total_solve_time / total_time, 5))
        print("Solving time:", round(total_solve_time, 5))
        print("Mean solving time:", round(mean(solve_times), 5))
        print("Total time:", round(total_time, 5))

        if with_mut_type_times:
            sorted_mut_type_times = dict(sorted(mut_type_times.items(),
                                           key=lambda item: item[1],
                                           reverse=True))
            for mut in sorted_mut_type_times:
                print(mut, sorted_mut_type_times[mut] / total_time)

    def create_traces_time_graph(self, fig: plt.Figure):
        global graph_i

        time_axis = []
        unique_traces_axis = []
        coef = []
        ax = fig.gca()
        ind = self.df['unique_traces'].notnull()
        last_time = None
        cur_time = None
        start_time = None
        last_trace = 0
        cur_trace = 0
        cur_run = 0
        j = 0
        for i, entry in self.df[ind].iterrows():
            if not start_time:
                start_time = entry['current_time']
            if entry['current_time'] - start_time > 43 * 60 * 60:
                break
            cur_time = entry['current_time']
            cur_trace = entry['unique_traces']
            cur_run = entry['runs']
            if i >= self.seed_num and \
                    (not last_time or
                     cur_time - last_time >= 3600):
                unique_traces_axis.append(cur_trace)
                print(cur_trace - last_trace)
                time = (cur_time - start_time) / (60 * 60)
                time_axis.append(time)
                if last_time:
                    coef.append(cur_trace / time if time else 0)
                last_time = cur_time
                last_trace = cur_trace
            j += 1

        print("Total time:", round((cur_time - start_time)/(60*60), 5))
        print("Run number:", cur_run)
        print("Trace number:", cur_trace)

        ax.set_ylabel('Unique traces')
        ax.set_xlabel('Time, h')
        # ax.set_ylabel('Количество уникальных трасс')
        # ax.set_xlabel('Время работы, ч')

        # lin_coef = mean(coef)
        # ax.plot(time_axis, [item * lin_coef for item in time_axis], c='black', linestyle='--')
        ax.plot(time_axis, unique_traces_axis, marker=markers[graph_i], fillstyle='none')
        graph_i += 1

    def create_traces_runs_graph(self, fig: plt.Figure):
        global graph_i

        time_axis = []
        unique_traces_axis = []
        ax = fig.gca()
        ind = self.df['unique_traces'].notnull()
        last_trace = 0
        j = 0
        for i, entry in self.df[ind].iterrows():
            if i >= self.seed_num and \
                    (entry['unique_traces'] - last_trace > 2000):
                last_trace = entry['unique_traces']
                unique_traces_axis.append(last_trace)
                time_axis.append(entry['runs'])
            j += 1
        ax.set_ylabel('Количество уникальных трасс')
        ax.set_xlabel('Количество прогонов')
        ax.plot(time_axis, unique_traces_axis, marker=markers[graph_i], fillstyle='none')
        # c=colors[graph_i],  fillstyle='none')
        graph_i += 1

    def get_mutation_weights(self):
        entries_ind = self.df[self.df['SWAP_AND'].notnull()].index.tolist()
        last_ind = entries_ind[-1]
        last_entry = self.df.iloc[last_ind]
        mut_weights_ind = last_entry.notnull()
        mut_weights = last_entry[mut_weights_ind][2:]
        with open('stats/mut-weights.txt', 'w+') as file:
            sorted_weights = dict()
            mut_names = mut_weights.index.values
            for i, entry in enumerate(mut_weights):
                sorted_weights[mut_names[i]] = entry
            sorted_weights = dict(sorted(sorted_weights.items(),
                                         key=lambda item: item[1],
                                         reverse=True))
            for mut_name in sorted_weights:
                file.writelines([mut_name,
                                 ' ',
                                 str(sorted_weights[mut_name]),
                                 '\n'])

    def analyze_entries(self, status: str):
        print('_______________' + status +
              '_______________', end='\n')
        ind = self.df['status'] == status
        count_dict = defaultdict(int)
        num = 0
        for i, entry in self.df.loc[ind].iterrows():
            filename = entry['filename']
            num += 1
            # if entry['model_state'] == -1:
            #     count_dict[entry['mut_type'].split('(')[0]] += 1
            count_dict[filename] += 1

        count_dict = dict(sorted(count_dict.items(),
                                 key=lambda item: item[1],
                                 reverse=True))
        for key in count_dict:
           print(key, count_dict[key])
        print(num)


def analyze(log_names: list, stats: list, select: list, options: list):
    if not os.path.exists('stats'):
        os.makedirs('stats')

    traces = plt.figure()
    times = plt.figure()
    legend = []
    for i, name in enumerate(log_names):
        cur_stats = Stats(name)

        entries = []
        for line in cur_stats.lines:
            try:
                entry = json.loads(line)
                if not cur_stats.seed_num and 'seed_number' in entry:
                    info = entry
                    cur_stats.seed_num = info['seed_number']
                elif 'context_deletion_error' not in entry:
                    entries.append(list(entry.values())[0])

            except Exception:
                print('Can\'t read the line:', line)
        cur_stats.df = pd.DataFrame(entries)

        # for heur in info['heuristics']:
        #     if heur == 'transitions':
        #         legend.append('Trace transition heuristic')
        #     elif heur == 'states':
        #         legend.append('Trace state heuristic')
        #     elif heur == 'difficulty':
        #         legend.append('Complexity heuristic')
        #     else:
        #         legend.append('Default')

        if select:
            for status in select:
                cur_stats.analyze_entries(status)

        if 'traces' in stats:
            cur_stats.create_traces_time_graph(traces)
            # cur_stats.create_traces_runs_graph(traces)
        with_mut_type_times = True if 'with_mut_type_times' in options else False
        if 'runs' in stats:
            cur_stats.create_time_graph(times, 'runs', with_mut_type_times)
        if 'bugs' in stats:
            cur_stats.create_time_graph(times, 'bugs', with_mut_type_times)
        if 'mutations' in stats:
            cur_stats.get_mutation_weights()

    legend.append('Random order')
    legend.append('Simple instance heuristic')
    legend.append('Complex instance heuristic')
    legend.append('Rare transition heuristic')
    # legend.append('Linear approximation')

    if 'traces' in stats:
        traces.legend(legend, bbox_to_anchor=(0.57, 0.88))  # (0.49, 0.88)
        traces.savefig('stats/traces.png', bbox_inches='tight')

    if 'runs' in stats or 'bugs' in stats:
        times.legend(legend, bbox_to_anchor=(0.9, 0.8))  # (0.9, 0.28)
        times.savefig('stats/times.png', bbox_inches='tight')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('logfile',
                        nargs='*',
                        default=['logfile'])
    parser.add_argument('-stats',
                        nargs='*',
                        choices=['runs', 'traces', 'mutations', 'bugs', 'cov'],
                        default=[],
                        help='what statistics do you want to see')
    parser.add_argument('-select',
                        nargs='*',
                        choices=['seed_unknown', 'seed_timeout',
                                 'solver_conflict', 'mutant_timeout',
                                 'mutant_unknown', 'error', 'bug',
                                 'wrong_model', 'model_timeout', 'pass',
                                 'timeout_before_check', 'without_change'],
                        default=[],
                        help='what kind of log entries do you want to see')
    parser.add_argument('-options', '-opt',
                        nargs='*',
                        choices=['with_mut_type_times'],
                        default=[])
    argv = parser.parse_args()
    plt.rc('font', size=11)

    analyze(argv.logfile, argv.stats, argv.select, argv.options)


if __name__ == '__main__':
    main()
