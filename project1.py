#!/usr/bin/python3
# alc23 - 13 - project1 
# DO NOT remove or edit the lines above. Thank you.

import sys

from pysat.examples.rc2 import RC2
from pysat.formula import WCNF
from pysat.pb import PBEnc

from networkx import DiGraph, topological_sort


def parse_input(input_str: str):
    """Parses the input file. The input file provided is assumed to be correct

    Args:
        input_str (str): Input to parse

    Returns:
        n (int): Number of groups of rules
        m (int): Number of switches
        mr (list[int]): List of memory requirement
        ns (list[int]): List of number of stages
        mc (list[int]): List of memory capacity
        d (int): Number of dependencies
        f (list[(list[int])]): List of rules for forwarding
    """
    if input_str[-1] != '\n':
        input_str += '\n'
    lines = input_str.split('\n')[:-1]
    n, m = [int(line) for line in lines[:2]]
    mr = [int(i) for i in lines[2].split(' ')]
    ns = [int(i) for i in lines[3].split(' ')]
    mc = [int(i) for i in lines[4].split(' ')]
    d = int(lines[5])
    f = [[int(i) for i in line.split(' ')] for line in lines[6: (6 + d)]]

    return n, m, mr, ns, mc, d, f


def generate_output(recirculations: int, order: list, placements: list):
    """Generates the string to be output to solution.txt

    Args:
        recirculations (int): Overall number of re-circulations
        order (list[int]): Order of the switches
        placements (list[(list[list[int]])]): Placement of groups of rules in each stage of each switch

    Returns:
        out (str): String to be printed to solution.txt
    """
    out = f"{recirculations}\n"

    for i in range(len(order)):
        out += f"{order[i]} "

    out = out[:-1]
    out += "\n"

    for switch in placements:
        for stage in switch:
            for rule in stage:
                out += f"{rule} "
            out = out[:-1]
            out += ", "
        out = out[:-2]
        out += "\n"

    return out


def create_coding(n: int, m: int, ns: list):  # -> tuple[Callable[..., int], Callable[..., tuple[int, int, int]]]:
    """Creates the encoding and decoding functions which convert between problem variables and SAT

    Args:
        n (int): Number of groups of rules
        m (int): Number of switches
        ns (list[int]): List of number of stages

    Returns:
        encode (Callable[..., int]): Converts from problem variables to its SAT number
        decode (Callable[..., tuple[int, int, int]]): Converts from its SAT number to the problem variables
    """

    # Auxiliary values

    sum_ns = [ns[0] * n]
    for i in range(1, m):
        sum_ns.append(sum_ns[i - 1] + ns[i] * n)

    relative_positions = []
    for i in range(1, m + 1):
        for j in range(1, m + 1):
            relative_positions.append([i, j])

    def encode_template(switch: int, stage: int, rule: int):
        """
        Args:
            switch (int): switch number
            stage (int): stage number
            rule (int): rule group number
        """
        return (0 if switch == 1 else sum_ns[switch - 2]) + (stage - 1) * n + rule

    def decode_template(literal: int):
        """
        Args:
            literal (int): global variable encoding rule placement in switch stage
        """
        literal -= 1
        rule = (literal % n) + 1

        switch = 0
        global_stage = (literal // n) + 1
        while global_stage > 0:
            global_stage -= ns[switch]
            switch += 1
        local_stage = global_stage + ns[switch - 1]  # Unwinds

        return rule, local_stage, switch

    def encode_switch_position_template(switch_1: int, switch_2: int):
        """ Encodes the relative position of two switches
        Args:
            switch_1 (int): the first switch
            switch_2 (int): the second switch
        """

        return sum_ns[m - 1] + m * (switch_1 - 1) + (switch_2 - 1) + 1

    def decode_switch_position_template(literal: int):
        """ Decodes the relative position of two switches
        Args:
            literal (int): global variable encoding switch relative position
        """

        relative = relative_positions[abs(literal) - sum_ns[m - 1] - 1]

        return relative[0], relative[1] if literal > 0 else relative[1], relative[0]

    return encode_template, decode_template, encode_switch_position_template, decode_switch_position_template, \
        sum_ns[m - 1]


def generate_hard_clauses(
        n: int,
        m: int,
        mr: list,
        ns: list,
        mc: list,
        f: list
):
    """
        Receives the problem's specifications and returns its hard clauses
    Args:
        n (int): Number of groups of rules
        m (int): Number of switches
        mr (list[int]): List of memory requirement
        ns (list[int]): List of number of stages
        mc (list[int]): List of memory capacity
        f (list[(list[int])]): List of dependencies between rule groups

    Returns:
        clauses (list[(list[int])]): hard clauses generated
    """
    # 1st Hard Requirement - Individually placing a group of rules in a stage
    # Each group of rules is placed into one and only one stage in one and only one switch

    clauses = []

    for rule in range(1, n + 1):
        clause = []
        for switch in range(1, m + 1):
            for stage in range(1, ns[switch - 1] + 1):
                if mr[rule - 1] > mc[switch - 1]:
                    continue
                else:
                    # Requirement 1.1.2
                    clause += [encode(switch, stage, rule)]
                    for other_stage in range(stage + 1, ns[switch - 1] + 1):
                        # Requirement 1.1.3
                        clauses.append([-encode(switch, stage, rule),
                                                 -encode(switch, other_stage, rule)])
                    for not_switch in range(switch + 1, m + 1):
                        if mr[rule - 1] > mc[not_switch - 1]:
                            continue
                        for not_switch_stage in range(1, ns[not_switch - 1] + 1):
                            # Requirement 1.1.4
                            clauses.append(
                                [-encode(switch, stage, rule), -encode(not_switch, not_switch_stage, rule)])
        clauses.append(clause)

    if m > 1:
        # 2nd Hard Requirement - Consistent relative switch order
        for preceding_switch in range(1, m + 1):
            for middle_switch in range(1, m + 1):
                if preceding_switch == middle_switch:
                    continue
                # Requirement 1.2.1
                clauses.append([-encode_switch_position(preceding_switch, middle_switch),
                                -encode_switch_position(middle_switch, preceding_switch)])
                # Requirement 1.2.2
                clauses.append([encode_switch_position(preceding_switch, middle_switch),
                                encode_switch_position(middle_switch, preceding_switch)])
                for succeeding_switch in range(1, m + 1):
                    if preceding_switch == succeeding_switch or middle_switch == succeeding_switch:
                        continue
                    # Requirement 1.2.3
                    clauses.append([-encode_switch_position(preceding_switch, middle_switch),
                                    -encode_switch_position(middle_switch, succeeding_switch),
                                    encode_switch_position(preceding_switch, succeeding_switch)])

        # 3rd Hard Requirement
        # For each (i, j) ∈ D, then group j cannot be placed into switch preceding switch where group i is placed
        # (i.e., there is no re-circulation between switches)
        for ancestor, descendant in f:
            for switch in range(1, m + 1):
                if mr[ancestor - 1] > mc[switch - 1]:
                    continue
                for not_switch in [x for x in range(1, m + 1) if x != switch]:
                    if mr[descendant - 1] > mc[not_switch - 1]:
                        continue
                    for switch_stage in range(1, ns[switch - 1] + 1):
                        for not_switch_stage in range(1, ns[not_switch - 1] + 1):
                            # Requirement 1.3.1
                            clauses.append([-encode_switch_position(not_switch, switch),
                                            -encode(switch, switch_stage, ancestor),
                                            -encode(not_switch, not_switch_stage, descendant)])

    # 4th Hard Requirement
    # The memory requirements of all groups of rules in each stage of the switch is not higher than its capacity

    top_id = sum(ns) * n + (m * m)

    for switch in range(1, m + 1):
        for stage in range(1, ns[switch - 1] + 1):
            clause = []
            for rule in range(1, n + 1):
                # Requirement 1.1.1
                if mr[rule - 1] <= mc[switch - 1]:
                    clause += [encode(switch, stage, rule)]
            clauses.append(clause)
            # Requirement 1.4.1
            cnf = PBEnc.atmost(
                lits=[encode(switch, stage, rule) for rule in range(1, n + 1)],
                weights=mr,
                bound=mc[switch - 1],
                top_id=top_id
            )
            top_id = cnf.nv
            clauses += cnf.clauses

    return clauses


def generate_soft_clauses(f: list, ns: list, mr: list, mc: list, m: int):
    # Soft Clauses - minimize the overall number of re-circulations, i.e. same stage or previous stage forwarding
    clauses = []
    for switch in range(1, m + 1):
        for stage in range(1, ns[switch - 1] + 1):
            for dependency in f:
                forwarding_rule = dependency[0]
                forwarded_rule = dependency[1]
                if mr[forwarding_rule - 1] > mc[switch - 1] or mr[forwarded_rule - 1] > mc[switch - 1]:
                    continue
                if mr[forwarding_rule - 1] + mr[forwarded_rule - 1] <= mc[switch - 1]:
                    # Requirement 2.1.1
                    clauses.append([-encode(switch, stage, forwarding_rule),
                                             -encode(switch, stage, forwarded_rule)])
                for not_stage in range(1, stage):
                    # Requirement 2.1.2
                    clauses.append([-encode(switch, stage, forwarding_rule),
                                            -encode(switch, not_stage, forwarded_rule)])

    return clauses


def translate_positions(literals: list):
    # Create a directed graph
    graph = DiGraph()
    positions = [decode_switch_position(lit) for lit in literals]

    unique_positions = []
    for position in positions:
        if position not in unique_positions:
            unique_positions.append(position)

    # Add relative position based edges
    for position in unique_positions:
        graph.add_edge(position[0], position[1])

    # Get topological order
    return list(topological_sort(graph))


def extract_solution(solution: list, m: int, sum_ns_times_n: int):
    if not solution:
        raise Exception("UNSATISFIABLE")

    # Keep only encoded true values
    switch_order = m * m
    switch_order_solution = solution[sum_ns_times_n: sum_ns_times_n + switch_order]
    literals_solution = list(filter(lambda lit: lit > 0, solution[:sum_ns_times_n]))

    # Get literals referent to switch relative placement
    switch_positions = [1]
    if m > 1:
        for x in [sum_ns_times_n + x * x for x in range(1, m + 1)]:
            if x in solution:
                switch_order_solution.remove(x)
            elif -x in solution:
                switch_order_solution.remove(-x)
        switch_positions = translate_positions(list(filter(lambda lit: lit > 0, switch_order_solution)))

    return literals_solution, switch_positions


def calculate_recirculations(solution: list, n: int, f: list, m: int):
    # Find the number of recirculations
    sol = solution.copy()
    recirculations = 0

    last_stage = (sol[0] - 1) // n
    rules_in_stage = []
    rules_until_stage = []
    read_literals = 0

    for switch in range(1, m + 1):
        sol = sol[read_literals:]
        read_literals = 0
        for literal in sol:
            # Computes recirculations when moving to the next switch
            if decode(literal)[2] != switch:
                rules_until_stage += rules_in_stage
                for dependency in f:
                    if dependency[0] in rules_in_stage and dependency[1] in rules_until_stage:
                        recirculations += 1

                last_stage = (literal - 1) // n
                rules_in_stage = []
                rules_until_stage = []
                break
            # Computes recirculations when moving to the next stage of a switch
            if last_stage == ((literal - 1) // n):
                rules_in_stage.append((literal - 1) % n + 1)
                read_literals += 1
            else:
                rules_until_stage += rules_in_stage
                for dependency in f:
                    if dependency[0] in rules_in_stage and dependency[1] in rules_until_stage:
                        recirculations += 1

                last_stage = (literal - 1) // n
                rules_in_stage = [(literal - 1) % n + 1]
                read_literals += 1

    rules_until_stage += rules_in_stage
    for dependency in f:
        if dependency[0] in rules_in_stage and dependency[1] in rules_until_stage:
            recirculations += 1

    return recirculations


def display_solution(literals_solution: list, recirculations: int, switch_positions: list, m: int, ns: list):
    placements = []
    for switch in range(m):
        placements.append([])
        # Decode switch in nth position
        for stage in range(ns[switch]):
            placements[switch].append([])

    for literal in literals_solution:
        rule, local_stage, switch = decode(literal)
        placements[switch - 1][local_stage - 1].append(rule)

    print(generate_output(recirculations, switch_positions, placements), end="")


def main():
    n, m, mr, ns, mc, d, f = parse_input(sys.stdin.read())

    global encode, decode, encode_switch_position, decode_switch_position
    encode, decode, encode_switch_position, decode_switch_position, sum_ns_times_n = create_coding(n, m, ns)

    cnf = WCNF()
    # start = time.time()
    cnf.extend(generate_hard_clauses(n, m, mr, ns, mc, f))
    for clause in generate_soft_clauses(f, ns, mr, mc, m):
        cnf.append(clause, weight=1)

    # Solve
    literals_solution, switch_positions = extract_solution(RC2(cnf, adapt = True).compute(), m, sum_ns_times_n)
    # print(time.time() - start)

    # Find the number of recirculations
    recirculations = calculate_recirculations(literals_solution, n, f, m)

    display_solution(literals_solution, recirculations, switch_positions, m, ns)


if __name__ == "__main__":
    main()
