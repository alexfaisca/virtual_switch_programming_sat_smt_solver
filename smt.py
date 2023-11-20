#!/usr/bin/python3
# alc23 - 13 - project2 
# DO NOT remove or edit the lines above. Thank you.

import time
from operator import itemgetter
from inout import *
from z3 import *
import sys
from networkx import DiGraph, topological_sort, Graph, edge_boundary, get_edge_attributes
from networkx.algorithms.community import greedy_modularity_communities


def translate_precedences(precedences):
    # Create a directed graph
    graph = DiGraph()
    precedences_list = []

    for name, value in precedences.items():
        if value:
            _, name1, name2 = name.split("_")
            switch_1 = int(name1)
            switch_2 = int(name2)
            precedences_list.append([switch_1, switch_2])

    # Add relative position based edges
    for precedence in precedences_list:
        graph.add_edge(precedence[0], precedence[1])

    # Get topological order
    return list(topological_sort(graph))


def soft_clause_partitioning(n, f):
    cvgi_graph = Graph()
    rules = list(range(1, n + 1))

    incidence = [0 for _ in rules]
    for ancestor, descendant in f:
        incidence[ancestor - 1] = incidence[ancestor - 1] + 1
        incidence[descendant - 1] = incidence[descendant - 1] + 1

    incidence = [(1 + 1 / weight) if weight > 0 else 1 for weight in incidence]

    for rule in rules:
        cvgi_graph.add_node(f"var_{rule}")

    for index, dependency in enumerate(f):
        cvgi_graph.add_node(f"{index}")
        cvgi_graph.add_edge(f"var_{dependency[0]}", f"{index}", weight=incidence[dependency[0] - 1])
        cvgi_graph.add_edge(f"var_{dependency[1]}", f"{index}", weight=incidence[dependency[1] - 1])

    communities = greedy_modularity_communities(cvgi_graph)

    connection_strength = [[0] * len(communities) for _ in communities]

    weight_labels = get_edge_attributes(cvgi_graph, 'weight')
    for index in range(len(communities)):
        for ext_index in [x for x in range(index + 1, len(communities))]:
            edges = list(edge_boundary(cvgi_graph, communities[index], communities[ext_index]))
            strength_vector = sum([
                    float(weight_labels[edge]) if weight_labels.__contains__(edge)
                    else weight_labels[(edge[1], edge[0])]
                    for edge in edges
                ])
            connection_strength[index][ext_index] = strength_vector
            connection_strength[ext_index][index] = strength_vector

    filtered_communities = []
    for community in communities:
        filtered_communities.append(list(filter(lambda vertex: vertex[0] != 'v', community)))

    filtered_communities = list(sorted(filtered_communities, key=lambda c: len(c)))
    return filtered_communities, connection_strength


def merge_partitions(connection_strength, relaxed_clauses, lambdas):
    # Get max strength of connection between any two communities
    first_community, temp = \
        max(enumerate((max(enumerate(vec), key=itemgetter(1))) for vec in connection_strength), key=itemgetter(1, 1))
    second_community, strength = temp

    if first_community > second_community:
        temp = first_community
        first_community = second_community
        second_community = temp

    # Get new partition connection strength vector
    first_strength_vector = connection_strength.pop(second_community)
    second_strength_vector = connection_strength.pop(first_community)
    strength_vector = [x + y for x, y in zip(first_strength_vector, second_strength_vector)]
    strength_vector.pop(second_community)
    strength_vector.pop(first_community)
    strength_vector.append(0)
    for community, vector in enumerate(connection_strength):
        first_community_connection = vector.pop(second_community)
        second_community_connection = vector.pop(first_community)
        connection_strength[community].append(first_community_connection + second_community_connection)
    connection_strength.append(strength_vector)

    # Update problem specs
    first_clause_set = relaxed_clauses.pop(second_community)
    second_clause_set = relaxed_clauses.pop(first_community)
    relaxed_clauses.append(first_clause_set + second_clause_set)
    first_lambda = lambdas.pop(second_community)
    second_lambda = lambdas.pop(first_community)
    lambdas.append(first_lambda + second_lambda)


# MaxSAT Divide and Conquer through community finding emplying basic incremental algorithm
def divide_and_conquer_smt(hard_clauses, soft_clauses, n, f):
    solver = Optimize()
    solver.assert_exprs(hard_clauses)
    if solver.check() != sat:
        raise Exception("UNSATISFIABLE")

    partitioned_clauses = []
    model = []

    partition, connection = soft_clause_partitioning(n, f)
    recirculations = [0] * len(partition)

    for community, clauses in enumerate(partition):
        partitioned_clauses.append([soft_clauses[int(index)] for index in clauses])
        _, recirculations[community] = max_sat_inc(hard_clauses, partitioned_clauses[-1])

    print(len(partition), "communities found")

    while len(partitioned_clauses) > 1:
        merge_partitions(connection, partitioned_clauses, recirculations)
        model, recirculations[-1] = max_sat_inc(hard_clauses, partitioned_clauses[-1], recirculations[-1])

    return solver.model(), recirculations[-1]


# MaxSAT MSU3 Algorithm
def max_sat_msu3(hard_clauses, soft_clauses):
    # Check if formula is staisfiable
    solver = Optimize()
    solver.assert_exprs(hard_clauses)
    if solver.check() != sat:
        raise Exception("UNSATISFIABLE")

    # Optimize solution
    recirculations = 0
    relaxation_variables = []
    relaxed = [False] * len(soft_clauses)

    for index, clause in enumerate(soft_clauses):
        relaxation_variables.append(Bool(f"r_{index}"))
        soft_clauses[index] = Or(clause, relaxation_variables[-1])
        solver.assert_and_track(soft_clauses[index], f"{index}")
    solver.push()

    for var in relaxation_variables:
        solver.add(Not(var))

    while solver.check() != sat:
        print("unsat")
        for clause in solver.unsat_core():
            relaxed[int(str(clause))] = True

        solver.pop()
        solver.push()
        recirculations = recirculations + 1

        # Stress clauses not yet having been part of an unsat core and AtMost-k on relaxed ones
        at_most_vars = []
        for index, var in enumerate(relaxation_variables):
            if relaxed[index]:
                at_most_vars.append(var)
            else:
                solver.assert_exprs(Not(var))
        solver.add(AtMost(*at_most_vars, recirculations))
        
    return solver.model(), recirculations


# MaxSAT Fu&Malik's Algorithm
def max_sat_fm(hard_clauses, soft_clauses):
    # Assert formula is satisfiable
    solver = Optimize()
    solver.assert_exprs(hard_clauses)
    if solver.check() != sat:
        raise Exception("UNSATISFIABLE")
    solver.push()

    # Optimize solution
    recirculations = 0
    at_most = []

    for index, clause in enumerate(soft_clauses):
        solver.assert_and_track(soft_clauses[index], f"{index}")

    while solver.check() != sat:
        solver.pop()
        solver.push()
        print("unsat")
        recirculations = recirculations + 1

        # Relax unsat core
        r = []
        for clause in solver.unsat_core():
            index = int(str(clause))
            r.append(Bool(f"r_{recirculations}_{index}"))
            soft_clauses[index] = Or(soft_clauses[index], r[-1])
        at_most.append(AtMost(*r, 1))
        
        # Add updated soft clauses
        for index, clause in enumerate(soft_clauses):
            solver.assert_and_track(clause, f"{index}")
        for constraint in at_most:
            solver.add(constraint)
        
    return solver.model(), recirculations


# MaxSAT simple incremental Algorithm
def max_sat_inc(hard_clauses, soft_clauses, recirculations = 0):
    # Check if formula is satisfiable
    solver = Optimize()
    solver.add(hard_clauses)
    if solver.check() != sat:
        raise Exception("UNSATISFIABLE")
    
    # Optimize soltion
    relaxed_clauses = []
    relaxation_variables = []

    for index, clause in enumerate(soft_clauses):
        relaxation_variables.append(Bool(f"r_{index}"))
        relaxed_clauses.append(Or(clause, relaxation_variables[index]))
    solver.assert_exprs(relaxed_clauses)
    solver.push()
    
    if recirculations == 0:
       for var in relaxation_variables:
            solver.add(Not(var))
    else:
        solver.add(AtMost(*relaxation_variables, recirculations))

    while solver.check() != sat:
        print("unsat")
        solver.pop()
        solver.push()
        recirculations = recirculations + 1
        solver.add(AtMost(*relaxation_variables, recirculations))
    
    return solver.model(), recirculations


def get_hard_clauses(placement, switch_positions, n, m, mr, ns, mc, f):
    hard_clauses = []

    # Constraint 1.1
    for index, (sw, st) in enumerate(placement):
        # Constraint 1.1.1
        hard_clauses.append(And(1 <= st, 1 <= sw, sw <= m))
        clause = []
        for switch in range(1, m + 1):
            clause.append(sw != switch if mc[switch - 1] < mr[index] else Implies(sw == switch, st <= ns[switch - 1]))
        hard_clauses.append(And(*clause))
    
    # Constraint 1.2
    for switch in range(1, m + 1):
        for stage in range(1, ns[switch - 1] + 1):
            parcels = []
            for rule, (sw, st) in enumerate(placement):
                parcels.append(If(And(sw == switch, st == stage), mr[rule], 0))
            # Constraint 1.2.1
            hard_clauses.append(0 < Sum(*parcels))
            hard_clauses.append(Sum(*parcels) <= mc[switch - 1])


    # Constraint 1.3
    if m > 1:
        precedences = {
            switch_1: {
                switch_2: Bool(f"p_{switch_1}_{switch_2}")
                for switch_2 in range(1, m + 1)
                if switch_1 != switch_2
            }
            for switch_1 in range(1, m + 1)
        }

        # Constraint 1.3.1
        hard_clauses = hard_clauses + [
                Xor(
                    precedences[preceding_switch][succeeding_switch],
                    precedences[succeeding_switch][preceding_switch]
                )
                for preceding_switch in range(1, m + 1)
                for succeeding_switch in range(1, m + 1)
                if preceding_switch != succeeding_switch
            ]

        # Ensure total ordering of switches
        if m > 2:
            for switch in range(1, m + 1):
                for switch2 in range(1, m + 1):
                    if switch2 == switch:
                        continue
                    for switch3 in range(1, m + 1):
                        if switch3 == switch2 or switch3 == switch:
                            continue
                        hard_clauses.append(
                            Implies(
                                And(
                                    precedences[switch][switch2], 
                                    precedences[switch2][switch3]
                                ), 
                                precedences[switch][switch3]
                            )
                        )

        # Constraint 1.3.2
        for preceding_rule, succeeding_rule in f:
            for preceding_switch in range(1, m + 1):
                for succeeding_switch in range(1, m + 1):
                    if preceding_switch != succeeding_switch:
                        hard_clauses.append(
                            Implies(
                                And(
                                    placement[preceding_rule - 1][0] == preceding_switch,
                                    placement[succeeding_rule - 1][0] == succeeding_switch
                                ),
                                precedences[preceding_switch][succeeding_switch]
                            )
                        )
    return hard_clauses


def get_objective_function(placement, f):
    soft_clauses = []

    for preceding_rule, succeeding_rule in f:
        soft_clauses.append(
            Not(
                And(
                    placement[preceding_rule - 1][0] == placement[succeeding_rule - 1][0],
                    placement[succeeding_rule - 1][1] - placement[preceding_rule - 1][1] <= 0
                )
            )
        )

    return soft_clauses




def main():
    n, m, mr, ns, mc, d_number, f = parse_input(sys.stdin.read())
    
    placement = [(Int(f"{i}_sw"), Int(f"{i}_st")) for i in range(1, n + 1)]
    switch_positions = [i for i in range(1, m + 1)]
    hard_clauses = get_hard_clauses(placement, switch_positions, n, m, mr, ns, mc, f)
    soft_clauses = get_objective_function(placement, f)
    
    ##############################################################################################
    # print results ##############################################################################
    ##############################################################################################

    start = time.time()
    # Through trial and error this was found to be the fastest implementation between all those 
    # tried, see above for the different algorithms tested (several variables influence these
    # results, e.g. z3's Solver::assert_and_track is much slower than a simple 
    # Solver::assert_exprs)
    model, recirculations = divide_and_conquer_smt(hard_clauses, soft_clauses, n, f)
    # model, recirculations = max_sat_fm(hard_clauses, soft_clauses)
    # model, recirculations = max_sat_msu3(hard_clauses, soft_clauses)
    # model, recirculations = max_sat_inc(hard_clauses, soft_clauses)
    print(time.time() - start)

    switches = [[] for _ in range(1, n + 1)]
    stages = [[] for _ in range(1, n + 1)]
    solution = [[[] for _ in range(ns[switch])] for switch in range(m)]
    precedences_solution = dict()

    for declaration in model.decls():
        if declaration.name()[-1] == "w":
            rule = declaration.name().split('_')[0]
            switches[int(rule) - 1].append(model[declaration].as_long())
        elif declaration.name()[-1] == "t":
            rule = declaration.name().split('_')[0]
            stages[int(rule) - 1].append(model[declaration].as_long())
        elif declaration.name()[0] == "p":
            precedences_solution[declaration.name()] = is_true(model[declaration])

    if m > 1:
        switch_positions = translate_precedences(precedences_solution)

    for rule in range(1, n + 1):
        solution[switches[rule - 1][0] - 1][stages[rule - 1][0] - 1].append(int(rule))

    print(generate_output(recirculations, switch_positions, solution), end="")

    ##############################################################################################


if __name__ == "__main__":
    main()
