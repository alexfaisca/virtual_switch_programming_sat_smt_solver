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


def merge_partitions(connection_strength, relaxed_clauses, relaxation_variables, lambdas):
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
    first_relaxation_variable_set = relaxation_variables.pop(second_community)
    second_relaxation_variable_set = relaxation_variables.pop(first_community)
    relaxation_variables.append(first_relaxation_variable_set + second_relaxation_variable_set)
    first_lambda = lambdas.pop(second_community)
    second_lambda = lambdas.pop(first_community)
    lambdas.append(first_lambda + second_lambda)


def partial_solver_initialize(hard_assertions, partition, soft_clauses):
    lambdas = [0] * len(partition)
    relaxed_clauses = []
    relaxation_variables = []

    for community, clauses in enumerate(partition):
        relaxed_clauses.append([])
        relaxation_variables.append([])

        for index, clause in enumerate([soft_clauses[int(index)] for index in clauses]):
            relaxation_variables[community].append(Bool(f"r_{community}_{index}"))
            relaxed_clauses[community].append(Or(clause, relaxation_variables[community][index]))
        
        new_solver = Optimize()
 
        new_solver.assert_exprs(hard_assertions)
        for index, clause in enumerate(relaxed_clauses[community]):
            new_solver.assert_and_track(clause, f"p{index}")
        new_solver.add(AtMost(*(relaxation_variables[community]), 0))

        while new_solver.check() != sat:
            print(new_solver.unsat_core(), "done")
            lambdas[community] = lambdas[community] + 1
            new_solver = Optimize()
            new_solver.assert_exprs(hard_assertions)
            new_solver.add(relaxed_clauses[community])
            new_solver.add(AtMost(*(relaxation_variables[community]), lambdas[community]))

        print("partition: ", community, " / unsatisfied soft clauses: ", lambdas[community])

    return lambdas, relaxation_variables, relaxed_clauses


# MaxSAT Divide and Conquer through community finding emplying basic incremental algorithm
def partial_soft_clause_smt(hard_clauses, soft_clauses, n, f):
    solver = Optimize()
    solver.assert_exprs(hard_clauses)
    if solver.check() != sat:
        raise Exception("UNSATISFIABLE")

    hard_assertions = solver.assertions()
    partition, connection = soft_clause_partitioning(n, f)

    lambdas, relaxation_variables, relaxed_clauses = partial_solver_initialize(hard_assertions, partition, soft_clauses)

    while len(relaxed_clauses) > 1:
        merge_partitions(connection, relaxed_clauses, relaxation_variables, lambdas)

        new_solver = Optimize()
        new_solver.assert_exprs(hard_assertions)
        for index, clause in enumerate(relaxed_clauses[-1]):
            new_solver.assert_and_track(clause, f"{index}")
        new_solver.add(AtMost(*(relaxation_variables[-1]), lambdas[-1]))

        # MAXSAT FM algorithm
        while new_solver.check() != sat:
            print(new_solver.unsat_core(), "done")
            lambdas[-1] = lambdas[-1] + 1
            new_solver = Optimize()
            new_solver.assert_exprs(hard_assertions)
            new_solver.add(relaxed_clauses[-1])
            new_solver.add(AtMost(*relaxation_variables[-1], lambdas[-1]))

        print("merge (", len(relaxed_clauses) - 1, "remaining merges )")

    return new_solver.model(), lambdas[-1]


# MaxSAT MSU3 Algorithm
def max_sat_msu3(hard_clauses, soft_clauses):
    # Check if formula is staisfiable
    solver = Optimize()
    solver.assert_exprs(hard_clauses)
    if solver.check() != sat:
        raise Exception("UNSATISFIABLE")

    # Optimize solution
    relaxed_clauses = []
    relaxation_variables = []
    cost = 0
    hard_clauses = solver.assertions()
    relaxed = []

    solver = Optimize()
    solver.assert_exprs(hard_clauses)
    for index, clause in enumerate(soft_clauses):
        relaxation_variables.append(Bool(f"r_{index}"))
        relaxed_clauses.append(Or(clause, relaxation_variables[index]))
        solver.assert_and_track(soft_clauses[index], f"{index}")

    while solver.check() != sat:
        cost = cost + 1

        unsat_core = []
        for clause in solver.unsat_core():
            unsat_core.append(relaxation_variables[int(str(clause))])
            relaxed.append(int(str(clause)))

        solver = Optimize()
        solver.assert_exprs(hard_clauses)
        for index, clause in enumerate(relaxed_clauses):
            solver.assert_and_track(clause, f"{index}")
        solver.add(AtMost(*list(set(clauses)), cost))

        # Stress clauses not yet having been part of an unsat core
        clauses = []
        for c in relaxed:
            clauses.append(relaxation_variables[c])
        for c in relaxation_variables:
            if c not in clauses:
                solver.add(Not(c))
        
    return solver.model(), cost


# MaxSAT Fu&Malik's Algorithm
def max_sat_fm(hard_clauses, soft_clauses):
    # Assert formula is satisfiable
    solver = Optimize()
    solver.assert_exprs(hard_clauses)
    if solver.check() != sat:
        raise Exception("UNSATISFIABLE")

    # Optimize solution
    cost = 0
    at_most = []

    solver = Optimize()
    solver.assert_exprs(hard_clauses)
    for index, clause in enumerate(soft_clauses):
        solver.assert_and_track(soft_clauses[index], f"{index}")

    while solver.check() != sat:
        print("unsat")
        cost = cost + 1

        r = []
        for clause in solver.unsat_core():
            index = int(str(clause))
            r.append(Bool(f"r_{cost}_{index}"))
            soft_clauses[index] = Or(soft_clauses[index], r[-1])
        at_most.append(AtMost(*r, 1))

        solver = Optimize()
        solver.assert_exprs(hard_clauses)
        for index, clause in enumerate(soft_clauses):
            solver.assert_and_track(clause, f"{index}")

        for constraint in at_most:
            solver.add(constraint)
        
    return solver.model(), cost


# MaxSAT PM2 Algorithm
def max_sat_pm2(hard_clauses, soft_clauses):
    # Assert formula is satisfiable
    solver = Optimize()
    solver.assert_exprs(hard_clauses)
    if solver.check() != sat:
        raise Exception("UNSATISFIABLE")

    # Optimize soltion
    relaxed_clauses = []
    relaxation_variables = []
    cost = 0
    unsat_cores = []
    at_least = []

    solver = Optimize()
    solver.assert_exprs(hard_clauses)
    for index, clause in enumerate(soft_clauses):
        relaxation_variables.append(Bool(f"r_{index}"))
        relaxed_clauses.append(Or(clause, relaxation_variables[index]))
        solver.assert_and_track(relaxed_clauses[index], f"{index}")

    solver.add(AtMost(*relaxation_variables, 0))

    while solver.check() != sat:
        print("unsat")
        cost = cost + 1

        core = []
        for clause in solver.unsat_core():
            core.append(int(str(clause)))

        cover = 1
        for c in unsat_cores:
            if max([True if el not in core else False for el in c]):
                continue
            cover = cover + 1
        unsat_cores = []
        at_most.append(AtMost(*core, cover))
        at_least.append(AtLeast(*core, cover))

        solver = Optimize()
        solver.assert_exprs(hard_clauses)
        for index, clause in enumerate(soft_clauses):
            solver.assert_and_track(clause, f"{index}")

        for constraint in at_most:
            solver.add(constraint)
        
    return solver.model(), cost


# MaxSAT simple incremental Algorithm
def max_sat_inc(hard_clauses, soft_clauses):
    # Check if formula is satisfiable
    solver = Optimize()
    solver.add(hard_clauses)
    if solver.check() != sat:
        raise Exception("UNSATISFIABLE")

    # Optimize soltion
    relaxed_clauses = []
    relaxation_variables = []
    cost = 0
    unsat_cores = []
    at_least = []

    solver = Optimize()
    solver.assert_exprs(hard_clauses)
    for index, clause in enumerate(soft_clauses):
        relaxation_variables.append(Bool(f"r_{index}"))
        relaxed_clauses.append(Or(clause, relaxation_variables[index]))
        solver.assert_exprs(relaxed_clauses[index])

    solver.add(AtMost(*relaxation_variables, cost))

    while solver.check() != sat:
        print("unsat")
        cost = cost + 1

        solver = Optimize()
        solver.assert_exprs(hard_clauses)
        solver.assert_exprs(relaxed_clauses)
        solver.add(AtMost(*relaxation_variables, cost))
    
    return solver.model(), cost


def main():
    n, m, mr, ns, mc, d_number, f = parse_input(sys.stdin.read())

    solver = Optimize()
    placement = [(Int(f"{i}_sw"), Int(f"{i}_st")) for i in range(1, n + 1)]
    
    # Constraint 1.1
    for index, (sw, st) in enumerate(placement):
        # Constraint 1.1.1
        solver.add(And(1 <= st, 1 <= sw, sw <= m))
        clause = []
        for switch in range(1, m + 1):
            clause.append(sw != switch if mc[switch - 1] < mr[index] else Implies(sw == switch, st <= ns[switch - 1]))
        solver.add(And(*clause))
    
    # Constraint 1.2
    for switch in range(1, m + 1):
        for stage in range(1, ns[switch - 1] + 1):
            parcels = []
            for rule, (sw, st) in enumerate(placement):
                parcels.append(If(And(sw == switch, st == stage), mr[rule], 0))
            # Constraint 1.2.1
            solver.add(0 < Sum(*parcels))
            solver.add(Sum(*parcels) <= mc[switch - 1])

    switch_positions = [i for i in range(1, m + 1)]

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
        solver.add(
            [
                Xor(
                    precedences[preceding_switch][succeeding_switch],
                    precedences[succeeding_switch][preceding_switch]
                )
                for preceding_switch in range(1, m + 1)
                for succeeding_switch in range(1, m + 1)
                if preceding_switch != succeeding_switch
            ]
        )

        # Constraint 1.3.2
        for preceding_rule, succeeding_rule in f:
            for preceding_switch in range(1, m + 1):
                for succeeding_switch in range(1, m + 1):
                    if preceding_switch != succeeding_switch:
                        solver.add(
                            Implies(
                                And(
                                    placement[preceding_rule - 1][0] == preceding_switch,
                                    placement[succeeding_rule - 1][0] == succeeding_switch
                                ),
                                precedences[preceding_switch][succeeding_switch]
                            )
                        )

    # Objective function minimization (soft clauses)
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

    ##############################################################################################
    # print results ##############################################################################
    ##############################################################################################

    start = time.time()
    # Through trial and error this was found to be the fastest implementation between all those 
    # tried, see above for the different algorithms tested (several variables influence these
    # results, e.g. z3's Solver::assert_and_track is much slower than a simple 
    # Solver::assert_exprs)
    model, recirculations = max_sat_inc(solver.assertions(), soft_clauses)
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
