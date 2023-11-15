#!/usr/bin/python3
# alc23 - 13 - project2 
# DO NOT remove or edit the lines above. Thank you.

# import time
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


def decide_merger(connection_strength):
    # Get max strength of connection between any two communities
    first_community, temp = \
        max(enumerate((max(enumerate(vec), key=itemgetter(1))) for vec in connection_strength), key=itemgetter(1, 1))
    second_community, strength = temp
    # get new partition connection strength vector
    first_strength_vector = connection_strength.pop(second_community if first_community < second_community else first_community)
    second_strength_vector = connection_strength.pop(first_community if first_community < second_community else second_community)
    strength_vector = [x + y for x, y in zip(first_strength_vector, second_strength_vector)]
    strength_vector.pop(second_community if first_community < second_community else first_community)
    strength_vector.pop(first_community if first_community < second_community else second_community)
    strength_vector.append(0)
    for community, vector in enumerate(connection_strength):
        first_community_connection = vector.pop(second_community if first_community < second_community else first_community)
        second_community_connection = vector.pop(first_community if first_community < second_community else second_community)
        connection_strength[community].append(first_community_connection + second_community_connection)
    connection_strength.append(strength_vector)
    return first_community, second_community, connection_strength


def partial_soft_clause_smt(hard_clauses, soft_clauses, n, f):
    solver = hard_clauses

    if not solver.check():
        raise Exception("UNSATISFIABLE")

    hard_assertions = solver.assertions()
    assertions = []
    partition, connection = soft_clause_partitioning(n, f)
    lambdas = [0] * len(partition)

    new_solver = Optimize()

    for community, clauses in enumerate(partition):
        soft = [soft_clauses[int(index)] for index in clauses]
        new_solver.assert_exprs(hard_assertions)
        new_solver.add_soft(soft)
        while new_solver.check() != sat:
            r = []
            for i, soft_clause in enumerate(soft):
                if not is_true(new_solver.model().eval(soft_clause)):
                    r.append(Bool(f"r_{community}_{i}"))
                    soft.pop(i)
                    soft.append(Or(soft_clause, r[-1]))
            lambdas[community] = lambdas[community] + 1
            new_solver = Optimize()
            new_solver.assert_exprs(hard_assertions)
            new_solver.add_soft(soft)
            new_solver.add_soft(AtMost(r, lambdas[community]))
        assertions.append(new_solver.assertions())
        new_solver = Optimize()

    # c = 0
    while len(partition) > 1:
        first_community, second_community, connection = decide_merger(connection)
        first_clause_set = partition.pop(second_community if first_community < second_community else first_community)
        first_set_assertions = assertions.pop(second_community if first_community < second_community else first_community)
        second_clause_set = partition.pop(first_community if first_community < second_community else second_community)
        second_set_assertions = assertions.pop(first_community if first_community < second_community else second_community)
        new_clause_set = first_clause_set + second_clause_set
        new_solver = Optimize()
        new_solver.assert_exprs(hard_assertions)
        new_solver.assert_exprs(first_set_assertions)
        new_solver.assert_exprs(second_set_assertions)
        new_solver.add_soft([soft_clauses[int(index)] for index in new_clause_set])
        while new_solver.check() != sat:
            print("unsat")
            r = []
            for i, soft_clause in enumerate(soft):
                if not is_true(new_solver.model().eval(soft_clause)):
                    r.append(Bool(f"r_{c}_{i}"))
                    soft.pop(i)
                    soft.append(Or(soft_clause, r[-1]))
            lambdas[c] = lambdas[c] + 1
            new_solver = Optimize()
            new_solver.assert_exprs(hard_assertions)
            new_solver.add_soft(soft)
            new_solver.add_soft(AtMost(r, lambdas[c]))
        assertions.append(new_solver.assertions())
        partition.append(new_clause_set)
        # c += 1
        # print("merge: ", c, " / ", "length: ", len(partition))
    return new_solver.model()


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

    # Objective function minimization
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

    ##############################################################################################
    # print results ##############################################################################
    ##############################################################################################

    # start = time.time()
    model = partial_soft_clause_smt(solver, soft_clauses, n, f)
    # print(time.time() - start)

    recirculations = 0
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

    # Count Recirculations
    for switch in solution:
        previous_stages = []
        for current_stage in switch:
            for index, rule_1 in enumerate(current_stage):
                for rule_2 in current_stage[(index + 1):]:
                    if rule_1 != rule_2:
                        if ([rule_1, rule_2] in f) or ([rule_2, rule_1] in f):
                            recirculations = recirculations + 1
            if previous_stages is not Empty:
                for rule_1 in current_stage:
                    for rule_2 in previous_stages:
                        if [rule_1, rule_2] in f:
                            recirculations = recirculations + 1
            for rule in current_stage:
                previous_stages.append(rule)

    print(generate_output(recirculations, switch_positions, solution), end="")

    ##############################################################################################


if __name__ == "__main__":
    main()
