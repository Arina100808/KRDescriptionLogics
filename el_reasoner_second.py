from itertools import combinations
from collections import deque
import argparse
from el_reasoner import copy_elements, Ontology, ELReasoner

"""
Run the following command in a terminal before running the code:
java -jar dl4python-0.1-jar-with-dependencies.jar

Second algorithm:
- applies 2 rules in 1 "for" loop instead of 2 separate loops
- uses a double ended queue for processing elements
"""


def conjunction_rule_1(input_concepts, elements, d, concept):
    new_concepts_conjuncts = set()
    changed = False
    for conjunct in concept.getConjuncts():
        if conjunct in input_concepts:
            elements[d]["concepts"].add(conjunct)
            new_concepts_conjuncts.add(conjunct)
            changed = True
            if (conjunct not in set().union(*(info["initial_concepts"]
                                              for element, info in elements.items()))):
                elements[d]["initial_concepts"].add(conjunct)
    return elements, new_concepts_conjuncts, changed


def existential_rule_1(input_concepts, elements, current_elements, d, concept):
    new_concepts_existential = set()
    changed = False
    role = concept.role()
    filler = concept.filler()
    if f"{role}_successor" not in current_elements[d]:
        elements[d][f"{role}_successor"] = set()
        changed = True
    successor_found = False
    # 1. If there is an element e with initial concept C assigned, make
    # e the r-successor of d.
    for e in current_elements.keys():
        if filler in current_elements[e]["initial_concepts"]:
            elements[d][f"{role}_successor"].add(e)
            successor_found = True
            changed = True
    # 2. Otherwise, add a new r-successor to d, and assign to it as
    # initial concept C.
    if not successor_found and filler in input_concepts:
        new_element = f"d{len(elements.keys())}"
        elements[d][f"{role}_successor"].add(new_element)
        elements[new_element] = {}
        elements[new_element]["initial_concepts"] = {filler}
        elements[new_element]["concepts"] = {filler}
        changed = True
    return elements, new_concepts_existential, changed


class ELReasoner2(ELReasoner):

    def apply_completion_rules_2(self, d, elements, tbox, input_concepts):

        elFactory = self.ontology.gateway.getELFactory()

        # ⊤-rule: Add ⊤ to any individual
        # only concepts from the input are assigned
        top_concept = elFactory.getTop()
        if top_concept in input_concepts:
            elements[d]["concepts"].add(top_concept)
            if top_concept not in set().union(*(info["initial_concepts"] for element, info in elements.items())):
                elements[d]["initial_concepts"].add(top_concept)
        current_elements = copy_elements(elements)
        changed = False
        changed_conj, changed_exist = False, False
        new_concepts_conjuncts = set()
        for concept in current_elements[d]["concepts"]:
            conceptType = concept.getClass().getSimpleName()
            # ⊓-rule 1: If d has C ⊓ D assigned, assign also C and D to d
            # only concepts from the input are assigned
            if conceptType == "ConceptConjunction":
                elements, new_concepts_conjuncts, changed_conj = conjunction_rule_1(input_concepts,
                                                                                    elements, d, concept)
            # ∃-rule 1: If d has ∃r.C assigned
            # only concepts from the input are assigned
            elif conceptType == "ExistentialRoleRestriction":
                elements, new_concepts_existential, changed_exist = existential_rule_1(input_concepts,
                                                                                       elements, current_elements,
                                                                                       d, concept)
        new_changed_exist = False
        for new_conjunct in new_concepts_conjuncts:
            new_conjunct_conceptType = new_conjunct.getClass().getSimpleName()
            if new_conjunct_conceptType == "ExistentialRoleRestriction":
                elements, new_concepts_existential, new_changed_exist = existential_rule_1(input_concepts,
                                                                                           elements, current_elements,
                                                                                           d, new_conjunct)
        if changed_conj or changed_exist or new_changed_exist:
            current_elements = copy_elements(elements)
        # ⊓-rule 2: If d has C and D assigned, assign also C ⊓ D to d
        # only concepts from the input are assigned
        for pair in combinations(current_elements[d]["concepts"], 2):
            conjunction_opt1 = elFactory.getConjunction(pair[0], pair[1])
            conjunction_opt2 = elFactory.getConjunction(pair[1], pair[0])
            if conjunction_opt1 in input_concepts:
                elements[d]["concepts"].add(conjunction_opt1)
                changed = True
                if (conjunction_opt1 not in set().union(*(info["initial_concepts"]
                                                          for element, info in elements.items()))):
                    elements[d]["initial_concepts"].add(conjunction_opt1)
            elif conjunction_opt2 in input_concepts:
                elements[d]["concepts"].add(conjunction_opt2)
                changed = True
                if (conjunction_opt2 not in set().union(*(info["initial_concepts"]
                                                          for element, info in elements.items()))):
                    elements[d]["initial_concepts"].add(conjunction_opt2)
        if changed:
            current_elements = copy_elements(elements)
        changed = False
        # ∃-rule 2: If d has an r-successor with C assigned, add ∃r.C to d
        # only concepts from the input are assigned
        for prop in current_elements[d].keys():
            if prop.endswith("successor"):
                successors = current_elements[d][prop]
                role = elFactory.getRole(prop.split('_')[0])
                for successor in successors:
                    for successor_concept in current_elements[successor]["concepts"]:
                        ex_role = elFactory.getExistentialRoleRestriction(role, successor_concept)
                        if ex_role in input_concepts:
                            elements[d]["concepts"].add(ex_role)
                            changed = True
                            if (ex_role not in set().union(*(info["initial_concepts"]
                                                             for element, info in elements.items()))):
                                elements[d]["initial_concepts"].add(ex_role)
        if changed:
            current_elements = copy_elements(elements)
        # ⊑-rule: If d has C assigned and C ⊑ D ∈ T, then also assign D to d
        for axiom in tbox:
            axiomType = axiom.getClass().getSimpleName()
            if axiomType == "GeneralConceptInclusion" and axiom.lhs() in current_elements[d]["concepts"]:
                elements[d]["concepts"].add(axiom.rhs())
                if (axiom.rhs() not in set().union(*(info["initial_concepts"]
                                                     for element, info in elements.items()))):
                    elements[d]["initial_concepts"].add(axiom.rhs())

        return elements

    def start_2(self, mode="test"):
        elFactory = self.ontology.gateway.getELFactory()
        elements = {"d0": {"initial_concepts": {elFactory.getConceptName(self.class_name)},
                           "concepts": {elFactory.getConceptName(self.class_name)}}}
        if mode == "lecture_example":
            tbox = self.lecture_example_tbox()
            input_concepts = self.get_input(elements["d0"]["initial_concepts"], tbox)
        else:
            tbox = self.ontology.get_tbox_axioms(replace_equivalent=True)
            input_concepts = self.ontology.ontology.getSubConcepts()

        if mode == "lecture_example":
            print("Initial state:")
            self.print_elements(elements)

        total = 0
        dequeue = deque()
        dequeue.append(list(elements.keys())[0])
        without_change = 0
        while without_change != len(elements.keys()):
            total += 1
            current_elements = copy_elements(elements)
            current_d = dequeue.pop()
            current_elements = self.apply_completion_rules_2(current_d, current_elements, tbox, input_concepts)
            if mode == "lecture_example":
                print(f"\n--- {total}. After applying rules to {current_d} ---")
                self.print_elements(current_elements)
            for new_element in set(current_elements.keys()) - set(elements.keys()):
                dequeue.append(new_element)
            if elements[current_d]["concepts"] == current_elements[current_d]["concepts"]:
                dequeue.appendleft(current_d)
            else:
                dequeue.append(current_d)
            if current_elements == elements:
                without_change += 1
            else:
                without_change = 0
            elements = current_elements
        subsumers = set()
        for c in elements["d0"]["concepts"]:
            c_type = c.getClass().getSimpleName()
            if c_type == "ConceptName":
                subsumers.add(c)
        return subsumers, total


def main(mode="command_line"):
    """
    :param mode:
        "command_line" (default): subsumers will be printed in a format 1 class name per line
                                  use this command: python el_reasoner.py ONTOLOGY_FILE CLASS_NAME
        All other modes can be used to test the code:
        "pizza": subsumers and its total number will be printed for pizza.owl ontology for '"Margherita"' class name
        "lecture_example": intermediate steps of the algorithm and class name, subsumers and its total number will
                           be printed for an example from Lecture 5 (slide 13)
    """
    ont_file = ""
    cl_name = ""
    if mode == "command_line":
        # Parse command-line arguments
        command_line_parser = argparse.ArgumentParser(description='Compute subsumers for a given class in an ontology.')
        command_line_parser.add_argument('ontology_file', type=str, help='Path to the ontology file')
        command_line_parser.add_argument('class_name', type=str,
                                         help='Name of the class for which to compute subsumers')
        args = command_line_parser.parse_args()
        ont_file = args.ontology_file
        cl_name = args.class_name
    elif mode == "pizza":
        ont_file = "TestOntologies/pizza.owl"
        cl_name = '"Margherita"'
    elif mode == "lecture_example":
        ont_file = "TestOntologies/pizza.owl"
        cl_name = "A"

    # Compute subsumers
    ontology = Ontology(ontology_file=ont_file)
    reasoner = ELReasoner2(ontology=ontology, class_name=cl_name)
    result_subsumers, n_iterations = reasoner.start_2(mode=mode)

    # Display results
    if mode != "command_line":
        print(f"Subsumers for {cl_name}:")
        print(f"({len(result_subsumers)} in total)")

    for concept in result_subsumers:
        print(concept)


if __name__ == "__main__":
    # mode = "pizza" / "lecture_example" / "command_line"
    # command example: python el_reasoner.py TestOntologies/amino-acid.amino-acid-ontology.2.owl.xml I
    main(mode="command_line")
