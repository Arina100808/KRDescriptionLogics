from py4j.java_gateway import JavaGateway
from itertools import combinations
import argparse

"""
Run the following command in a terminal before running the code:
java -jar dl4python-0.1-jar-with-dependencies.jar
"""


def copy_elements(elements):
    copied_elements = {element: {prop: set(value) if isinstance(value, set) else value
                                 for prop, value in elements[element].items()}
                       for element in elements}
    return copied_elements


class Ontology:
    def __init__(self, ontology_file):
        # connect to the java gateway of dl4python
        self.gateway = JavaGateway()
        # get a formatter to print in nice DL format
        self.formatter = self.gateway.getSimpleDLFormatter()
        # load an ontology from a file
        self.ontology = self.gateway.getOWLParser().parseFile(ontology_file)
        # convert to binary conjunctions
        self.gateway.convertToBinaryConjunctions(self.ontology)

    def get_tbox_axioms(self, replace_equivalent=False):
        # get the TBox axioms
        tbox = self.ontology.tbox()
        axioms = tbox.getAxioms()
        if replace_equivalent:
            elFactory = self.gateway.getELFactory()
            final_axioms = set()
            for axiom in axioms:
                axiomType = axiom.getClass().getSimpleName()
                if axiomType == "EquivalenceAxiom":
                    concepts = axiom.getConcepts()
                    conceptA = concepts[0]
                    conceptB = concepts[1]
                    gciA = elFactory.getGCI(conceptA, conceptB)
                    gciB = elFactory.getGCI(conceptB, conceptA)
                    final_axioms.add(gciA)
                    final_axioms.add(gciB)
                else:
                    final_axioms.add(axiom)
        else:
            final_axioms = axioms
        return final_axioms


class ELReasoner:
    def __init__(self, ontology, class_name):
        self.ontology = ontology
        self.class_name = class_name

    def lecture_example_tbox(self):
        elFactory = self.ontology.gateway.getELFactory()

        conceptA = elFactory.getConceptName("A")
        conceptB = elFactory.getConceptName("B")
        conceptC = elFactory.getConceptName("C")
        conceptD = elFactory.getConceptName("D")
        conceptE = elFactory.getConceptName("E")
        conceptF = elFactory.getConceptName("F")
        conceptG = elFactory.getConceptName("G")

        role_r = elFactory.getRole("r")
        role_s = elFactory.getRole("s")

        conjunctionCG = elFactory.getConjunction(conceptC, conceptG)

        existential_rC = elFactory.getExistentialRoleRestriction(role_r, conceptC)
        existential_sE = elFactory.getExistentialRoleRestriction(role_s, conceptE)
        existential_sF = elFactory.getExistentialRoleRestriction(role_s, conceptF)
        existential_rCG = elFactory.getExistentialRoleRestriction(role_r, conjunctionCG)

        conjunctionDsE = elFactory.getConjunction(conceptD, existential_sE)

        a1 = elFactory.getGCI(conceptA, existential_rC)
        a2 = elFactory.getGCI(conceptC, conjunctionDsE)
        a3 = elFactory.getGCI(conceptE, conceptF)
        a4 = elFactory.getGCI(existential_sF, conceptG)
        a5 = elFactory.getGCI(existential_rCG, conceptB)

        return {a1, a2, a3, a4, a5}

    def print_elements(self, elements):
        for element in elements.keys():
            print(element)
            for prop in elements[element]:
                if prop == "concepts" or prop == "initial_concepts":
                    print(f"    {prop}: {[self.ontology.formatter.format(x) for x in elements[element][prop]]}")
                else:
                    print(f"    {prop}: {elements[element][prop]}")

    def get_input(self, d, tbox):
        elFactory = self.ontology.gateway.getELFactory()
        elementary = ["ConceptName", "TopConcept$"]
        input_concepts = set()
        input_concepts.update(list(d))
        input_concepts.add(elFactory.getTop())
        input_concepts.update(tbox)
        while len(tbox) != 0:
            new_tbox = set()
            processed_concepts = set()
            for concept in tbox:
                conceptType = concept.getClass().getSimpleName()
                if conceptType in elementary:
                    input_concepts.add(concept)
                else:
                    if conceptType == "ExistentialRoleRestriction":
                        first = concept.role()
                        second = concept.filler()
                    elif conceptType == "ConceptConjunction":
                        first = concept.getConjuncts()[0]
                        second = concept.getConjuncts()[1]
                    elif conceptType == "GeneralConceptInclusion":
                        first = concept.lhs()
                        second = concept.rhs()
                    else:
                        continue
                    input_concepts.add(first)
                    input_concepts.add(second)
                    new_tbox.add(first)
                    new_tbox.add(second)
                processed_concepts.add(concept)
            # Add elements to tbox after the iteration is complete
            tbox.update(new_tbox)
            # Remove processed elements from tbox
            tbox = new_tbox

        return input_concepts

    def apply_completion_rules(self, d, elements, tbox, input_concepts):

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
        # ⊓-rule 1: If d has C ⊓ D assigned, assign also C and D to d
        # only concepts from the input are assigned
        for concept in current_elements[d]["concepts"]:
            conceptType = concept.getClass().getSimpleName()
            if conceptType == "ConceptConjunction":
                for conjunct in concept.getConjuncts():
                    if conjunct in input_concepts:
                        elements[d]["concepts"].add(conjunct)
                        changed = True
                        if (conjunct not in set().union(*(info["initial_concepts"]
                                                          for element, info in elements.items()))):
                            elements[d]["initial_concepts"].add(conjunct)
        if changed:
            current_elements = copy_elements(elements)
        changed = False
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
        # ∃-rule 1: If d has ∃r.C assigned
        # only concepts from the input are assigned
        for concept in current_elements[d]["concepts"]:
            conceptType = concept.getClass().getSimpleName()
            if conceptType == "ExistentialRoleRestriction":
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

    def start(self, mode="test"):
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

        i = 0
        total = 0
        changed = True
        while changed:
            i += 1
            current_elements = copy_elements(elements)
            for d in elements.keys():
                total += 1
                current_elements = self.apply_completion_rules(d, current_elements, tbox, input_concepts)
                if mode == "lecture_example":
                    print(f"\n--- {i}.{total}. After applying rules to {d} ---")
                    self.print_elements(current_elements)
            changed = (elements != current_elements)
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
    reasoner = ELReasoner(ontology=ontology, class_name=cl_name)
    result_subsumers, n_iterations = reasoner.start(mode=mode)

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
