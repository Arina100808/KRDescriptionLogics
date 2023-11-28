from el_reasoner import Ontology, ELReasoner
from el_reasoner_second import ELReasoner2
from elk import test_elk, reformat
from py4j.java_gateway import JavaGateway
from os import listdir
from os.path import isfile, join
import time
import csv

results_file = 'results.csv'


def add_row_to_csv(file_path, data):
    with open(file_path, 'a', newline='') as csvfile:
        fieldnames = ['file', 'class', 'reasoner', 'iterations', 'time', 'n_subsumers', 'subsumers']
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)

        # If the file is empty, write the header
        if csvfile.tell() == 0:
            writer.writeheader()

        writer.writerow(data)


def find_subsumers(start_reasoner, ont_name, cl_name):
    start_time = time.time()
    result_subsumers, n_iterations = start_reasoner()
    end_time = time.time()
    execution_time = round(end_time - start_time, 4)
    result_subsumers = reformat(result_subsumers)
    print(f"Subsumers for {ont_name} / {cl_name}:")
    print(f"({len(result_subsumers)} in total)")
    print(result_subsumers)
    print(f"Iterations: {n_iterations}")
    print(f"Time: {execution_time}")
    return result_subsumers, n_iterations, execution_time


def main():
    gateway = JavaGateway()
    parser = gateway.getOWLParser()
    path = "TestOntologies/"
    test_files = [path + f for f in listdir(path) if isfile(join(path, f))]
    for file in test_files:
        ontology = parser.parseFile(file)
        gateway.convertToBinaryConjunctions(ontology)
        conceptNames = ontology.getConceptNames()
        n_names = len(conceptNames)
        n = 0
        if n_names < 150:
            n = 30
        elif n_names < 300:
            n = 20
        elif n_names < 600:
            n = 10
        elif n_names > 900:
            n = 1
        conceptNames = reformat(conceptNames)[:n]
        ontology_file = file
        ontology = Ontology(ontology_file=ontology_file)
        ontology_name = file.split('/')[1].split('.')[0]
        for class_name in conceptNames:
            reasoner_1 = ELReasoner(ontology=ontology, class_name=class_name)
            reasoner_2 = ELReasoner2(ontology=ontology, class_name=class_name)
            print("--------------------- ELK ---------------------")
            s3 = test_elk(ontology_file=ontology_file, class_name=class_name)
            print(f"Subsumers for {ontology_name} / {class_name}:")
            print(f"({len(s3)} in total)")
            print(s3)
            data_elk = {'file': ontology_file,
                        'class': class_name,
                        'reasoner': 3,
                        'iterations': None,
                        'time': None,
                        'n_subsumers': len(s3),
                        'subsumers': s3}
            add_row_to_csv(results_file, data_elk)
            print("----------------- REASONER 1 -----------------")
            s1, i1, t1 = find_subsumers(reasoner_1.start, ontology_name, class_name)
            data_1 = {'file': ontology_file,
                      'class': class_name,
                      'reasoner': 1,
                      'iterations': i1,
                      'time': t1,
                      'n_subsumers': len(s1),
                      'subsumers': s1}
            add_row_to_csv(results_file, data_1)
            print("----------------- REASONER 2 -----------------")
            s2, i2, t2 = find_subsumers(reasoner_2.start_2, ontology_name, class_name)
            data_2 = {'file': ontology_file,
                      'class': class_name,
                      'reasoner': 2,
                      'iterations': i2,
                      'time': t2,
                      'n_subsumers': len(s2),
                      'subsumers': s2}
            add_row_to_csv(results_file, data_2)


if __name__ == "__main__":
    main()
