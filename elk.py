from py4j.java_gateway import JavaGateway

gateway = JavaGateway()
parser = gateway.getOWLParser()
formatter = gateway.getSimpleDLFormatter()
elFactory = gateway.getELFactory()


def reformat(subsumers):
    return [formatter.format(x) for x in subsumers]


def test_elk(ontology_file, class_name):
    ontology = parser.parseFile(ontology_file)
    elk = gateway.getELKReasoner()
    class_name = elFactory.getConceptName(class_name)
    elk.setOntology(ontology)
    subsumers = elk.getSubsumers(class_name).toArray()
    subsumers = reformat(subsumers)
    subsumers.remove('⊤')

    return subsumers
