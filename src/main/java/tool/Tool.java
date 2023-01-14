package tool;

import org.eclipse.rdf4j.model.vocabulary.OWL;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.util.Construct;
import org.semanticweb.owlapi.util.DLExpressivityChecker;
import org.semanticweb.owlapi.util.Languages;

import java.io.*;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class Tool {
    public static OWLOntology loadOntology(String filePath) throws OWLOntologyCreationException {
        return loadOntology(new File(filePath));

    }
    public static OWLOntology loadOntology(File file) throws OWLOntologyCreationException {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        return manager.loadOntologyFromOntologyDocument(file);

    }

    public static void getTimeout() throws IOException {
        try(BufferedReader br = new BufferedReader(new FileReader("log.txt"));
            BufferedWriter bw = new BufferedWriter(new FileWriter("timeout.txt"))){
            String line = null;
            String ontoName;
            while((line = br.readLine()) != null){
                if(line.contains("BioPortal") || line.contains("Oxford-ISG")){
                    ontoName = line.substring(line.indexOf("-") + 2);
                    line = br.readLine();
                    if(line.contains("Time out!")){
                        bw.write(ontoName + "\n");
                    }
                }
            }
        }
    }

    public static boolean isELHAxiom(OWLLogicalAxiom axiom){
        if(axiom instanceof OWLSubClassOfAxiom){
            return isELHExpression(((OWLSubClassOfAxiom) axiom).getSubClass())
                    && isELHExpression(((OWLSubClassOfAxiom) axiom).getSuperClass());
        }else if(axiom instanceof OWLSubObjectPropertyOfAxiom){
            OWLSubObjectPropertyOfAxiom owlOP = (OWLSubObjectPropertyOfAxiom) axiom;
            return isRoleName(owlOP.getSubProperty()) && isRoleName(owlOP.getSuperProperty());

        }else if(axiom instanceof OWLEquivalentClassesAxiom){
            OWLEquivalentClassesAxiom owlECA = (OWLEquivalentClassesAxiom) axiom;
            for(OWLClassExpression operand: owlECA.getOperandsAsList()){
                if(!isELHExpression(operand)){
                    return false;
                }
            }
            return true;
        }else if(axiom instanceof OWLObjectPropertyDomainAxiom){
            OWLObjectPropertyDomainAxiom owlOPDA = (OWLObjectPropertyDomainAxiom) axiom;
            return isELHExpression(owlOPDA.getDomain()) && isRoleName(owlOPDA.getProperty());

        }else if(axiom instanceof OWLEquivalentObjectPropertiesAxiom){
            OWLEquivalentObjectPropertiesAxiom owlEOPA = (OWLEquivalentObjectPropertiesAxiom) axiom;
            for(OWLObjectPropertyExpression role: owlEOPA.getOperandsAsList()){
                if(!isRoleName(role)){
                    return false;
                }
            }
            return true;
        }else{
            return false;
        }
    }
    public static boolean isELHExpression(OWLClassExpression concept){
        if(concept.isOWLThing()){
            return true;
        }
        if(concept instanceof OWLClass){
            return true;
        }else if(concept instanceof OWLObjectIntersectionOf){
            OWLObjectIntersectionOf owlOBIO = (OWLObjectIntersectionOf) concept;
            for(OWLClassExpression subConcept: owlOBIO.getOperands()){
                if(!isELHExpression(subConcept)){
                    return false;
                }
            }
            return true;
        }else if(concept instanceof OWLObjectSomeValuesFrom){
            OWLObjectSomeValuesFrom owlOSVF = (OWLObjectSomeValuesFrom) concept;
            OWLObjectPropertyExpression role = owlOSVF.getProperty();
            if(isRoleName(role)){
                return isELHExpression(owlOSVF.getFiller());
            }
            return false;
        }
        else{
            return false;
        }
    }

    public static boolean isRoleName(OWLObjectPropertyExpression role){
        return !role.isOWLTopObjectProperty() && role.isOWLObjectProperty();
    }

    public static OWLOntology getELHPart(OWLOntology ontology) throws OWLOntologyCreationException {
        Set<OWLAxiom> elhAxioms = new HashSet<>();
        for(OWLLogicalAxiom axiom: ontology.getLogicalAxioms()){

            if(isELHAxiom(axiom)){
                if(axiom instanceof OWLObjectPropertyDomainAxiom){
                    axiom = ((OWLObjectPropertyDomainAxiom) axiom).asOWLSubClassOfAxiom();
                }
                elhAxioms.add(axiom);
            }
        }
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology ans = manager.createOntology(elhAxioms);
//        DLExpressivityChecker dlExpressivityChecker = new DLExpressivityChecker(Collections.singleton(ans));
//        for(Construct construct: dlExpressivityChecker.getConstructs()){
//            System.out.println(construct.name());
//
//        }

        return ans;
    }

    public static void main(String[] args) throws IOException {
        getTimeout();
    }
}
