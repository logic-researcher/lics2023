package forgetting;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;

import java.io.*;
import java.util.*;


public class SignaturePartition {

    static OWLOntology loadOntology(File file) throws OWLOntologyCreationException {
        OWLOntology owlOntology;
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        try {
            owlOntology = manager.loadOntologyFromOntologyDocument(file);
        }catch (Exception e){
            owlOntology = manager.loadOntologyFromOntologyDocument(file);
        }
        return owlOntology;
    }

    public static Map<String , Set<OWLEntity>> buildSignatureMap(Set<OWLEntity> forgettingSignatures, OWLOntology ontology, Map<String, Set<OWLLogicalAxiom>> signatureAxiomMap){
        Map<String, Set<OWLEntity>> signatureMap = new HashMap<>();
//        Map<String, Set<OWLLogicalAxiom>> signatureAxiomMap = new HashMap<>();
//        for(OWLEntity entity: forgettingSignatures){
//            signatureMap.put(entity.toString(), new HashSet<>());
//        }
        Set<OWLEntity> axiomSignatures;
        Set<OWLEntity> adjacent;
        for(OWLLogicalAxiom axiom: ontology.getLogicalAxioms()){
            axiomSignatures = axiom.getSignature();
            axiomSignatures.retainAll(forgettingSignatures);
            for(OWLEntity signature: axiomSignatures){
                if((adjacent = signatureMap.get(signature.toString())) == null){
                    signatureMap.put(signature.toString(), new HashSet<>());
                    adjacent = signatureMap.get(signature.toString());
                    signatureAxiomMap.put(signature.toString(), new HashSet<>());
                }
                signatureAxiomMap.get(signature.toString()).add(axiom);
                adjacent.addAll(axiomSignatures);
//                signatureMap.get(signature.toString()).addAll(axiomSignatures);

            }
        }
        return signatureMap;
    }

    public static Set<OWLEntity > gatherSignatures(Set<OWLEntity> startSignatures, Map<String, Set<OWLEntity>> signatureMap){
        Set<OWLEntity> ans = new HashSet<>();
        for(OWLEntity key: startSignatures){
            if(signatureMap.get(key.toString()) != null ){
                ans.addAll(signatureMap.get(key.toString()));
                signatureMap.put(key.toString(), null);
            }
        }
        if(!ans.isEmpty() )
            ans.addAll(gatherSignatures(ans, signatureMap));
        return ans;
    }

    public static List<Set<OWLEntity>> partitionSignature(Set<OWLEntity> forgettingSignatures, OWLOntology ontology,
                                                          Map<String, Set<OWLLogicalAxiom>> signatureAxiomMap) throws OWLOntologyCreationException {
//        Map<String, Set<OWLLogicalAxiom>> signatureAxiomMap = new HashMap<>();

        Map<String, Set<OWLEntity>> signatureMap = buildSignatureMap(forgettingSignatures, ontology, signatureAxiomMap);
        List<Set<OWLEntity>> partitions = new ArrayList<>();
//        List<Set<OWLLogicalAxiom>> axiomsPartitions = new ArrayList<>();
        for(String key: signatureMap.keySet()){
            if(signatureMap.get(key) != null){
                partitions.add(gatherSignatures(signatureMap.get(key), signatureMap));
            }
        }
        return partitions;

    }

    public  static void main(String[] args) throws OWLOntologyCreationException, IOException {

    }

}
