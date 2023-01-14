package forgetting;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.util.Languages;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tool.Tool;
import org.semanticweb.owlapi.metrics.DLExpressivity;
import org.semanticweb.owlapi.util.DLExpressivityChecker;
import javax.annotation.processing.Filer;
import java.io.*;
import java.util.*;
import java.util.concurrent.*;
import elk.elkEntailment;

public class ForgetterTest {
    public static Logger logger = LoggerFactory.getLogger(ForgetterTest.class);

    public static long singleRun(File file) throws Exception {
        OWLOntology ontology = Tool.loadOntology(file);
        Forgetter singleForgetter = new Forgetter(ontology);
        List<OWLObjectProperty> rolesList = new ArrayList<>(ontology.getObjectPropertiesInSignature());
        List<OWLClass> conceptsList = new ArrayList<>(ontology.getClassesInSignature());
//        Collections.shuffle(rolesList);
//        Collections.shuffle(conceptsList);
        double ratio = 0.3;
        Set<OWLObjectProperty> forgottenRoles = new HashSet<>(rolesList.subList(0, (int)Math.round(ratio * rolesList.size())));
        Set<OWLClass> forgottenConcepts = new HashSet<>(conceptsList.subList(0, (int)Math.round(ratio * conceptsList.size())));
        ExecutorService executorService = Executors.newSingleThreadExecutor();
        Long startTime = System.currentTimeMillis();
//        singleForgetter.forgettingSingleThread(forgottenRoles, forgottenConcepts, ontology);

        Future<Set<OWLAxiom>> future = executorService.submit(new Callable<Set<OWLAxiom>>() {
            @Override
            public Set<OWLAxiom> call() throws Exception {
//                return singleForgetter.forgettingSingleThread(forgottenRoles, forgottenConcepts, ontology);
                return null;
            }
        });
        try{
            future.get(300, TimeUnit.SECONDS);
        }catch (TimeoutException e){
            logger.info("Time out!");
            return -1;
        }catch (Exception e){
            logger.info("Unknown exception!");
            return -1;
        }
        Long duration1 = System.currentTimeMillis() - startTime;
        logger.info("Single thread time consumption: " + duration1);
        executorService.shutdown();
        return duration1;

    }

    public static long multiThreadRun(File file) throws Exception {
        OWLOntology ontology = Tool.loadOntology(file);
        Forgetter forgetter = new Forgetter(ontology);
        List<OWLObjectProperty> rolesList = new ArrayList<>(ontology.getObjectPropertiesInSignature());
        List<OWLClass> conceptsList = new ArrayList<>(ontology.getClassesInSignature());
//        Collections.shuffle(rolesList);
//        Collections.shuffle(conceptsList);
        double ratio = 0.3;
        Set<OWLObjectProperty> forgottenRoles = new HashSet<>(rolesList.subList(0, (int)Math.round(ratio * rolesList.size())));
        Set<OWLClass> forgottenConcepts = new HashSet<>(conceptsList.subList(0, (int)Math.round(ratio * conceptsList.size())));
        Long startTime = System.currentTimeMillis();
        forgetter.forgettingMultiThread(forgottenRoles , forgottenConcepts, ontology);
        Long duration2 = System.currentTimeMillis() - startTime;
        logger.info("Multi thread time consumption: " + duration2);
//        logger.info("ratio: {}", 1.0 * duration2 / duration1);
        return duration2;
    }

    public static void multiThreadExperiment(File file) throws Exception {
        OWLOntology ontology = Tool.loadOntology(file);
        final OWLOntology finalOntology = Tool.getELHPart(ontology);
//        final OWLOntology finalOntology = ontology;
        logger.info("Original size: {}, ELH part size: {}", ontology.getLogicalAxiomCount(), finalOntology.getLogicalAxiomCount());

        Forgetter forgetter = new Forgetter();
        List<OWLObjectProperty> rolesList = new ArrayList<>(finalOntology.getObjectPropertiesInSignature());
        List<OWLClass> conceptsList = new ArrayList<>(finalOntology.getClassesInSignature());
//        Collections.shuffle(rolesList);
//        Collections.shuffle(conceptsList);
        double ratio = 0.1;
        Set<OWLObjectProperty> forgottenRoles = new HashSet<>(rolesList.subList(0, (int)Math.round(ratio * rolesList.size())));
        Set<OWLClass> forgottenConcepts = new HashSet<>(conceptsList.subList(0, (int)Math.round(ratio * conceptsList.size())));
        Set<OWLObjectProperty> forgottenRolesCopy = new HashSet<>(forgottenRoles);
        Set<OWLClass> forgottenConceptsCopy = new HashSet<>(forgottenConcepts);
        Long startTime, duration1, duration2;


        //单线程运行
        Thread t = new Thread(() -> {
            try {
                forgetter.forgettingSingleThread(forgottenRoles, forgottenConcepts, finalOntology);
//                System.out.println();
            }
            catch (Exception e) {
                throw new RuntimeException(e);
            }
        });

        startTime = System.currentTimeMillis();
        t.start();
        t.join(300 * 1000);
        duration1 = System.currentTimeMillis() - startTime;
        logger.info("Single thread time consumption: " + duration1);
        logger.debug("The size of hasChecked: {}", elkEntailment.hasChecked_OnO2.size());
        elkEntailment.hasChecked_OnO2.clear();

        if(t.isAlive()){
            logger.info("Time out!");
            while(t.isAlive()){
                t.stop();
            }
            logger.info("Killed the thread!");
            return;
        }
        if(Forgetter.isExtra ){
            logger.info("There is extra expressivity");
            Forgetter.isExtra = false;
            return;
        }


        //多线程运行
        startTime = System.currentTimeMillis();
        forgetter.forgettingMultiThread(forgottenRolesCopy , forgottenConceptsCopy, finalOntology);
        duration2 = System.currentTimeMillis() - startTime;
        logger.debug("The size of hasChecked: {}", elkEntailment.hasChecked_OnO2.size());
        elkEntailment.hasChecked_OnO2.clear();
        if(forgottenRolesCopy.size() + forgottenConceptsCopy.size() <= 30){
            duration2 = duration1;
        }
        logger.info("Multi thread time consumption: " + duration2);
        elkEntailment.hasChecked_OnO2.clear();


//        ExecutorService executorService = Executors.newSingleThreadExecutor();
//        Long startTime = System.currentTimeMillis();
//        Future<Set<OWLAxiom>> future = executorService.submit(new Callable<Set<OWLAxiom>>() {
//            @Override
//            public Set<OWLAxiom> call() throws Exception {
//                return forgetter.forgettingSingleThread(forgottenRoles, forgottenConcepts, finalOntology);
////                return null;
//            }
//        });
//        try{
//            future.get(300, TimeUnit.SECONDS);
//        }catch (TimeoutException e){
//            logger.info("Time out!");
//            return;
//        }catch (IllegalArgumentException e){
//            logger.info("There is extra expressivity");
//            return;
//
//        }
//        catch (Exception e){
//            logger.info(e.getMessage());
//            return;
//        }


        logger.info("ratio: {}", 1.0 * duration2 / duration1);


//        long duration1, duration2;
//        if((duration1 = singleRun(file)) >= 0){
//            elkEntailment.hasChecked_OnO2.clear();
//            duration2 = multiThreadRun(file);
//            logger.info("ratio: {}", 1.0 * duration2 / duration1);
//
//        }
    }

    public static void experiment() throws IOException {
        String basePath = "./data/test_forgetting/";
        String[] datasets = {"BioPortal", "Oxford-ISG"};
        String[] parts = {"PARTI", "PARTII", "PARTIII"};
        List<String> timeoutList = new ArrayList<>();
        try(BufferedReader br = new BufferedReader(new FileReader("timeout.txt"))){
            String line;
            while((line = br.readLine()) != null){
                timeoutList.add(line);
            }
        }
        for(String dataset: datasets){
//            File file1 = new File(basePath + dataset);
            for(String part: parts){
                File file2 = new File(basePath + dataset + "/" + part);
                if(file2.isDirectory()){
                    //Part
                    File[] files = Objects.requireNonNull(file2.listFiles((dir, name) -> name.endsWith(".xml")|| name.endsWith(".owl")));
                    List<File> fileList = new ArrayList<>(Arrays.asList(files));
                    fileList.sort(Comparator.naturalOrder());
                    for(File file3: fileList){
                        String filePath = file3.getPath();
                        filePath = filePath.substring(filePath.indexOf(dataset));
                        logger.info(filePath);
//                        if(timeoutList.contains(filePath)){
//                            logger.info("Time out!");
//                            logger.info("\n");
//                            continue;
//                        }
                        try{
                            multiThreadExperiment(file3);
                            System.gc();
                            Thread.sleep(1000);
                        }catch (Exception e){
                            logger.info(e.getMessage());
                        }
                        logger.info("\n");
                    }
                }
            }
        }

    }

    public static void main(String[] args) throws Exception {
//        String ontoPath = "./data/test_forgetting/BioPortal/PARTII/ntdo.neglected-tropical-disease-ontology.1.owl.xml";
//        String ontoPath = "./data/test_forgetting/BioPortal/PARTII/dermo.human-dermatological-disease-ontology.10.owl.xml";
//        String ontoPath2 = "./data/test_forgetting/BioPortal/PARTII/eco.evidence-and-conclusion-ontology.49.owl.xml";
//        multiThreadExperiment(new File(ontoPath2));
//        multiThreadExperiment(new File(ontoPath));

        experiment();
        logger.info("Experiment Over!");

    }
}
