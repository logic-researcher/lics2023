package Test;

import com.google.gson.Gson;
import org.semanticweb.HermiT.ReasonerFactory;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tool.Tool;

import java.util.concurrent.*;

public class HermitMultiThread {
    final private static Logger logger = LoggerFactory.getLogger(HermitMultiThread.class);
    final private ThreadLocal<OWLReasoner> localReasoner;
    public HermitMultiThread(OWLOntology ontology){
        localReasoner = ThreadLocal.withInitial(() -> new ReasonerFactory().createReasoner(ontology));
    }

    public void initialReasoner(OWLReasoner reasoner){
        localReasoner.set(reasoner);
    }
    public boolean entailCheck(OWLOntology checkedOnto, OWLReasoner reasoner){
//        localReasoner.set(reasoner);
//        logger.info("Start load reasoner");
//        reasoner = localReasoner.get();
//        logger.info("End load reasoner");
        int cnt = 0;
        logger.info("Start entailment checking");
        for(OWLLogicalAxiom axiom: checkedOnto.getLogicalAxioms()){
            reasoner.isEntailed(axiom);
            cnt++;
            if(cnt >= 10)
                break;
        }
        logger.info("End entailment checking");
        return true;
    }

    static public void main(String[] args) throws OWLOntologyCreationException, InterruptedException {
//        OWLOntology kb = Tool.loadOntology("./data/SNOMED CT1/ontology_201601.owl");
        OWLOntology kb = Tool.loadOntology("./data/test_forgetting/Oxford-ISG/PARTIII/00518.owl");

        OWLOntology checkedOnto = Tool.loadOntology("./data/SNOMED CT1/ontology_201607.owl");
        logger.info("Finished load ontology");
        HermitMultiThread hermitMultiThread = new HermitMultiThread(kb);
        OWLReasoner reasoner = new ReasonerFactory().createReasoner(kb);
        Gson gson = new Gson();
        logger.info("Start copy reasoner");
        OWLReasoner reasonerCopy = gson.fromJson(gson.toJson(reasoner), OWLReasoner.class);
        logger.info("End copy reasoner");
        ExecutorService executors = Executors.newFixedThreadPool(2);

        Thread t1 = new Thread(() -> {
//            hermitMultiThread.initialReasoner(reasoner);
            hermitMultiThread.entailCheck(checkedOnto, reasoner);
        });
        t1.start();

        Thread.sleep(3000);
        Thread t2 = new Thread(() -> {
//            hermitMultiThread.initialReasoner(reasoner);
            hermitMultiThread.entailCheck(checkedOnto, reasonerCopy);
        });
        t2.start();
//        Future<Boolean> future = executors.submit(() -> hermitMultiThread.entailCheck(checkedOnto));
//        executors.submit(() -> hermitMultiThread.entailCheck(checkedOnto));
//        hermitMultiThread.logger.info("Thread t started");
//        t.join(100000);
//        if(t.isAlive()){
//            t.stop();
//            hermitMultiThread.logger.info("Has stopped!");
//
//        }

//        try{
//            t.join(1000);
////            future.get(1, TimeUnit.SECONDS);
//        }catch (InterruptedException e){
//            System.out.println(e.getMessage());
//            t.stop();
//            hermitMultiThread.logger.info("executed stop!");
////            hermitMultiThread.logger.info("ready for return!");
//            return;
//        }
//        executors.shutdown();
    }


}
