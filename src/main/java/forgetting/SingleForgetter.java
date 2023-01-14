package forgetting;

import Test.TestForgetting;
import checkfrequency.FChecker;
import concepts.AtomicConcept;
import convertion.Converter;
import extraction.SubsetExtractor;
import formula.Formula;
import inference.DefinerIntroducer;
import inference.Inferencer;
import inference.simplifier;
import org.semanticweb.HermiT.ReasonerFactory;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import roles.AtomicRole;

import java.util.*;

public class SingleForgetter {

    public static  int isExtra = 0;
    static Logger logger = LoggerFactory.getLogger(SingleForgetter.class);

    OWLOntology ontology;
    public SingleForgetter(OWLOntology ontology){
        //初始化线程本地变量
        this.ontology = ontology;
    }

    public SingleForgetter(){

    }


    /**
     *
     * @param roles 要遗忘的role
     * @param concepts 要遗忘的concept
     * @param onto 这个就是读入的onto不需要，传入之前不需要做任何操作，传入后，需要删除不是ELH的axioms，再形成本体。
     * @return
     * @throws Exception
     */
    public List<Formula> Forgetting(Set<OWLObjectProperty> roles, Set<OWLClass> concepts, OWLOntology onto,saveMetrics metrics) throws Exception {
        double tempTime1 = System.currentTimeMillis();
        DefinerIntroducer di = new DefinerIntroducer();
        SubsetExtractor se = new SubsetExtractor();
        Inferencer inf = new Inferencer();
        FChecker fc = new FChecker();
        simplifier sp = new simplifier();
        Converter ct = new Converter();
        int conceptsSize = concepts.size();

        logger.info("The Forgetting Starts:");
        logger.info("The forgetting task is to eliminate [" + concepts.size() + "] concept names and ["
                + roles.size() + "] role names from [" + onto.getLogicalAxiomCount() + "] axioms");

        //提取
        Set<OWLEntity> forgettingSignatures = new HashSet<>();
        forgettingSignatures.addAll(roles);
        forgettingSignatures.addAll(concepts);
//		Set<OWLLogicalAxiom> moduleOnto_2OnForgettingSig = sp.extractModule(onto,Sets.difference(onto.getSignature(), forgettingSignatures));

        Set<OWLLogicalAxiom> moduleOnto_2OnForgettingSig = onto.getLogicalAxioms();

        //优化：1.只有1个A = 。。。定义式 删掉 2。 A全是in的 A in B A in C existr.A in B 即在左边并且没有等号的，直接删掉 3。有定义式的 ，用定义式右边的去替换
        //其他地方的A，其他地方的A包括左边和右边的 4. 如果一个concept只出现在右边，全部替换成T
        moduleOnto_2OnForgettingSig = sp.eliminateDefinedConceptsAndBasedConcepts(moduleOnto_2OnForgettingSig, concepts, metrics);

        //list转换 转换过程中会删除掉不是ELH的axiom,同时形成新的onto
        List<Formula> formula_list_normalised = ct.AxiomsConverter(moduleOnto_2OnForgettingSig);
        //onto =bc.toOWLOntology(formula_list_normalised);

        //做一些不必要的初始化 防止bug
        AtomicConcept.definer_indexInit();
        TestForgetting.isExtra = 0;
        Forgetter.isExtra = false;

        logger.debug("Start load reasoner!");
        OWLReasoner hermit = new ReasonerFactory().createReasoner(ontology);
        logger.debug("End load reasoner!");


        //forgetting signature数据结构转换
//		Set<AtomicRole> r_sig = ct.getRolesfromObjectProperties(roles);
        Set<AtomicRole> r_sig_set = ct.getRolesfromObjectProperties(roles);
        List<AtomicRole > r_sig = new ArrayList<>(r_sig_set);
        Set<AtomicConcept> c_sig = ct.getConceptsfromClasses(concepts);
        r_sig.sort(Comparator.naturalOrder()) ;

        logger.debug("Before role forgetting");
        if (!r_sig.isEmpty()) {
            List<Formula> r_sig_list_normalised = se.getRoleSubset(r_sig_set, formula_list_normalised);
            List<Formula> pivot_list_normalised = null;
            //List<AtomicRole> r_sig_ordering = ordering2(r_sig,r_sig_list_normalised);

            int i = 0;
            for (AtomicRole role : r_sig) {

//				System.out.println("Forgetting Role [" + i + "] = " + role);
                i++;
                pivot_list_normalised = se.getRoleSubset(role, r_sig_list_normalised);
                if(role.toString().equals("http://purl.org/biotop/biotop.owl#hasProperPhysicalPart")){
                    pivot_list_normalised.sort(Comparator.comparing(Object::toString));
//					for(Formula formula: pivot_list_normalised){
//						System.out.println(formula);
//					}
                }
                logger.trace("Forgetting Role [" + i + "] = " + role + " from {} normalised axioms", pivot_list_normalised.size());
                if (pivot_list_normalised.isEmpty()) {

                } else {

                    pivot_list_normalised = di.introduceDefiners(role, pivot_list_normalised);///
                    pivot_list_normalised = inf.combination_R(role, pivot_list_normalised, onto,hermit, null);

                    r_sig_list_normalised.addAll(pivot_list_normalised);
                }
            }

            formula_list_normalised.addAll(r_sig_list_normalised);
        }

        logger.debug("Finished role forgetting, before concept forgetting");
        if (!c_sig.isEmpty()) {
            List<Formula> c_sig_list_normalised = se.getConceptSubset(c_sig, formula_list_normalised);
            List<Formula> pivot_list_normalised = null;
            int j = 1;
            List<AtomicConcept> c_sig_ordering = sp.ordering(c_sig,c_sig_list_normalised);
            for (AtomicConcept concept : c_sig_ordering) {
                //for (AtomicConcept concept : c_sig) {
                logger.trace("Forgetting Concept [" + j + "] (of "+c_sig_ordering.size()+") = " + concept);
//				System.out.println("Forgetting Concept [" + j + "] (of "+c_sig_ordering.size()+") = " + concept);
                //System.out.println("Reasoning with "+concept);
                j++;
                pivot_list_normalised = se.getConceptSubset(concept, c_sig_list_normalised);

                if (pivot_list_normalised.isEmpty()) {

                } else if (fc.positive(concept, pivot_list_normalised) == 0 ||
                        fc.negative(concept, pivot_list_normalised) == 0) {
                    c_sig_list_normalised.addAll(inf.Purify(concept, pivot_list_normalised));

                } else {

                    pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);
                    pivot_list_normalised = inf.combination_A(concept, pivot_list_normalised, onto, hermit, null);
                    //todo cyclic check
                    //for(Formula formula : pivot_list_normalised){
                    //	Set<AtomicConcept> common = Sets.intersection(formula.getSubFormulas().get(0).get_c_sig(),formula.getSubFormulas().get(1).get_c_sig());
                    ///	if((Sets.intersection(common,c_sig).size()!=0|| Sets.intersection(common,di.definer_set).size()!=0)){
                    //		System.out.println(formula);
                    //		throw new Exception();
                    //	}
                    //}

                    c_sig_list_normalised.addAll(pivot_list_normalised);
                }
                c_sig_list_normalised = new ArrayList<>(new HashSet<>(c_sig_list_normalised));


            }

            formula_list_normalised.addAll(c_sig_list_normalised);

        }
        logger.debug("Finished concept forgetting");


        if (!di.definer_set.isEmpty()) {
            List<Formula> d_sig_list_normalised = se.getConceptSubset(di.definer_set, formula_list_normalised);
            List<Formula> pivot_list_normalised = null;
            Set<AtomicConcept> definer_set = null;
            List<Formula> forgetting_Definer_output = new ArrayList<>();

            ////this is the case of the cyclic cases, that's why the ACK_A is not re-used.
            //In case the results of contains this case. report!
            int k = 1;
            int num = 0;

            do {
                if (di.definer_set.isEmpty()) {
                    logger.info("Definer Forgetting Successful!");
                    logger.info("===================================================");
//					System.out.println("Forgetting Successful2!");
//					System.out.println("===================================================");
                    formula_list_normalised.addAll(d_sig_list_normalised);

                    break;
                }

                definer_set = new LinkedHashSet<>(di.definer_set);

                //List<AtomicConcept>  definer_set_inverse = new ArrayList<>(definer_set.size());
                //List<AtomicConcept> definer_set_ordering = ordering(definer_set,d_sig_list_normalised);
                //for (AtomicConcept concept : definer_set_ordering) {
                for (AtomicConcept concept : definer_set) {
                    num++;
                    if(num > 6000) break;
                    logger.trace("Forgetting Definer [" + k + "] = " + concept +" definer_set size :"+di.definer_set.size());
//					System.out.println("Forgetting Definer [" + k + "] = " + concept +" definer_set size :"+di.definer_set.size());
                    k++;
                    pivot_list_normalised = se.getConceptSubset(concept, d_sig_list_normalised);
                    if (pivot_list_normalised.isEmpty()) {
                        di.definer_set.remove(concept);

                    } else if (fc.positive(concept, pivot_list_normalised) == 0) {

                        List<Formula> ans = inf.Purify(concept, pivot_list_normalised);
						/*
						//todo cyclic check
						for(Formula formula : ans){
							Set<AtomicConcept> common = Sets.intersection(formula.getSubFormulas().get(0).get_c_sig(),formula.getSubFormulas().get(1).get_c_sig());
							if((Sets.intersection(common,c_sig).size()!=0|| Sets.intersection(common,di.definer_set).size()!=0)){
								num = 10000;
								//throw new Exception();
							}
						}

						 */
                        d_sig_list_normalised.addAll(ans);
                        di.definer_set.remove(concept);

                    } else if (fc.negative(concept, pivot_list_normalised) == 0) {

                        List<Formula> ans = inf.Purify(concept, pivot_list_normalised);
						/*
						//todo cyclic check
						for(Formula formula : ans){
							Set<AtomicConcept> common = Sets.intersection(formula.getSubFormulas().get(0).get_c_sig(),formula.getSubFormulas().get(1).get_c_sig());
							if((Sets.intersection(common,c_sig).size()!=0|| Sets.intersection(common,di.definer_set).size()!=0)){
								num = 10000;
								//throw new Exception();
							}
						}

						 */


                        d_sig_list_normalised.addAll(ans);
                        di.definer_set.remove(concept);

                    } else {
                        pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);
                        pivot_list_normalised = inf.combination_A(concept, pivot_list_normalised ,onto,hermit, null);
						/*
						//todo cyclic check
						for(Formula formula : pivot_list_normalised){
							Set<AtomicConcept> common = Sets.intersection(formula.getSubFormulas().get(0).get_c_sig(),formula.getSubFormulas().get(1).get_c_sig());
							if((Sets.intersection(common,c_sig).size()!=0|| Sets.intersection(common,di.definer_set).size()!=0)){
								num = 10000;
								//throw new Exception();
							}
						}

						 */

                        d_sig_list_normalised.addAll(pivot_list_normalised);
                        di.definer_set.remove(concept);

                    }
                }
                if(num > 6000){
                    metrics.isExtra = 1;
                    TestForgetting.isExtra = 1;
                    Forgetter.isExtra = true;
                    logger.warn("\"There is extra expressivity !\"");
//                    System.out.println("There is extra expressivity !");
                    break;
                }
            } while (true);


        }
        else{
            metrics.success = 1;
            logger.info("DefinersSet is empty!! ");
            logger.info("Forgetting Successful!");
            logger.info("===================================================");
//			System.out.println("DefinersSet is empty!! ");
//			System.out.println("Forgetting Successful!");
//			System.out.println("===================================================");


        }
        hermit.dispose();

        //调试 可以删除
        double tempTime2 = System.currentTimeMillis();
        int optSum = metrics.optimizeNum1+metrics.optimizeNum4+metrics.optimizeNum3+metrics.optimizeNum2;
        logger.info("Thread time consumption: {}", tempTime2 - tempTime1);
//		logger.debug("message "+conceptsSize+"\t"+(tempTime2-tempTime1)+"\t"+(optSum*1.0/conceptsSize));
        //return new ArrayList<>(new HashSet<>(formula_list_normalised));
        return formula_list_normalised;
    }

    public Set<OWLAxiom> forgettingSingleThread(Set<OWLObjectProperty> roles, Set<OWLClass> concepts, OWLOntology ontology) throws Exception {
        List<Formula> formulaList = Forgetting(roles, concepts, ontology, new saveMetrics());
//		BackConverter bc = new BackConverter();
//    	Set<OWLAxiom> axioms = bc.toOWLAxioms(formulaList);
        logger.debug("UI size: {}", formulaList.size());
//		return axioms;
        return null;
    }
}
