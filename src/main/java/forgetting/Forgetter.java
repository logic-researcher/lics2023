package forgetting;

import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.text.Normalizer;
import java.util.HashSet;
import java.util.List;
import java.util.*;
import java.util.concurrent.*;

import Test.TestForgetting;
import com.google.common.collect.Sets;
import com.sun.deploy.net.offline.OfflineHandler;
import convertion.BackConverter;
import convertion.Converter;
import org.semanticweb.HermiT.*;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;

import checkfrequency.FChecker;
import concepts.AtomicConcept;
import extraction.SubsetExtractor;
import formula.Formula;
import inference.DefinerIntroducer;
import inference.Inferencer;
import inference.simplifier;

import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import roles.AtomicRole;
import uk.ac.man.cs.lethe.forgetting.*;
import uk.ac.man.cs.lethe.interpolation.*;

public class Forgetter {
    public static  boolean isExtra = false;
	static Logger logger = LoggerFactory.getLogger(Forgetter.class);
	SubsetExtractor se = new SubsetExtractor();
	FChecker fc = new FChecker();
	simplifier sp = new simplifier();
	Converter ct = new Converter();
	Inferencer inf = new Inferencer();
	OWLOntologyManager manager = OWLManager.createOWLOntologyManager();


	private ThreadLocal<OWLReasoner> reasonerThreadLocal = null;
	public Forgetter(OWLOntology ontology){
		//初始化线程本地变量
//		reasonerThreadLocal = ThreadLocal.withInitial(() -> new ReasonerFactory().createReasoner(ontology));
	}

	public Forgetter(){
//		System.err.println("error");
//		//初始化线程本地变量
//		reasonerThreadLocal = ThreadLocal.withInitial(() -> new ReasonerFactory().createReasoner(null));
	}

	public void setReasoner(OWLOntology ontology){
		reasonerThreadLocal = ThreadLocal.withInitial(() -> new ReasonerFactory().createReasoner(ontology));
	}

	public OWLOntology forgettingSingleThread(Set<OWLObjectProperty> roles, Set<OWLClass> concepts, OWLOntology ontology) throws Exception {
		reasonerThreadLocal = ThreadLocal.withInitial(() -> new ReasonerFactory().createReasoner(ontology));
		Set<OWLEntity> entitySet = new HashSet<>(roles);
		entitySet.addAll(concepts);
//		Set<OWLAxiom> axiomSet = ontology.getAxioms();
//		Set<OWLAxiom> subAxiomSet = se.getEntitySubset(entitySet, axiomSet);

		List<Formula> formulaList = Forgetting(roles, concepts, ontology, new saveMetrics());
		BackConverter bc = new BackConverter();
    	Set<OWLAxiom> axioms = bc.toOWLAxioms(formulaList);
		logger.debug("UI size: {}", formulaList.size());
//		return axioms;
		return OWLManager.createOWLOntologyManager().createOntology(axioms);
//		return formulaList;
	}

	public OWLOntology forgettingMultiThread(Set<OWLObjectProperty> roles, Set<OWLClass> concepts, OWLOntology ontology) throws Exception {
		reasonerThreadLocal = ThreadLocal.withInitial(() -> new ReasonerFactory().createReasoner(ontology));
		int threadNum = Runtime.getRuntime().availableProcessors();
		int ave = (roles.size() + concepts.size()) / threadNum;
		ExecutorService executors = Executors.newFixedThreadPool(threadNum);
		Long startTime = System.currentTimeMillis();
		Set<OWLEntity> forgettingSignatures = new HashSet<>(roles);
		forgettingSignatures.addAll(concepts);
		SubsetExtractor se = new SubsetExtractor();
		Map<String, Set<OWLLogicalAxiom>> signatureAxiomMap = new HashMap<>();
		List<Set<OWLEntity>> partitions = SignaturePartition.partitionSignature(forgettingSignatures, ontology, signatureAxiomMap);
		partitions.sort((o1, o2) -> {
			if(o1.size() > o2.size())
				return -1;
			else if(o1.size() == o2.size())
				return 0;
			return 1;
		});

		Set<OWLEntity> forgettingSignature = null;
		int maxPartition = 0;
		try{
			maxPartition = partitions.get(0).size();
		}catch (Exception e){

		}
		long duration = System.currentTimeMillis() - startTime;
		logger.debug("The time of partition: {}", duration);
		logger.debug("MaxPartition / ForgettingSignatures: {} / {}", maxPartition, forgettingSignatures.size());
		List<Future<List<Formula>>> futures = new ArrayList<>();
		List<Formula> formulaList = new ArrayList<>();
		List<Integer> formulaListSize = new ArrayList<>();
		Set<OWLAxiom> axiomSet = new HashSet<>(ontology.getLogicalAxioms());
		int cnt = 0;
		boolean flag = false;
		for(Set<OWLEntity> partition: partitions){
			cnt ++;
			if(forgettingSignature == null){
				forgettingSignature = partition;
				flag = true;
				continue;
			}
			if(forgettingSignature.size() + partition.size() >= Math.max(ave, maxPartition)){
				Set<OWLAxiom> subAxiomSet = se.getEntitySubset(forgettingSignature, axiomSet, signatureAxiomMap);
//				Forgetting(forgettingSignature, subAxiomSet, new saveMetrics());
//				Future<List<Formula>> future = executors.submit(new MyThread(forgettingSignature, subAxiomSet, new saveMetrics()));
				Set<OWLEntity> finalForgettingSignature = forgettingSignature;

				Set<OWLAxiom> finalSubAxiomSet1 = subAxiomSet;
				Future<List<Formula>> future = executors.submit(() -> Forgetting(finalForgettingSignature, finalSubAxiomSet1, new saveMetrics()));
				futures.add(future);
				forgettingSignature = partition;
				flag = true;

			}else{
				forgettingSignature.addAll(partition);
			}
		}
		if(flag){
			Set<OWLAxiom> subAxiomSet = se.getEntitySubset(forgettingSignature, axiomSet, signatureAxiomMap);
			Set<OWLEntity> finalForgettingSignature1 = forgettingSignature;
			Future<List<Formula>> future = executors.submit(() -> Forgetting(finalForgettingSignature1, subAxiomSet, new saveMetrics()));
			futures.add(future);
		}
		for(Future<List<Formula>> future: futures){
			formulaList.addAll(future.get());
		}
		executors.shutdown();
    	BackConverter bc = new BackConverter();
		axiomSet.addAll(bc.toOWLAxioms(formulaList));
		logger.warn("UI size: {}", formulaList.size() + axiomSet.size());
		return OWLManager.createOWLOntologyManager().createOntology(axiomSet);
	}
	public Set<OWLAxiom> ForgettingAPI(Set<OWLObjectProperty> roles, Set<OWLClass> concepts, OWLOntology onto) throws Exception{
		return null;
	}

	public List<Formula> ForgettingOldVersion(Set<OWLObjectProperty> roles, Set<OWLClass> concepts, OWLOntology onto) throws Exception {
		return null;
	}


//	/**
//	 *这个是CIKM版本的forgetting 不加优化
//	 * @param roles 要遗忘的role
//	 * @param concepts 要遗忘的concept
//	 * @param onto 这个就是读入的onto不需要，传入之前不需要做任何操作，传入后，需要删除不是ELH的axioms，再形成本体。
//	 * @return
//	 * @throws Exception
//	 */
//	public List<Formula> ForgettingOldVersion(Set<OWLObjectProperty> roles, Set<OWLClass> concepts, OWLOntology onto) throws Exception {
//		DefinerIntroducer di = new DefinerIntroducer();
//		SubsetExtractor se = new SubsetExtractor();
//		Inferencer inf = new Inferencer();
//		FChecker fc = new FChecker();
//		simplifier sp = new simplifier();
//		Converter ct = new Converter();
//		BackConverter bc = new BackConverter();
//
//
//		//提取module
//		Set<OWLEntity> forgettingSignatures = new HashSet<>();
//		forgettingSignatures.addAll(roles);
//		forgettingSignatures.addAll(concepts);
//		Set<OWLLogicalAxiom> moduleOnto_2OnForgettingSig = sp.extractModule(onto,Sets.difference(onto.getSignature(), forgettingSignatures));
//		//System.out.println("module size "+moduleOnto_2OnForgettingSig.size());
//
//		//list转换 转换过程中会删除掉不是ELH的axiom,同时形成新的onto
//		List<Formula> formula_list_normalised = ct.AxiomsConverter(moduleOnto_2OnForgettingSig);
//		//onto =bc.toOWLOntology(formula_list_normalised);
//
//		//做一些不必要的初始化 防止bug
//		AtomicConcept.definer_indexInit();
//		TestForgetting.isExtra = 0;
//		Forgetter.isExtra = false;
//
//		//初始化reasoner
//		System.out.println("hermit begin");
//
//		OWLReasoner hermit = null;
//		try {
//
//
//			hermit = new ReasonerFactory().createReasoner(onto);
//		}catch (Exception e){
//			System.out.println(e);
//			return null;
//		}
//		System.out.println("hermit finished");
//
//		//forgetting signature数据结构转换
//		Set<AtomicRole> r_sig = ct.getRolesfromObjectProperties(roles);
//		Set<AtomicConcept> c_sig = ct.getConceptsfromClasses(concepts);
//
//		System.out.println("The Forgetting Starts:");
//		System.out.println("The forgetting task is to eliminate [" + c_sig.size() + "] concept names and ["
//				+ r_sig.size() + "] role names from [" + formula_list_normalised.size() + "] normalized axioms");
//
//		if (!r_sig.isEmpty()) {
//			List<Formula> r_sig_list_normalised = se.getRoleSubset(r_sig, formula_list_normalised);
//			List<Formula> pivot_list_normalised = null;
//			//List<AtomicRole> r_sig_ordering = ordering2(r_sig,r_sig_list_normalised);
//
//			int i = 1;
//			for (AtomicRole role : r_sig) {
//
//				System.out.println("Forgetting Role [" + i + "] = " + role);
//				i++;
//				pivot_list_normalised = se.getRoleSubset(role, r_sig_list_normalised);
//				if (pivot_list_normalised.isEmpty()) {
//
//				} else {
//
//					pivot_list_normalised = di.introduceDefiners(role, pivot_list_normalised);///
//					pivot_list_normalised = inf.combination_R(role, pivot_list_normalised, onto,hermit);
//
//					r_sig_list_normalised.addAll(pivot_list_normalised);
//				}
//			}
//
//			formula_list_normalised.addAll(r_sig_list_normalised);
//		}
//
//		if (!c_sig.isEmpty()) {
//			List<Formula> c_sig_list_normalised = se.getConceptSubset(c_sig, formula_list_normalised);
//			List<Formula> pivot_list_normalised = null;
//			int j = 1;
//			List<AtomicConcept> c_sig_ordering = sp.ordering(c_sig,c_sig_list_normalised);
//			for (AtomicConcept concept : c_sig_ordering) {
//				//for (AtomicConcept concept : c_sig) {
//				System.out.println("Forgetting Concept [" + j + "] (of "+c_sig_ordering.size()+") = " + concept);
//				//System.out.println("Reasoning with "+concept);
//				j++;
//				pivot_list_normalised = se.getConceptSubset(concept, c_sig_list_normalised);
//
//				if (pivot_list_normalised.isEmpty()) {
//
//				} else if (fc.positive(concept, pivot_list_normalised) == 0 ||
//						fc.negative(concept, pivot_list_normalised) == 0) {
//					c_sig_list_normalised.addAll(inf.Purify(concept, pivot_list_normalised));
//
//				} else {
//					pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);
//					pivot_list_normalised = inf.combination_A(concept, pivot_list_normalised, onto, hermit, reasonerThreadLocal);
//					c_sig_list_normalised.addAll(pivot_list_normalised);
//				}
//				c_sig_list_normalised = new ArrayList<>(new HashSet<>(c_sig_list_normalised));
//
//
//			}
//
//			formula_list_normalised.addAll(c_sig_list_normalised);
//
//		}
//
//
//		if (!di.definer_set.isEmpty()) {
//			List<Formula> d_sig_list_normalised = se.getConceptSubset(di.definer_set, formula_list_normalised);
//			List<Formula> pivot_list_normalised = null;
//			Set<AtomicConcept> definer_set = null;
//			List<Formula> forgetting_Definer_output = new ArrayList<>();
//
//			////this is the case of the cyclic cases, that's why the ACK_A is not re-used.
//			//In case the results of contains this case. report!
//			int k = 1;
//			int num = 0;
//
//			do {
//				if (di.definer_set.isEmpty()) {
//					System.out.println("Forgetting Successful!");
//					System.out.println("===================================================");
//					formula_list_normalised.addAll(d_sig_list_normalised);
//
//					return formula_list_normalised;
//				}
//
//				definer_set = new LinkedHashSet<>(di.definer_set);
//
//				//List<AtomicConcept>  definer_set_inverse = new ArrayList<>(definer_set.size());
//				//List<AtomicConcept> definer_set_ordering = ordering(definer_set,d_sig_list_normalised);
//				//for (AtomicConcept concept : definer_set_ordering) {
//				for (AtomicConcept concept : definer_set) {
//					num++;
//					System.out.println("Forgetting Definer [" + k + "] = " + concept +" definer_set size :"+di.definer_set.size());
//					k++;
//					pivot_list_normalised = se.getConceptSubset(concept, d_sig_list_normalised);
//					if (pivot_list_normalised.isEmpty()) {
//						di.definer_set.remove(concept);
//
//					} else if (fc.positive(concept, pivot_list_normalised) == 0) {
//
//						List<Formula> ans = inf.Purify(concept, pivot_list_normalised);
//
//						d_sig_list_normalised.addAll(ans);
//						di.definer_set.remove(concept);
//
//					} else if (fc.negative(concept, pivot_list_normalised) == 0) {
//
//						List<Formula> ans = inf.Purify(concept, pivot_list_normalised);
//
//						d_sig_list_normalised.addAll(ans);
//						di.definer_set.remove(concept);
//
//					} else {
//						pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);
//						pivot_list_normalised = inf.combination_A(concept, pivot_list_normalised ,onto, hermit, reasonerThreadLocal);
//						d_sig_list_normalised.addAll(pivot_list_normalised);
//						di.definer_set.remove(concept);
//
//					}
//				}
//				if(num > 6000){
//					TestForgetting.isExtra = 1;
//					Forgetter.isExtra = true;
//					System.out.println("There is extra expressivity !");
//					break;
//				}
//			} while (true);
//
//
//		}
//		else{
//			System.out.println("DefinersSet is empty!! ");
//			System.out.println("Forgetting Successful!");
//			System.out.println("===================================================");
//
//
//		}
//		hermit.dispose();
//		return formula_list_normalised;
//	}

	public List<Formula> Forgetting(Set<OWLEntity> forgettingSignature, Set<OWLAxiom> subAxiomSet, saveMetrics metrics) throws Exception {
		Set<OWLObjectProperty> roles = new HashSet<>();
		Set<OWLClass> concepts = new HashSet<>();

		for(OWLEntity entity: forgettingSignature){
			if(entity instanceof OWLObjectProperty)
				roles.add((OWLObjectProperty) entity);
			else
				concepts.add((OWLClass) entity);
		}
		return Forgetting(roles, concepts, manager.createOntology(subAxiomSet), metrics);
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
		logger.info("The Forgetting Starts:");

		double tempTime1 = System.currentTimeMillis();
		DefinerIntroducer di = new DefinerIntroducer();

		logger.info("The forgetting task is to eliminate [" + concepts.size() + "] concept names and ["
				+ roles.size() + "] role names from [" + onto.getLogicalAxiomCount() + "] axioms");

		//提取
		Set<OWLEntity> forgettingSignatures = new HashSet<>();
		forgettingSignatures.addAll(roles);
		forgettingSignatures.addAll(concepts);
		Set<OWLLogicalAxiom> moduleOnto_2OnForgettingSig = sp.extractModule(onto,Sets.difference(onto.getSignature(), forgettingSignatures));
//		Set<OWLLogicalAxiom> moduleOnto_2OnForgettingSig = onto.getLogicalAxioms();

		//优化：1.只有1个A = 。。。定义式 删掉 2。 A全是in的 A in B A in C existr.A in B 即在左边并且没有等号的，直接删掉 3。有定义式的 ，用定义式右边的去替换
		//其他地方的A，其他地方的A包括左边和右边的 4. 如果一个concept只出现在右边，全部替换成T

		logger.info("Before eliminate distinguish concepts");
		moduleOnto_2OnForgettingSig = sp.eliminateDefinedConceptsAndBasedConcepts(moduleOnto_2OnForgettingSig, concepts, metrics);
		logger.info("After eliminate distinguish concepts");

		//list转换 转换过程中会删除掉不是ELH的axiom,同时形成新的onto
		List<Formula> formula_list_normalised = ct.AxiomsConverter(moduleOnto_2OnForgettingSig);
		//onto =bc.toOWLOntology(formula_list_normalised);

		//做一些不必要的初始化 防止bug
//        AtomicConcept.definer_indexInit();
        TestForgetting.isExtra = 0;
        Forgetter.isExtra = false;

//		logger.debug("Start load reasoner!");
//		OWLReasoner hermit = reasonerThreadLocal.get();
		OWLReasoner hermit = null;
//		logger.debug("End load reasoner!");

		//forgetting signature数据结构转换
//		Set<AtomicRole> r_sig = ct.getRolesfromObjectProperties(roles);
		Set<AtomicRole> r_sig_set = ct.getRolesfromObjectProperties(roles);
		List<AtomicRole > r_sig = new ArrayList<>(r_sig_set);
		r_sig.sort(Comparator.naturalOrder()) ;
		Set<AtomicConcept> c_sig = ct.getConceptsfromClasses(concepts);

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

				logger.trace("Forgetting Role [" + i + "] = " + role + " from {} normalised axioms", pivot_list_normalised.size());
				if (pivot_list_normalised.isEmpty()) {

				} else {

                    pivot_list_normalised = di.introduceDefiners(role, pivot_list_normalised);///
                    pivot_list_normalised = inf.combination_R(role, pivot_list_normalised, onto, hermit, reasonerThreadLocal);

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
//			List<AtomicConcept> c_sig_ordering = sp.ordering(c_sig,c_sig_list_normalised);
			List<AtomicConcept> c_sig_ordering = sp.alphabetOrdering(c_sig,c_sig_list_normalised);

			for (AtomicConcept concept : c_sig_ordering) {
			//for (AtomicConcept concept : c_sig) {
				pivot_list_normalised = se.getConceptSubset(concept, c_sig_list_normalised);
				logger.trace("Forgetting Concept [" + j + "] (of "+c_sig_ordering.size()+") = " + concept+ " from {} normalised axioms", pivot_list_normalised.size());
//				System.out.println("Forgetting Concept [" + j + "] (of "+c_sig_ordering.size()+") = " + concept);
				//System.out.println("Reasoning with "+concept);
				j++;

				if (pivot_list_normalised.isEmpty()) {
					
				} else if (fc.positive(concept, pivot_list_normalised) == 0 ||
						fc.negative(concept, pivot_list_normalised) == 0) {
					c_sig_list_normalised.addAll(inf.Purify(concept, pivot_list_normalised));

				} else {

					pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);
					pivot_list_normalised = inf.combination_A(concept, pivot_list_normalised, onto, hermit, reasonerThreadLocal);
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
						d_sig_list_normalised.addAll(ans);
						di.definer_set.remove(concept);

					} else {
						pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);
						pivot_list_normalised = inf.combination_A(concept, pivot_list_normalised ,onto,hermit, reasonerThreadLocal);

						d_sig_list_normalised.addAll(pivot_list_normalised);
						di.definer_set.remove(concept);

					}
				}
				if(num > 6000){
					metrics.isExtra = 1;
					TestForgetting.isExtra = 1;
                    Forgetter.isExtra = true;
//					throw new IllegalArgumentException();
//					logger.warn("\"There is extra expressivity !\"");
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
		if(hermit != null){
			hermit.dispose();
		}
		reasonerThreadLocal.remove();
		//调试 可以删除
		double tempTime2 = System.currentTimeMillis();
		int optSum = metrics.optimizeNum1+metrics.optimizeNum4+metrics.optimizeNum3+metrics.optimizeNum2;
		logger.info("Thread time consumption: {}", tempTime2 - tempTime1);
//		logger.debug("message "+conceptsSize+"\t"+(tempTime2-tempTime1)+"\t"+(optSum*1.0/conceptsSize));
		//return new ArrayList<>(new HashSet<>(formula_list_normalised));
		return formula_list_normalised;
	}

	public boolean initializeReasoner(){
		reasonerThreadLocal.get();
		return true;
	}

	public static void main(String [] args) throws  Exception {

		//testmain();
		String ontoPath = "/Users/liuzhao/Desktop/Untitled2.owl";
		OWLOntologyManager manager =  OWLManager.createOWLOntologyManager();
		OWLOntology onto = manager.loadOntologyFromOntologyDocument(new File(ontoPath));
		Set<OWLEntity> concepts = new HashSet<>();
		for(OWLEntity temp : onto.getSignature()){
			if(temp.toString().contains("B") || temp.toString().contains("F")) concepts.add(temp);;
		}
		System.out.println(concepts);
		AlchTBoxForgetter now = new AlchTBoxForgetter();
		AlchTBoxInterpolator te = new AlchTBoxInterpolator();
		//OWLOntology ans = te.uniformInterpolant(onto,concepts);
		OWLOntology ans = now.forget(onto,concepts);
		System.out.println(ans.getLogicalAxioms());
	}
	public static void testmain()throws  Exception{
		String ontoPath = "/NCBOcrawler/GO/go1802.owl";
		OWLOntologyManager manager =  OWLManager.createOWLOntologyManager();
		OWLOntology onto = manager.loadOntologyFromOntologyDocument(new File(ontoPath));

		Set<OWLClass>concepts = onto.getClassesInSignature();
		Set<OWLObjectProperty>roles = onto.getObjectPropertiesInSignature();
		List<OWLClass> conceptList = new ArrayList<>(concepts);
		List<OWLObjectProperty>roleList = new ArrayList<>(roles);
		int forgettingroleNumber = 0;
		int forgettingconcpetNumber = 10;
		List<OWLClass> forgettingConcepts = TestForgetting.getSubStringByRadom2(conceptList,forgettingconcpetNumber);
		List<OWLObjectProperty> forgettingRoles = TestForgetting.getSubStringByRadom1(roleList, forgettingroleNumber);
		Forgetter fg = new Forgetter(onto);
		Set<OWLAxiom> ui = fg.ForgettingAPI(new HashSet<>(forgettingRoles),new HashSet<>(forgettingConcepts),onto);
		OWLOntologyManager man = OWLManager.createOWLOntologyManager();
		OWLOntology uitemp = man.createOntology(ui);

		OutputStream os_ui = new FileOutputStream(new File( "ui11.owl"));
		man.saveOntology(uitemp,os_ui);
		System.out.println(uitemp.getLogicalAxiomCount());
	}
	public static void testGhadah()throws Exception{
		String ontoPath = "/Users/liuzhao/Desktop/goslim_mouse.owl";
		OWLOntology prerserve_cig = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(ontoPath));
		OWLOntology onto = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File("/Users/liuzhao/Desktop/go.owl_denormalised.owl"));
		Set<OWLClass> cig = prerserve_cig.getClassesInSignature();
		Set<OWLClass> forgettingcig = Sets.difference(onto.getClassesInSignature(),cig);
		Set<OWLObjectProperty> roles = new LinkedHashSet<>();
		Forgetter fg = new Forgetter(onto);
		List<Formula> temp = fg.Forgetting(roles,forgettingcig,onto,new saveMetrics());
		System.out.println(temp.size());
	}



	class MyThread implements Callable<List<Formula>> {
		Set<OWLEntity> forgettingSignatures;
		saveMetrics metrics;
		Set<OWLAxiom> subAxiomSet;
		public MyThread(Set<OWLEntity> forgettingSignatures, Set<OWLAxiom> subAxiomSet, saveMetrics metrics){
			this.forgettingSignatures = forgettingSignatures;
			this.metrics = metrics;
			this.subAxiomSet = subAxiomSet;
		}
		@Override
		public List<Formula> call() throws Exception {
			return Forgetting(forgettingSignatures, subAxiomSet, metrics);
		}
	}
}



