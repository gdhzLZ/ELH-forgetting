package forgetting;

import java.io.File;
import java.text.Normalizer;
import java.util.HashSet;
import java.util.List;
import java.util.*;

import Test.TestForgetting;
import checkTautology.TautologyChecker;
import concepts.TopConcept;
import javafx.util.*;
import com.google.common.collect.Sets;
import connectives.And;
import connectives.Exists;
import connectives.Inclusion;
import convertion.BackConverter;
import convertion.Converter;
import elk.*;
import org.semanticweb.elk.owlapi.ElkReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;

import checkfrequency.FChecker;
import concepts.AtomicConcept;
import extraction.SubsetExtractor;
import formula.Formula;
import inference.DefinerIntroducer;
import inference.Inferencer;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import roles.AtomicRole;


public class Forgetter {
    /**
     *
     * @param r_sig the role set we want to forget
     * @param c_sig the concept set we want to forget
     * @param formula_list_normalised  the formula_list which is transfromed from initial ontology
     * @param onto2   In some rules, we need to check entailments on onto2
     * @return
     * @throws Exception
     */
	public List<Formula> Forgetting(Set<AtomicRole> r_sig, Set<AtomicConcept> c_sig,
			List<Formula> formula_list_normalised, OWLOntology onto2) throws Exception {

		System.out.println("The Forgetting Starts:");
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology onto = manager.createOntology(onto2.getAxioms());// it is a copy of onto2


		DefinerIntroducer di = new DefinerIntroducer();
		//Simplifier pp = new Simplifier();
		SubsetExtractor se = new SubsetExtractor();
		BackConverter bc = new BackConverter();
		Inferencer inf = new Inferencer();
		FChecker fc = new FChecker();

		if (!r_sig.isEmpty()) {
			List<Formula> r_sig_list_normalised = se.getRoleSubset(r_sig, formula_list_normalised);
			List<Formula> pivot_list_normalised = null;
			int i = 1;
			for (AtomicRole role : r_sig) {

				System.out.println("Forgetting Role [" + i + "] = " + role);
				i++;
				//if(!role.toString().contains("http://snomed.info/id/732945000")) continue;

				pivot_list_normalised = se.getRoleSubset(role, r_sig_list_normalised);
				if (pivot_list_normalised.isEmpty()) {

				} else {
                    Set<Formula> beforeIntroDefiners = new LinkedHashSet<>(pivot_list_normalised);

                    pivot_list_normalised = di.introduceDefiners(role, pivot_list_normalised);///
                    Set<Formula> afterIntroDefiners = new LinkedHashSet<>(pivot_list_normalised);

                    Set<OWLAxiom> containNewDefinersSet = new LinkedHashSet<>();
                    for(Formula formula :  Sets.difference(afterIntroDefiners,beforeIntroDefiners)){
                        containNewDefinersSet.add(bc.toOWLAxiom(formula));
                    }
                    manager.addAxioms(onto,containNewDefinersSet);

                    pivot_list_normalised = inf.combination_R(role, pivot_list_normalised, onto);

					r_sig_list_normalised.addAll(pivot_list_normalised);
				}
			}

			formula_list_normalised.addAll(r_sig_list_normalised);
		}
		
		if (!c_sig.isEmpty()) {
			List<Formula> c_sig_list_normalised = se.getConceptSubset(c_sig, formula_list_normalised);
			List<Formula> pivot_list_normalised = null;
			int j = 1;
			for (AtomicConcept concept : c_sig) {
				System.out.println("Forgetting Concept [" + j + "] = " + concept);
				j++;
				pivot_list_normalised = se.getConceptSubset(concept, c_sig_list_normalised);

				if (pivot_list_normalised.isEmpty()) {
					
				} else if (fc.positive(concept, pivot_list_normalised) == 0 ||
						fc.negative(concept, pivot_list_normalised) == 0) {
					c_sig_list_normalised.addAll(inf.Purify(concept, pivot_list_normalised));

				} else {
                    Set<Formula> beforeIntroDefiners = new LinkedHashSet<>(pivot_list_normalised);
                    pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);
                    Set<Formula> afterIntroDefiners = new LinkedHashSet<>(pivot_list_normalised);
                    Set<OWLAxiom> containNewDefinersSet = new LinkedHashSet<>();
                    for(Formula formula :  Sets.difference(afterIntroDefiners,beforeIntroDefiners)){
                        containNewDefinersSet.add(bc.toOWLAxiom(formula));
                    }
                    manager.addAxioms(onto,containNewDefinersSet);
                    pivot_list_normalised = inf.combination_A(concept, pivot_list_normalised, onto);
					c_sig_list_normalised.addAll(pivot_list_normalised);
				}
			}

			formula_list_normalised.addAll(c_sig_list_normalised);
		}

		/*
		if (!DefinerIntroducer.definer_set.isEmpty()) {
			List<Formula> d_sig_list_normalised = new ArrayList<>();
			List<Formula> forgetting_Definer_output = new ArrayList<>();
			List<Formula> pivot_list_normalised = null;
			Set<AtomicConcept> definer_set = null;
			////this is the case of the cyclic cases, that's why the ACK_A is not re-used. 
			//In case the results of contains this case. report!
			int k = 1;
			do {
				if (DefinerIntroducer.definer_set.isEmpty()) {
					System.out.println("Forgetting Successful!");
					System.out.println("===================================================");
					formula_list_normalised.addAll(forgetting_Definer_output);

					return formula_list_normalised;
				}
				
				definer_set = new LinkedHashSet<>(DefinerIntroducer.definer_set);
				d_sig_list_normalised = se.getConceptSubset(DefinerIntroducer.definer_set, formula_list_normalised);

				for (AtomicConcept concept : definer_set) {
					System.out.println("Forgetting Definer [" + k + "] = " + concept +" definer_set size :"+DefinerIntroducer.definer_set.size());
					k++;
					pivot_list_normalised = se.getConceptSubset(concept, d_sig_list_normalised);
					if (pivot_list_normalised.isEmpty()) {
						DefinerIntroducer.definer_set.remove(concept);

					} else if (fc.positive(concept, pivot_list_normalised) == 0) {
						System.out.println("purify 1");
						List<Formula> temp = inf.Purify(concept, pivot_list_normalised);
						forgetting_Definer_output.addAll(temp);
						for(Formula i : temp){
							System.out.println(i);
						}
						System.out.println("-----------");
						DefinerIntroducer.definer_set.remove(concept);

					} else if (fc.negative(concept, pivot_list_normalised) == 0) {
						System.out.println("purify 2");
						List<Formula> temp = inf.Purify(concept, pivot_list_normalised);
						forgetting_Definer_output.addAll(temp);
						for(Formula i : temp){
							System.out.println(i);
						}
						System.out.println("-----------");
						DefinerIntroducer.definer_set.remove(concept);

					} else {
						pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);
						pivot_list_normalised = inf.combination_A(concept, pivot_list_normalised, onto);
						forgetting_Definer_output.addAll(pivot_list_normalised);
					}
				}

			} while (true);
			*/

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
					System.out.println("Forgetting Successful!");
					System.out.println("===================================================");
					formula_list_normalised.addAll(d_sig_list_normalised);

					return formula_list_normalised;
				}

				definer_set = new LinkedHashSet<>(di.definer_set);

				for (AtomicConcept concept : definer_set) {
					num++;
					System.out.println("Forgetting Definer [" + k + "] = " + concept +" definer_set size :"+di.definer_set.size());
					k++;
					pivot_list_normalised = se.getConceptSubset(concept, d_sig_list_normalised);
					if (pivot_list_normalised.isEmpty()) {
						di.definer_set.remove(concept);

					} else if (fc.positive(concept, pivot_list_normalised) == 0) {

						List<Formula> ans = inf.Purify(concept, pivot_list_normalised);

						d_sig_list_normalised.addAll(ans);
						di.definer_set.remove(concept);

					} else if (fc.negative(concept, pivot_list_normalised) == 0) {

						List<Formula> ans = inf.Purify(concept, pivot_list_normalised);

						d_sig_list_normalised.addAll(ans);
						di.definer_set.remove(concept);

					} else {
						/*
                        int length1 = pivot_list_normalised.size();
						pivot_list_normalised = di.removeCyclicDefinition(concept,pivot_list_normalised);
						int length2 = pivot_list_normalised.size();
						if(length1 != length2){
							TestForgetting.isExtra = 1;
							System.out.println("There is extra expressivity !");
						}

						 */
						Set<Formula> beforeIntroDefiners = new LinkedHashSet<>(pivot_list_normalised);
						pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);
                        Set<Formula> afterIntroDefiners = new LinkedHashSet<>(pivot_list_normalised);
                        Set<OWLAxiom> containNewDefinersSet = new LinkedHashSet<>();
                        for(Formula formula :  Sets.difference(afterIntroDefiners,beforeIntroDefiners)){
                            containNewDefinersSet.add(bc.toOWLAxiom(formula));
                        }
                        manager.addAxioms(onto,containNewDefinersSet);
						pivot_list_normalised = inf.combination_A(concept, pivot_list_normalised, onto);
						d_sig_list_normalised.addAll(pivot_list_normalised);
						di.definer_set.remove(concept);

					}
				}
				if(num > 12000){
					TestForgetting.isExtra = 1;
					System.out.println("There is extra expressivity !");
					break;
				}
			} while (true);


		}
		else{
			System.out.println("DefinersSet is empty!! ");
			System.out.println("Forgetting Successful!");
			System.out.println("===================================================");


		}
		

		return formula_list_normalised;
	}
	public static void main(String [] args) throws  Exception {

		OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();

        Formula CA= new Inclusion(new AtomicConcept("C"),new AtomicConcept("A"));
        Formula existrA = new Exists(new AtomicRole("r"),new AtomicConcept("A"));
        Set<Formula> AandB = new LinkedHashSet<>();
        AandB.add(new AtomicConcept("A"));AandB.add(new AtomicConcept("B"));
        And and = new And(AandB);

        List<Formula> formula_list_normalised = new ArrayList<>();
        Set<Formula> s1 = new LinkedHashSet<>();
        s1.add(existrA);s1.add(new AtomicConcept("B"));
        And and2 = new And(s1);
        formula_list_normalised.add(CA);
        formula_list_normalised.add(new Inclusion(new AtomicConcept("C"),existrA));
        formula_list_normalised.add(new Inclusion(new AtomicConcept("C"),new Exists(new AtomicRole("r"),and)));
        formula_list_normalised.add(new Inclusion(new AtomicConcept("A"),new AtomicConcept("G")));
        formula_list_normalised.add(new Inclusion(and,new AtomicConcept("G")));
        formula_list_normalised.add(new Inclusion(new Exists(new AtomicRole("s"),new AtomicConcept("A")),new AtomicConcept("G")));
        formula_list_normalised.add(new Inclusion(and2,new AtomicConcept("G")));
        formula_list_normalised.add(new Inclusion(new AtomicRole("r"),new AtomicRole("s")));
        formula_list_normalised.add(new Inclusion(new Exists(new AtomicRole("r"),and),new AtomicConcept("G")));
        Set<Formula> s2 = new LinkedHashSet<>();
        s2.add(new Exists(new AtomicRole("r"),and));
        s2.add(new AtomicConcept("F"));
        formula_list_normalised.add(new Inclusion(new And(s2),new AtomicConcept("G")));
        Forgetter fg = new Forgetter();
        Set<AtomicConcept> c_sig = new LinkedHashSet<>();
        c_sig.add(new AtomicConcept("A"));
        Set<OWLAxiom> temp = new LinkedHashSet<>();
        BackConverter bc = new BackConverter();
        OWLOntology onto = bc.toOWLOntology(new ArrayList<>(formula_list_normalised));
        System.out.println(formula_list_normalised);
        OWLReasoner reasoner =  new ElkReasonerFactory().createReasoner(onto);
        System.out.println(elkEntailment.entailed(reasoner,bc.toOWLAxiom(new Inclusion(TopConcept.getInstance(),new AtomicConcept("B")))));
        List<Formula> ui = fg.Forgetting(new LinkedHashSet<>(),c_sig,formula_list_normalised,onto);
        Set<Formula> n = new HashSet<>(ui);
        for(Formula f:ui){
        	System.out.println(f);
        	System.out.println(f.hashCode());
		}
        System.out.println(n);








	}


}
