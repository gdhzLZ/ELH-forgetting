package test_term;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import checkexistence.EChecker;
import checkfrequency.FChecker;
import concepts.AtomicConcept;
import concepts.TopConcept;
import org.semarglproject.vocab.OWL;
import roles.AtomicRole;
import connectives.And;
import connectives.Or;

import connectives.Exists;
import connectives.Inclusion;
import convertion.BackConverter;
import formula.Formula;
public class statistical {
    public static  void main(String [] args) throws Exception{
        HashMap<OWLAxiom,Integer> now = new HashMap<>();
        BackConverter bc = new BackConverter();


        AtomicConcept a1 = new AtomicConcept("A");
        AtomicConcept b1 = new AtomicConcept("B");
        AtomicConcept c1 = new AtomicConcept("C");
        AtomicRole r1 = new AtomicRole("r");
        Exists e1 = new Exists(r1, b1);
        Exists e2 = new Exists(r1, a1);
        Exists e3 = new Exists(r1, c1);
        Set<Formula> list1 = new HashSet<>();
        list1.add(e1);
        list1.add(e2);
        list1.add(e3);
        And and1 = new And(list1);
        Inclusion inc1 = new Inclusion(and1, c1);

        Or or1 = new Or(new ArrayList<>(list1));

        System.out.println(inc1.clone());
        System.out.println("-------------");

        System.out.println(and1);
        System.out.println("-------------");


        Inclusion inc2 = new Inclusion(b1, c1);
        System.out.println(inc1.clone().getSubFormulas());
        System.out.println("-------------");
        System.out.println(inc2.clone().getSubFormulas());



        /*
        OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();
        System.out.println("Read Onto_1...");
        String filePath1 = "/Users/liuzhao/Downloads/Thesaurus (3).owl";
        OWLOntology onto_1 = manager1.loadOntologyFromOntologyDocument(new File(filePath1));
        int numNot = 0;
        int num = 0;
        int allNum = onto_1.getAxiomCount();
        for(OWLAxiom axiom : onto_1.getLogicalAxioms()){
            if(axiom instanceof OWLSubClassOfAxiom){
                OWLSubClassOfAxiom subAxiom = (OWLSubClassOfAxiom) axiom;
                OWLClassExpression now = subAxiom.getSubClass();
                if(!(now instanceof OWLClass)){
                    numNot++;
                    System.out.println(axiom);
                }
            }
            else if(axiom instanceof  OWLEquivalentClassesAxiom){
                OWLEquivalentClassesAxiom subAxiom = (OWLEquivalentClassesAxiom) axiom;
                Set<OWLSubClassOfAxiom> setAxioms = subAxiom.asOWLSubClassOfAxioms();
                for(OWLSubClassOfAxiom axiom_temp : setAxioms){
                    OWLSubClassOfAxiom temp = (OWLSubClassOfAxiom) axiom_temp;
                    OWLClassExpression now = temp.getSubClass();
                    if(!(now instanceof OWLClass)){
                        numNot++;
                        System.out.println(axiom);
                        break;
                    }
                }

            }
            num++;
            System.out.println(num +" "+ allNum +" " );


        }
        System.out.println(numNot +" "+ allNum +" " + numNot*1.0/allNum);

         */

    }
}
