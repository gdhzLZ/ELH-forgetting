package Test;
import java.io.*;
import java.util.*;

import com.google.common.collect.Sets;
import concepts.AtomicConcept;
import convertion.BackConverter;
import convertion.Converter;
import forgetting.*;
import formula.Formula;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.elk.owlapi.ElkReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.OWLXMLDocumentFormat;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import roles.AtomicRole;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;
import elk.*;

import java.util.concurrent.*;

public class TestForgetting {
    public static ArrayList<String> getFileName(String path){
        ArrayList<String> listFileName = new ArrayList<>();
        File file =new File(path);
        String[] names= file.list();
        for(String name : names){
            listFileName.add(path+name);
        }
        return listFileName;
    }
    public static void saveUI(Set<OWLAxiom> ui, String path)throws Exception{

        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology now = manager.createOntology(ui);
        OutputStream ops = new FileOutputStream(new File(path));
        manager.saveOntology(now, new OWLXMLDocumentFormat(), ops);
    }
    public static List<OWLObjectProperty> getSubStringByRadom1(List<OWLObjectProperty> list, int count){
        List backList = null;
        backList = new ArrayList<OWLObjectProperty>();
        Random random = new Random();
        int backSum = 0;
        if (list.size() >= count) {
            backSum = count;
        }else {
            backSum = list.size();
        }
        for (int i = 0; i < backSum; i++) {
//			随机数的范围为0-list.size()-1
            int target = random.nextInt(list.size());
            backList.add(list.get(target));
        }
        return backList;
    }
    public static List<OWLClass> getSubStringByRadom2(List<OWLClass> list, int count){
        List backList = null;
        backList = new ArrayList<OWLClass>();
        Random random = new Random();
        int backSum = 0;
        if (list.size() >= count) {
            backSum = count;
        }else {
            backSum = list.size();
        }
        for (int i = 0; i < backSum; i++) {
//			随机数的 ≤./范围为0-list.size()-1
            int target = random.nextInt(list.size());
            backList.add(list.get(target));
        }
        return backList;
    }

    public static int afterForgettingAxiomsSize = 0;
    public static OWLOntology onto = null;
    public static double time = 0;
    public static int isExtra = 0;
    public static double mem = 0;
    public static int success = 0;
    public static String nowLog = null;
    public static int witness_explicit_onto = 0;
    public static  int witness_implicit_onto = 0;
    public static void test2(String dictPath)throws Exception{
        double Rate = 0.1;
        String filelog = "log"+Rate+"_3.txt";
        ArrayList<String> hasRecord = readFile.readFile(dictPath+filelog);

        String title = "fileName,LogicalAxiomsSize,RolesSize,ConceptsSize,GCISize,GCIRolesSize,GCIConceptSize,isTestGCIForgetting,rate,time,memory,timeOut,MemoryOut," +"isSuccess,isExtra,afterForgettingAxiomsSize\n";
        writeFile.writeFile(dictPath+filelog,title);
        Converter ct = new Converter();
        BackConverter bc = new BackConverter();
        int circle = 5;
        int isTestGCIForgetting = 0;
        ArrayList<String> now = getFileName(dictPath);
        double []rates = new double[]{Rate};
        for(String path : now){

            int hasRead = 0;
            for(String temp : hasRecord) {
                if (temp.contains(path)) {
                    hasRead = 1;
                    break;
                }
            }
            if(hasRead == 1) continue;
            //if(hasRead != 1) continue;
            if(!path.contains(".owl")) continue;
            OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();
            onto = manager1.loadOntologyFromOntologyDocument(new File(path));

            // 统计基本的信息
            int logicalsize = onto.getLogicalAxioms().size();
            int rolesize = onto.getObjectPropertiesInSignature().size();
            int conceptsize = onto.getClassesInSignature().size();
            int GCIsize = onto.getGeneralClassAxioms().size();


            Set<OWLClassAxiom> GCIs = onto.getGeneralClassAxioms();
            Set<OWLObjectProperty> GCIroles = new LinkedHashSet<>();
            Set<OWLClass> GCIconcepts = new LinkedHashSet<>();
            for(OWLClassAxiom axiom : GCIs){
                GCIconcepts.addAll(axiom.getClassesInSignature());
                GCIroles.addAll(axiom.getObjectPropertiesInSignature());
            }
            int GCIrolesize = GCIroles.size();
            int GCIconceptsize = GCIconcepts.size();

            //data
            List<Formula> formulaELH = ct.OntologyConverter(onto);
            onto = bc.toOWLOntology(formulaELH);
            Set<OWLClass>concepts = onto.getClassesInSignature();
            Set<OWLObjectProperty>roles = onto.getObjectPropertiesInSignature();
            List<OWLClass> conceptList = new ArrayList<>(concepts);
            List<OWLObjectProperty>roleList = new ArrayList<>(roles);
            GCIs = onto.getGeneralClassAxioms();
            GCIroles = new LinkedHashSet<>();
            GCIconcepts = new LinkedHashSet<>();
            for(OWLClassAxiom axiom : GCIs){
                GCIconcepts.addAll(axiom.getClassesInSignature());
                GCIroles.addAll(axiom.getObjectPropertiesInSignature());
            }

            String log = path+","+logicalsize+","+rolesize+","+conceptsize+","+GCIsize+","+GCIrolesize+","+GCIconceptsize+","+isTestGCIForgetting;

            for(double rate :rates){
                nowLog = log+","+rate;
                System.out.println(nowLog);
                time = 0;
                mem = 0;
                afterForgettingAxiomsSize = 0;
                for(int i = 0 ; i < circle ; i++){
                    Forgetter fg = new Forgetter();
                    isExtra = 0;
                    success = 1;
                    elkEntailment.hasChecked_OnO2 = new HashMap<>();
                    AtomicConcept.setDefiner_index(1);
                    System.out.println("forgetting roles :"+(int) (rate * rolesize));
                    System.out.println("forgetting concepts :"+(int) (rate * conceptsize));

                    List<OWLClass> forgettingConcepts = getSubStringByRadom2(conceptList, (int) (rate * conceptsize));
                    List<OWLObjectProperty> forgettingRoles = getSubStringByRadom1(roleList, (int) (rate * rolesize));
                    Set<OWLEntity> forgettingSignatures = Sets.union(new HashSet<>(forgettingConcepts), new HashSet<>(forgettingRoles));
                    SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(manager1, onto, ModuleType.BOT);
                    Set<OWLAxiom> moduleOnto_2OnForgettingSig = extractor.extract(Sets.difference(onto.getSignature(), forgettingSignatures));
                    Set<OWLLogicalAxiom> moduleOnto_2OnCommonSig_logical = new HashSet<>();
                    System.out.println("module finished");
                    for (OWLAxiom axiom : moduleOnto_2OnForgettingSig) {
                        if (axiom instanceof OWLLogicalAxiom) {
                            moduleOnto_2OnCommonSig_logical.add((OWLLogicalAxiom) axiom);
                        }
                    }
                    List<Formula> formulaList = ct.AxiomsConverter(moduleOnto_2OnCommonSig_logical);
                    Set<AtomicRole> roleSet = ct.getRolesfromObjectProperties(new HashSet<>(forgettingRoles));
                    Set<AtomicConcept> conceptSet = ct.getConceptsfromClasses(new HashSet<>(forgettingConcepts));
                    final ExecutorService exec = Executors.newSingleThreadExecutor();
                    Callable<Integer> task = new Callable<Integer>() {
                        @Override
                        public Integer call() throws Exception {
                            try {
                                System.gc();
                                Runtime r = Runtime.getRuntime();
                                long mem1 = r.freeMemory();
                                long time1 = System.currentTimeMillis();
                                List<Formula> ui = fg.Forgetting(roleSet, conceptSet, formulaList, onto);
                                long time2 = System.currentTimeMillis();
                                long mem2 = r.freeMemory();

                                //elkEntailment.check(onto,ui);
                                afterForgettingAxiomsSize += ui.size();
                                time += (time2 - time1);
                                mem += (mem1-mem2);
                            } catch (OutOfMemoryError e){
                                nowLog = nowLog+",0,0,0,1,0,0,0\n";
                                writeFile.writeFile(dictPath+filelog,nowLog);
                                System.err.println("outofmemory");

                                success = 0;
                            }

                            catch (StackOverflowError e){
                                nowLog = nowLog+",0,0,0,2,0,0,0\n";
                                writeFile.writeFile(dictPath+filelog,nowLog);
                                System.err.println("stackoverflow");
                                success = 0;
                            }




                            return 1;
                        }
                    };

                    Future<Integer> future = exec.submit(task);
                    try{
                        int t = future.get(1000 * 900,TimeUnit.MILLISECONDS);
                    }

                    catch (OutOfMemoryError e){
                        nowLog = nowLog+",0,0,0,1,0,0,0\n";
                        writeFile.writeFile(dictPath+filelog,nowLog);
                        System.err.println("outofmemory2");

                        success = 0;
                        break;
                    }
                    catch (TimeoutException e){
                        nowLog = nowLog+",0,0,1,0,0,0,0\n";
                        writeFile.writeFile(dictPath+filelog,nowLog);
                        System.err.println("timeout");
                        success = 0;
                        System.gc();
                        break;
                    }

                    if(success == 0 || isExtra != 0) break;

                }
                if(success == 1 && isExtra == 0){
                    nowLog = nowLog+","+time*1.0/circle+","+mem/1024/1024/circle+",0,0,1,0,"+afterForgettingAxiomsSize/circle+"\n";
                    writeFile.writeFile(dictPath+filelog,nowLog);


                }
                if(success == 1 && isExtra != 0){
                    nowLog = nowLog+",0,0,0,0,0,"+isExtra+",0\n";
                    writeFile.writeFile(dictPath+filelog,nowLog);
                }
            }
        }
    }


    public static void test3(String dictPath)throws Exception{
        String filelog = "log"+".txt";
        ArrayList<String> hasRecord = readFile.readFile(dictPath+filelog);

        String title = "fileName_O1,fileName_O2,LogicalAxiomsSize_O1,LogicalAxiomsSize_O2,RolesSize_O1,RolesSize_O2,ConceptsSize_O1,ConceptsSize_O2," +
                "GCISize_O1,GCISize_O2,GCIRolesSize_O1,GCIRolesSize_O2,GCIConceptSize_O1,GCIConceptSize_O2,newLogicalRoleSize,newLogicalConceptSize,newLogicalRoleSizeOccuredInGCI,newLogicalConceptSizeOccuredInGCI,time," +
                "memory,timeOut,MemoryOut," +"isSuccess,isExtra,UI_size,explicit_witness,implicit_witness\n";
        writeFile.writeFile(dictPath+filelog,title);
        Converter ct = new Converter();
        BackConverter bc = new BackConverter();
        ArrayList<String> now = getFileName(dictPath);
        for(String path : now) {
            for (String path2 : now) {
                if(path.equals(path2)) continue;
                int hasRead = 0;
                for (String temp : hasRecord) {
                    if (temp.contains(path+","+path2)) {
                        hasRead = 1;
                        break;
                    }
                }
                if(path.contains("202001")) continue;
                if(!(path.contains("ontology_201707") && path2.contains("ontology_201701"))) continue;
                if (hasRead == 1) continue;
                if (!path.contains(".owl") || !path2.contains(".owl")) continue;
                OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();
                System.out.println(dictPath+path.substring(path.length()-10,path.length()-4)+path2.substring(path2.length()-10,path2.length()-4)+".owl");

                System.out.println(path);
                System.out.println(path2);

                OWLOntology onto1 = manager1.loadOntologyFromOntologyDocument(new File(path));
                System.out.println("onto1 load1");
                // 统计基本的信息
                int logicalsize1 = onto1.getLogicalAxioms().size();
                int rolesize1 = onto1.getObjectPropertiesInSignature().size();
                int conceptsize1 = onto1.getClassesInSignature().size();
                int GCIsize1 = onto1.getGeneralClassAxioms().size();
                Set<OWLClassAxiom> GCIs1 = onto1.getGeneralClassAxioms();
                Set<OWLObjectProperty> GCIroles1 = new LinkedHashSet<>();
                Set<OWLClass> GCIconcepts1 = new LinkedHashSet<>();
                for (OWLClassAxiom axiom : GCIs1) {
                    GCIconcepts1.addAll(axiom.getClassesInSignature());
                    GCIroles1.addAll(axiom.getObjectPropertiesInSignature());
                }
                int GCIrolesize1 = GCIroles1.size();
                int GCIconceptsize1 = GCIconcepts1.size();


                OWLOntologyManager manager2 = OWLManager.createOWLOntologyManager();
                OWLOntology onto2 = manager2.loadOntologyFromOntologyDocument(new File(path2));
                System.out.println("onto2 load1");
                // 统计基本的信息
                int logicalsize2 = onto2.getLogicalAxioms().size();
                int rolesize2 = onto2.getObjectPropertiesInSignature().size();
                int conceptsize2 = onto2.getClassesInSignature().size();
                int GCIsize2 = onto2.getGeneralClassAxioms().size();
                Set<OWLClassAxiom> GCIs2 = onto2.getGeneralClassAxioms();
                Set<OWLObjectProperty> GCIroles2 = new LinkedHashSet<>();
                Set<OWLClass> GCIconcepts2 = new LinkedHashSet<>();
                for (OWLClassAxiom axiom : GCIs2) {
                    GCIconcepts2.addAll(axiom.getClassesInSignature());
                    GCIroles2.addAll(axiom.getObjectPropertiesInSignature());
                }
                int GCIrolesize2 = GCIroles2.size();
                int GCIconceptsize2 = GCIconcepts2.size();


                //data

                Set<OWLClass> concepts1 = onto1.getClassesInSignature();
                Set<OWLObjectProperty> roles1 = onto1.getObjectPropertiesInSignature();

                Set<OWLClass> concepts2 = onto2.getClassesInSignature();
                Set<OWLObjectProperty> roles2 = onto2.getObjectPropertiesInSignature();

                //diff data

                Set<OWLClass> c_sig = new LinkedHashSet<>(Sets.difference(concepts2, concepts1));
                Set<OWLObjectProperty> r_sig = new LinkedHashSet<>(Sets.difference(roles2, roles1));
                Set<AtomicRole> role_set = ct.getRolesfromObjectProperties(r_sig);
                Set<AtomicConcept> concept_set = ct.getConceptsfromClasses(c_sig);
                Set<OWLEntity> forgettingSignatures = new HashSet<>();
                forgettingSignatures.addAll(r_sig);
                forgettingSignatures.addAll(c_sig);

                String log = path + "," + path2+","+logicalsize1 + "," +logicalsize2+","+ rolesize1 + "," +rolesize2+","+
                        conceptsize1 + "," +conceptsize2+","+ GCIsize1 + "," + GCIsize2 + "," +GCIrolesize1 + "," +GCIrolesize2 + "," +
                        GCIconceptsize1 + ","+ GCIconceptsize2 + ","+ Sets.difference(roles2,roles1).size()+","+Sets.difference(concepts2,concepts1).size()+","+
                        Sets.intersection(GCIroles2, Sets.difference(roles2,roles1)).size()+","+Sets.intersection(GCIconcepts2, Sets.difference(concepts2,concepts1)).size();


                nowLog = log + "," ;
                System.out.println(nowLog);
                time = 0;
                mem = 0;
                afterForgettingAxiomsSize = 0;
                Forgetter fg = new Forgetter();
                isExtra = 0;
                success = 1;
                witness_explicit_onto = 0;
                witness_implicit_onto = 0;
                elkEntailment.hasChecked_OnO2 = new HashMap<>();
                AtomicConcept.setDefiner_index(1);


                SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(manager1, onto2, ModuleType.STAR);
                Set<OWLAxiom> moduleOnto_2OnCommonSig = extractor.extract(Sets.difference(onto2.getSignature(),forgettingSignatures));
                Set<OWLLogicalAxiom> moduleOnto_2OnCommonSig_logical = new HashSet<>();
                for (OWLAxiom axiom : moduleOnto_2OnCommonSig) {
                    if (axiom instanceof OWLLogicalAxiom) {
                        moduleOnto_2OnCommonSig_logical.add((OWLLogicalAxiom) axiom);
                    }
                }
                System.out.println("module finished");
                List<Formula> formulaList = ct.AxiomsConverter(moduleOnto_2OnCommonSig_logical);
                try {
                    System.gc();
                    Runtime r = Runtime.getRuntime();
                    long mem1 = r.freeMemory();
                    long time1 = System.currentTimeMillis();
                    System.out.println("The forgetting task is to eliminate [" + concept_set.size() + "] concept names and ["
                            + role_set.size() + "] role names from [" + moduleOnto_2OnCommonSig_logical.size() + "] normalized axioms");

                    List<Formula> ui = fg.Forgetting(role_set, concept_set, formulaList, onto2);

                   // elkEntailment.check(onto2,ui);
                    long time2 = System.currentTimeMillis();
                    long mem2 = r.freeMemory();
                    time += (time2 - time1);
                    mem += (mem1 - mem2);
                    Set<OWLAxiom> uniform_interpolant = bc.toOWLAxioms(ui);
                    saveUI(uniform_interpolant,dictPath+path.substring(path.length()-10,path.length()-4)+path2.substring(path2.length()-10,path2.length()-4)+".owl");

                    for(OWLLogicalAxiom axiom : onto2.getLogicalAxioms()){
                        if(Sets.intersection(axiom.getSignature(),forgettingSignatures).size() == 0 ){
                            uniform_interpolant.add(axiom);
                        }
                    }
                    uniform_interpolant = Sets.difference(uniform_interpolant,onto1.getAxioms());
                    afterForgettingAxiomsSize = uniform_interpolant.size();
                    OWLReasoner reasoner =  new ElkReasonerFactory().createReasoner(onto1);
                    int all = 0;
                    for (OWLAxiom axiom : uniform_interpolant) {
                        all++;
                        if(!elkEntailment.entailed(reasoner,axiom)){
                            if (onto2.getAxioms().contains(axiom)) {
                                witness_explicit_onto++;
                                System.out.println("witness_explicit num= " + witness_explicit_onto);
                                System.out.println(uniform_interpolant.size());
                            } else {
                                witness_implicit_onto++;
                                System.out.println("witness_implicit num= " + witness_implicit_onto);
                                System.out.println(uniform_interpolant.size());

                            }
                        }
                        else{
                            System.out.println("it is entailed "+all+" "+uniform_interpolant.size());
                        }
                    }
                    reasoner.dispose();


                } catch (OutOfMemoryError e) {
                    nowLog = nowLog + ",0,0,0,1,0,0,0,0,0\n";
                    writeFile.writeFile(dictPath + filelog, nowLog);
                    System.err.println("outofmemory");
                    e.printStackTrace();
                    success = 0;
                } catch (StackOverflowError e) {
                    nowLog = nowLog + ",0,0,0,2,0,0,0,0,0\n";
                    writeFile.writeFile(dictPath + filelog, nowLog);
                    System.err.println("stackoverflow");
                    success = 0;
                }



                if (success == 1 && isExtra == 0) {
                    nowLog = nowLog + "," + time  + "," + mem / 1024 / 1024  + ",0,0,1,0," + afterForgettingAxiomsSize  + ","+witness_explicit_onto
                    +witness_implicit_onto+"\n";
                    writeFile.writeFile(dictPath + filelog, nowLog);


                }
                if (success == 1 && isExtra != 0) {
                    nowLog = nowLog + ",0,0,0,0,0," + isExtra + ",0,0,0\n";
                    writeFile.writeFile(dictPath + filelog, nowLog);
                }

            }
        }
    }
    public static void tt()throws Exception{
        OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();
        OWLOntologyManager manager2 = OWLManager.createOWLOntologyManager();
        System.out.println("Onto_2 Path: ");
        String filePath2 = "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/ontology_201707.owl";
        OWLOntology onto_2 = manager2.loadOntologyFromOntologyDocument(new File(filePath2));
        String ui = "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/201707201701.owl";
        OWLOntology uniform_interpolant = manager1.loadOntologyFromOntologyDocument(new File(ui));
        System.out.println("onto_2 size = " + onto_2.getLogicalAxiomCount());
        System.out.println("c_sig_2 size = " + onto_2.getClassesInSignature().size());
        System.out.println("r_sig_2 size = " + onto_2.getObjectPropertiesInSignature().size());
        OWLReasoner reasoner2 =  new ElkReasonerFactory().createReasoner(onto_2);
        int num = 0;
        int isnot = 0;
        Set<OWLLogicalAxiom> axioms = uniform_interpolant.getLogicalAxioms();
        for(OWLAxiom axiom : axioms){
            if(!elkEntailment.entailed(reasoner2,axiom)){
                isnot++;
                if(axiom.toString().contains("Definer")){
                    System.out.println("hhhh");
                }
                System.out.println("it is not entailed! "+isnot);
            }
            System.out.println(num+" "+axioms.size());
            num++;
        }
        reasoner2.dispose();


    }
    public static void main(String[] args)throws Exception{
        tt();
        //String dictPath = "/Users/liuzhao/Desktop/experiments/Test_data_for_forgetting/TestData/Corpus_1/";
        //String dictPath = "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/";
        //test3(dictPath);
    }
}
