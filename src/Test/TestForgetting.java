package Test;
import java.io.*;
import java.util.*;

import com.google.common.collect.Sets;
import concepts.AtomicConcept;
import convertion.BackConverter;
import convertion.Converter;
import forgetting.*;
import formula.Formula;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
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
    /*
    public static void test(String dictPath)throws Exception{
        String title = "fileName,LogicalAxiomsSize,RolesSize,ConceptsSize,GCISize,GCIRolesSize,GCIConceptSize,isTestGCIForgetting,rate,time,timeOut,MemoryOut" +
                "isSuccess,isExtra,afterForgettingAxiomsSize\n";
        writeFile.writeFile(dictPath+"log.txt",title);
        Converter ct = new Converter();
        BackConverter bc = new BackConverter();
        int circle = 1;
        int isTestGCIForgetting = 0;
        ArrayList<String> now = getFileName(dictPath);
        double []rates = new double[]{0.1,0.3,0.5,0.7};
        for(String path : now){

            OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();
            OWLOntology onto = manager1.loadOntologyFromOntologyDocument(new File(path));

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
                String nowLog = log+","+rate;
                double time = 0;
                System.out.println(nowLog);
                int success = 1;
                int afterForgettingAxiomsSize = 0;
                for(int i = 0 ; i < circle ; i++){
                    Forgetter fg = new Forgetter();
                    isExtra = 0;
                    try {

                        List<OWLClass> forgettingConcepts = getSubStringByRadom2(conceptList, (int) (rate * conceptsize));
                        List<OWLObjectProperty> forgettingRoles = getSubStringByRadom1(roleList, (int) (rate * rolesize));
                        Set<OWLEntity> forgettingSignatures = Sets.union(new HashSet<>(forgettingConcepts), new HashSet<>(forgettingRoles));
                        SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(manager1, onto, ModuleType.BOT);
                        Set<OWLAxiom> moduleOnto_2OnForgettingSig = extractor.extract(Sets.difference(onto.getSignature(), forgettingSignatures));
                        Set<OWLLogicalAxiom> moduleOnto_2OnCommonSig_logical = new HashSet<>();

                        for (OWLAxiom axiom : moduleOnto_2OnForgettingSig) {
                            if (axiom instanceof OWLLogicalAxiom) {
                                moduleOnto_2OnCommonSig_logical.add((OWLLogicalAxiom) axiom);
                            }
                        }
                        List<Formula> formulaList = ct.AxiomsConverter(moduleOnto_2OnCommonSig_logical);
                        Set<AtomicRole> roleSet = ct.getRolesfromObjectProperties(new HashSet<>(forgettingRoles));
                        Set<AtomicConcept> conceptSet = ct.getConceptsfromClasses(new HashSet<>(forgettingConcepts));
                        long time1 = System.currentTimeMillis();
                        List<Formula> ui = fg.Forgetting(roleSet, conceptSet, formulaList, onto);
                        long time2 = System.currentTimeMillis();
                        afterForgettingAxiomsSize+=ui.size();
                        elkEntailment.check(onto,ui);

                        time += (time2 - time1);
                        System.out.println("ui size " + ui.size());
                        System.out.println(time);
                    }

                    catch (StackOverflowError e){
                        nowLog = nowLog+",0,0,1,0,0,0\n";
                        writeFile.writeFile(dictPath+"log.txt",nowLog);
                        success = 0;
                        break;
                    }
                    catch (OutOfMemoryError e){
                        nowLog = nowLog+",0,0,1,0,0,0\n";
                        writeFile.writeFile(dictPath+"log.txt",nowLog);
                        success = 0;
                        break;
                    }
                    if(isExtra == 1) break;

                }
                if(success == 1 && isExtra == 0){
                    nowLog = nowLog+","+time*1.0/circle+",0,0,1,0,"+afterForgettingAxiomsSize/circle+"\n";
                    writeFile.writeFile(dictPath+"log.txt",nowLog);


                }
                if(success == 1 && isExtra == 1){
                    nowLog = nowLog+",,0,0,0,0,1,0\n";
                    writeFile.writeFile(dictPath+"log.txt",nowLog);
                }
            }

        }
    }

     */
    public static int afterForgettingAxiomsSize = 0;
    public static OWLOntology onto = null;
    public static int time = 0;
    public static int isExtra = 0;

    public static int success = 0;
    public static String nowLog = null;

    public static void test2(String dictPath)throws Exception{
        double Rate = 0.3;
        String filelog = "log"+Rate+"_2.txt";
        ArrayList<String> hasRecord = readFile.readFile(dictPath+filelog);

        String title = "fileName,LogicalAxiomsSize,RolesSize,ConceptsSize,GCISize,GCIRolesSize,GCIConceptSize,isTestGCIForgetting,rate,time,timeOut,MemoryOut," +"isSuccess,isExtra,afterForgettingAxiomsSize\n";
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
                                long time1 = System.currentTimeMillis();
                                List<Formula> ui = fg.Forgetting(roleSet, conceptSet, formulaList, onto);
                                //elkEntailment.check(onto,ui);
                                long time2 = System.currentTimeMillis();
                                afterForgettingAxiomsSize += ui.size();
                                time += (time2 - time1);
                            } catch (OutOfMemoryError e){
                                nowLog = nowLog+",0,0,1,0,0,0\n";
                                writeFile.writeFile(dictPath+filelog,nowLog);
                                System.err.println("outofmemory");

                                success = 0;
                            }

                            catch (StackOverflowError e){
                                nowLog = nowLog+",0,0,2,0,0,0\n";
                                writeFile.writeFile(dictPath+filelog,nowLog);
                                System.err.println("stackoverflow");
                                success = 0;
                            }




                            return 1;
                        }
                    };

                    Future<Integer> future = exec.submit(task);
                    try{
                        int t = future.get(1000 * 1200,TimeUnit.MILLISECONDS);
                    }

                    catch (OutOfMemoryError e){
                        nowLog = nowLog+",0,0,1,0,0,0\n";
                        writeFile.writeFile(dictPath+filelog,nowLog);
                        System.err.println("outofmemory2");

                        success = 0;
                        break;
                    }
                    catch (TimeoutException e){
                        nowLog = nowLog+",0,1,0,0,0,0\n";
                        writeFile.writeFile(dictPath+filelog,nowLog);
                        System.err.println("timeout");
                        success = 0;
                        break;
                    }

                    if(success == 0 || isExtra != 0) break;

                }
                if(success == 1 && isExtra == 0){
                    nowLog = nowLog+","+time*1.0/circle+",0,0,1,0,"+afterForgettingAxiomsSize/circle+"\n";
                    writeFile.writeFile(dictPath+filelog,nowLog);


                }
                if(success == 1 && isExtra != 0){
                    nowLog = nowLog+",0,0,0,0,"+isExtra+",0\n";
                    writeFile.writeFile(dictPath+filelog,nowLog);
                }
            }
            System.gc();
        }
    }
    public static void main(String[] args)throws Exception{

        String dictPath = "/Users/liuzhao/Desktop/experiments/Test_data_for_forgetting/TestData/Corpus_1/";
        test2(dictPath);
    }
}
