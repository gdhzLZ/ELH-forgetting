package Test;
import java.io.*;
import java.util.*;
import forgetting.*;
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
    public static void main(String[] args){
        String dictPath = "/Users/liuzhao/Desktop/experiments/Test data for forgetting/Test Data/Corpus_1/";
        int circle = 20;
        ArrayList<String> now = getFileName(dictPath);
        System.out.println(now.size());
        String title = "fileName,LogicalAxioms,Roles,Concepts,GCIs,LeftRolesOfGCIs,LeftConceptsOfGCIs,tag,ForgettingRate,Time,T.O,Success,AfterAxioms";
        for(String path : now){

        }
    }
}
