package checkTautology;

import concepts.AtomicConcept;
import connectives.*;
import formula.Formula;
import java.util.*;
public class TautologyChecker {
    public TautologyChecker(){

    }
    public static boolean  isTautology(Formula formula){
        Formula left = formula.getSubFormulas().get(0);
        Formula right = formula.getSubFormulas().get(1);

        if(formula instanceof Inclusion && (left instanceof And) && left.getSubformulae().contains(right)){
            return true;
        }
        else if(formula instanceof  Inclusion && left.equals(right)) return true;
        return false;
    }

}
