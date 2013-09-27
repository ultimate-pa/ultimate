package pea_to_boogie.translator;
import java.util.*;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import pea.*;

import java.util.*;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.ASTNode;
import de.uni_freiburg.informatik.ultimate.model.*;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.*;
public class PlayWithCDD {
	public void CDDGame() {
		
		 CDD A  = BooleanDecision.create("A");
		 CDD B  = BooleanDecision.create("B");
		 CDD C  = BooleanDecision.create("C");
		 CDD D = CDD.FALSE;
		 CDD range1 = RangeDecision.create("E", RangeDecision.OP_GTEQ, 3);
		 CDD range2 = RangeDecision.create("F", RangeDecision.OP_LTEQ, 6);
		 CDD G  = BooleanDecision.create("G");
		 CDD k = RangeDecision.create("C", RangeDecision.OP_LT, 3);
		 CDD L = RangeDecision.create("0", RangeDecision.OP_LT, 5);
		 System.out.println(k.and(L));
	//	 CDD conjunction = (A.and(B.negate().or(C).or(G)).or(D)).and(range1).and(range2);
	//	 CDD conjunction = (A.or(G));
	//	 CDD conjunction = A.and(B).and(C).or(G);
	//	 CDD conjunction = A.or(G).and((B));
	//	 System.out.println(A.and(A.negate()).and(B).and(C));
	//	 System.out.println(toString(conjunction,false));
	


	}
    public String toString(CDD cdd, boolean needsParens) {
        StringBuffer sb = new StringBuffer();
        String ordelim = "";
        int clauses = 0;

        if (cdd == CDD.TRUE) {
            return "true";
        }

        if (cdd == CDD.FALSE) {
            return "false";
        }
    	CDD[] childs = cdd.getChilds();
    	Decision decision = cdd.getDecision(); 
    	for (int i = 0; i < childs.length; i++) {
    		System.out.println(childs[i]);
    	}
    	System.out.println("/////////////////////////");
    	System.out.println(decision.getVar());
    	System.out.println("/////////////////////////");
        for (int i = 0; i < childs.length; i++) {
            if (childs[i] == CDD.FALSE) {
                continue;
            }

            sb.append(ordelim);
            if (cdd.childDominates(i)) {
                sb.append(toString(childs[i],true));
                         
            } else {
            	if (decision instanceof RangeDecision) {
            		sb.append(toStringForRange(i,decision.getVar(),
            				 ((RangeDecision) decision).getLimits()));
            	} else {
                    sb.append(decision.toString(i));
            	}
                if (childs[i] != CDD.TRUE) {
                    sb.append(" && ").append(toString(childs[i],false));
                }
            	
            }

            ordelim = " || ";
            clauses++;
        }

    //    if (needsParens && (clauses > 1)) {
     //       return "(" + sb + ")";
     //   } else {

            return sb.toString();
      //  }
        
    }
    public String toStringForRange(int childs, String var, int[] limits) {
        if (childs == 0) {
            return var + (((limits[0] & 1) == 0) ? " < " : " <= ") +
            (limits[0] / 2);
        }

        if (childs == limits.length) {
            return var +
            (((limits[limits.length - 1] & 1) == 1) ? " > " : " >= ") +
            (limits[limits.length - 1] / 2);
        }

        if ((limits[childs - 1] / 2) == (limits[childs] / 2)) {
            return var + " == " + (limits[childs] / 2);
        }

        return "" + (limits[childs - 1] / 2) +
        (((limits[childs - 1] & 1) == 1) ? " < " : " <= ") + var +
        (((limits[childs] & 1) == 0) ? " < " : " <= ") +
        (limits[childs] / 2);
    }

}
