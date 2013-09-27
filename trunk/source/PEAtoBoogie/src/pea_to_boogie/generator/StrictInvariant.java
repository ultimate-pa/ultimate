package pea_to_boogie.generator;

import pea.*;
import pea.RelationDecision.Operator;
import de.uni_freiburg.informatik.ultimate.model.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import java.util.*;
public class StrictInvariant {

	 public CDD genStrictInv(CDD cdd, List<String> resetList) {
	            
		    if (cdd == CDD.TRUE) {	         	     	
	            return CDD.TRUE;
	        }
	        if (cdd == CDD.FALSE) {
	            return CDD.FALSE;
	        }
	        
	    	CDD[] childs = cdd.getChilds();
	    	Decision decision = cdd.getDecision();
            
          	CDD decisionCDD;
          	if (!resetList.contains(decision.getVar())) {
          	   decisionCDD = 
          			toStrictRange(decision.getVar(), ((RangeDecision) decision).getLimits()); 
          	   CDD[] newChilds = new CDD[childs.length];
               for (int i = 0; i < childs.length; i++) {
	        	newChilds[i] = genStrictInv(childs[i],resetList);	            	
	           } 
               return  decisionCDD.getDecision().simplify(newChilds);	
          	} else {
      			assert childs.length == 2;
      			decisionCDD = genStrictInv(childs[0], resetList).or(genStrictInv(childs[1], resetList));

          	}
          	return decisionCDD;       
	    }
	    public CDD toStrictRange(String var, int[] limits) {

            return  RangeDecision.create(var, -2, (limits[0] / 2));  

	    }

}
