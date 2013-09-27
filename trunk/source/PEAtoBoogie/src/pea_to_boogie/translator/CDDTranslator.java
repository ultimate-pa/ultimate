package pea_to_boogie.translator;
import pea.*;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.model.*;
public class CDDTranslator {

	 public Expression CDD_To_Boogie(CDD cdd,String fileName, BoogieLocation bl) {
		    BoogieLocation blBoolLiteral = new BoogieLocation (fileName,
         		   0, 0, 0, 0, bl);
		    Expression falseExpr = new BooleanLiteral(blBoolLiteral, false);
		    Expression expr = falseExpr;
	        
		    if (cdd == CDD.TRUE) {	         	     	
	      	    BooleanLiteral bLiteral = new BooleanLiteral(blBoolLiteral, true);
	            return bLiteral;
	        }
	        if (cdd == CDD.FALSE) {
	            return falseExpr;
	        }
	    	CDD[] childs = cdd.getChilds();
	    	Decision decision = cdd.getDecision();
	    	cdd = decision.simplify(childs);
	    	if (cdd == CDD.TRUE) return new BooleanLiteral(blBoolLiteral, true);
	    	if (cdd == CDD.FALSE) return new BooleanLiteral(blBoolLiteral, false);
	    	childs = cdd.getChilds();
	    	decision = cdd.getDecision();
	        for (int i = 0; i < childs.length; i++) {

	        	if (childs[i] == CDD.FALSE) {
	                continue;
	            }
	        	Expression childExpr = CDD_To_Boogie(childs[i],fileName, blBoolLiteral);
	            if (!cdd.childDominates(i)) {
	            	Expression decisionExpr;
	            	if (decision instanceof RangeDecision) {
	            		decisionExpr = 
		            			 toExpressionForRange(i,decision.getVar(), ((RangeDecision) decision).getLimits(),
		         		            			fileName, blBoolLiteral);
	            	} else {
	            		String varName;
	            		
	            		if (decision instanceof BooleanDecision) {
	            			varName = ((BooleanDecision)decision).getVar();
	            		}
	            		else {
	            			varName = ((EventDecision)decision).getEvent();
	            		}
	            		decisionExpr = new IdentifierExpression(bl, varName);
	            		if (i == 1)
	            			decisionExpr = new UnaryExpression(bl, 
	            					UnaryExpression.Operator.LOGICNEG, decisionExpr);
	            	}
	            	if (childExpr instanceof BooleanLiteral
	            		&& ((BooleanLiteral)childExpr).getValue() == true) {
	            		childExpr = decisionExpr;
	            	}
	            	else
		            	childExpr = new BinaryExpression(blBoolLiteral, 
		            			BinaryExpression.Operator.LOGICAND,
		            			decisionExpr, childExpr);
	            }
            	if (expr == falseExpr)
            		expr = childExpr;
            	else
            		expr = new BinaryExpression(blBoolLiteral, 
            				BinaryExpression.Operator.LOGICOR,
            				childExpr, expr);
	        }
	        return expr;	        
	    }
	    public Expression toExpressionForRange(int childs, String var, int[] limits, 
	    		String fileName, BoogieLocation bl ) {
		    BoogieLocation blRangeExpr = new BoogieLocation (fileName,
	         		   0, 0, 0, 0, bl);	
	    	if (childs == 0) {
	    	  IdentifierExpression LHS = new IdentifierExpression(blRangeExpr, var);
	    	  RealLiteral RHS = new RealLiteral(blRangeExpr, Double.toString(limits[0] / 2));
	    	  if ((limits[0] & 1) == 0) {	    		  
	    		return new BinaryExpression(blRangeExpr, BinaryExpression.Operator.COMPLT,
	    				LHS, RHS);
	    	  } else {
		    	return new BinaryExpression(blRangeExpr, BinaryExpression.Operator.COMPLEQ,
		    			LHS, RHS); 
	    	  }
	        }
	  	    
	        if (childs == limits.length) {
		    	  IdentifierExpression LHS = new IdentifierExpression(blRangeExpr, var);
		    	  RealLiteral RHS = new RealLiteral(blRangeExpr, Double.toString(limits[limits.length - 1] / 2));
		    	  if ((limits[limits.length - 1] & 1) == 1) {	    		  
		    		return new BinaryExpression(blRangeExpr, BinaryExpression.Operator.COMPGT,
		    				LHS, RHS);
		    	  } else {
			    	return new BinaryExpression(blRangeExpr, BinaryExpression.Operator.COMPGEQ,
			    			LHS, RHS); 
		    	  }	
	        }

	        if ((limits[childs - 1] / 2) == (limits[childs] / 2)) {
	        	 IdentifierExpression LHS = new IdentifierExpression(blRangeExpr, var);
		    	 RealLiteral RHS = new RealLiteral(blRangeExpr, Double.toString(limits[childs] / 2));
		         return new BinaryExpression(blRangeExpr, BinaryExpression.Operator.COMPEQ,
		    			LHS, RHS);
	        }
	        RealLiteral LHS = new RealLiteral(blRangeExpr, Double.toString(limits[childs - 1] / 2));
	        RealLiteral RHS = new RealLiteral(blRangeExpr, Double.toString(limits[childs] / 2));
	        IdentifierExpression varID = new IdentifierExpression(blRangeExpr, var);
	        BinaryExpression expr = null;
            if ((limits[childs - 1] & 1) == 1  &  (limits[childs] & 1) == 0){
            	
            	BinaryExpression RHS_LT_LT = new BinaryExpression(blRangeExpr, BinaryExpression.Operator.COMPLT,
            			varID, RHS);
            	expr = new BinaryExpression(blRangeExpr, BinaryExpression.Operator.COMPLT, LHS, RHS_LT_LT);
            
            } else if ((limits[childs - 1] & 1) == 1  &  !((limits[childs] & 1) == 0)){
            	
            	BinaryExpression RHS_LT_LTEQ = new BinaryExpression(blRangeExpr, BinaryExpression.Operator.COMPLEQ,
            			varID, RHS);
            	expr = new BinaryExpression(blRangeExpr, BinaryExpression.Operator.COMPLT, LHS, RHS_LT_LTEQ);	
            
            } else if (!((limits[childs - 1] & 1) == 1)  &  ((limits[childs] & 1) == 0)) {
            	
            	BinaryExpression RHS_LTEQ_LT = new BinaryExpression(blRangeExpr, BinaryExpression.Operator.COMPLT,
            			varID, RHS);
            	expr = new BinaryExpression(blRangeExpr, BinaryExpression.Operator.COMPLEQ, LHS, RHS_LTEQ_LT);
            } else if (!((limits[childs - 1] & 1) == 1)  &  !((limits[childs] & 1) == 0)) {
            	
            	BinaryExpression RHS_LTEQ_LTEQ = new BinaryExpression(blRangeExpr, BinaryExpression.Operator.COMPLEQ,
            			varID, RHS);
            	expr = new BinaryExpression(blRangeExpr, BinaryExpression.Operator.COMPLEQ, LHS, RHS_LTEQ_LTEQ);
            }
            return expr;
	    }
	    
}
