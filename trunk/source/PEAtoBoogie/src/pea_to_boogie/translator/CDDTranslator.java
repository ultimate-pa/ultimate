package pea_to_boogie.translator;
import pea.*;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.model.location.BoogieLocation;
public class CDDTranslator {

	 public Expression CDD_To_Boogie(CDD cdd,String fileName, BoogieLocation bl) {
		    Expression falseExpr = new BooleanLiteral(bl, false);
		    Expression expr = falseExpr;
	        
		    if (cdd == CDD.TRUE) {	         	     	
	      	    BooleanLiteral bLiteral = new BooleanLiteral(bl, true);
	            return bLiteral;
	        }
	        if (cdd == CDD.FALSE) {
	            return falseExpr;
	        }
	    	CDD[] childs = cdd.getChilds();
	    	Decision decision = cdd.getDecision();
	    	cdd = decision.simplify(childs);
	    	if (cdd == CDD.TRUE) return new BooleanLiteral(bl, true);
	    	if (cdd == CDD.FALSE) return new BooleanLiteral(bl, false);
	    	childs = cdd.getChilds();
	    	decision = cdd.getDecision();
	        for (int i = 0; i < childs.length; i++) {

	        	if (childs[i] == CDD.FALSE) {
	                continue;
	            }
	        	Expression childExpr = CDD_To_Boogie(childs[i],fileName, bl);
	            if (!cdd.childDominates(i)) {
	            	Expression decisionExpr;
	            	if (decision instanceof RangeDecision) {
	            		decisionExpr = 
		            			 toExpressionForRange(i,decision.getVar(), ((RangeDecision) decision).getLimits(),
		         		            			fileName, bl);
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
		            	childExpr = new BinaryExpression(bl, 
		            			BinaryExpression.Operator.LOGICAND,
		            			decisionExpr, childExpr);
	            }
            	if (expr == falseExpr)
            		expr = childExpr;
            	else
            		expr = new BinaryExpression(bl, 
            				BinaryExpression.Operator.LOGICOR,
            				childExpr, expr);
	        }
	        return expr;	        
	    }
	    public Expression toExpressionForRange(int childs, String var, int[] limits, 
	    		String fileName, BoogieLocation bl ) {
	    	if (childs == 0) {
	    	  IdentifierExpression LHS = new IdentifierExpression(bl, var);
	    	  RealLiteral RHS = new RealLiteral(bl, Double.toString(limits[0] / 2));
	    	  if ((limits[0] & 1) == 0) {	    		  
	    		return new BinaryExpression(bl, BinaryExpression.Operator.COMPLT,
	    				LHS, RHS);
	    	  } else {
		    	return new BinaryExpression(bl, BinaryExpression.Operator.COMPLEQ,
		    			LHS, RHS); 
	    	  }
	        }
	  	    
	        if (childs == limits.length) {
		    	  IdentifierExpression LHS = new IdentifierExpression(bl, var);
		    	  RealLiteral RHS = new RealLiteral(bl, Double.toString(limits[limits.length - 1] / 2));
		    	  if ((limits[limits.length - 1] & 1) == 1) {	    		  
		    		return new BinaryExpression(bl, BinaryExpression.Operator.COMPGT,
		    				LHS, RHS);
		    	  } else {
			    	return new BinaryExpression(bl, BinaryExpression.Operator.COMPGEQ,
			    			LHS, RHS); 
		    	  }	
	        }

	        if ((limits[childs - 1] / 2) == (limits[childs] / 2)) {
	        	 IdentifierExpression LHS = new IdentifierExpression(bl, var);
		    	 RealLiteral RHS = new RealLiteral(bl, Double.toString(limits[childs] / 2));
		         return new BinaryExpression(bl, BinaryExpression.Operator.COMPEQ,
		    			LHS, RHS);
	        }
	        RealLiteral LHS = new RealLiteral(bl, Double.toString(limits[childs - 1] / 2));
	        RealLiteral RHS = new RealLiteral(bl, Double.toString(limits[childs] / 2));
	        IdentifierExpression varID = new IdentifierExpression(bl, var);
	        BinaryExpression expr = null;
            if ((limits[childs - 1] & 1) == 1  &  (limits[childs] & 1) == 0){
            	
            	BinaryExpression RHS_LT_LT = new BinaryExpression(bl, BinaryExpression.Operator.COMPLT,
            			varID, RHS);
            	expr = new BinaryExpression(bl, BinaryExpression.Operator.COMPLT, LHS, RHS_LT_LT);
            
            } else if ((limits[childs - 1] & 1) == 1  &  !((limits[childs] & 1) == 0)){
            	
            	BinaryExpression RHS_LT_LTEQ = new BinaryExpression(bl, BinaryExpression.Operator.COMPLEQ,
            			varID, RHS);
            	expr = new BinaryExpression(bl, BinaryExpression.Operator.COMPLT, LHS, RHS_LT_LTEQ);	
            
            } else if (!((limits[childs - 1] & 1) == 1)  &  ((limits[childs] & 1) == 0)) {
            	
            	BinaryExpression RHS_LTEQ_LT = new BinaryExpression(bl, BinaryExpression.Operator.COMPLT,
            			varID, RHS);
            	expr = new BinaryExpression(bl, BinaryExpression.Operator.COMPLEQ, LHS, RHS_LTEQ_LT);
            } else if (!((limits[childs - 1] & 1) == 1)  &  !((limits[childs] & 1) == 0)) {
            	
            	BinaryExpression RHS_LTEQ_LTEQ = new BinaryExpression(bl, BinaryExpression.Operator.COMPLEQ,
            			varID, RHS);
            	expr = new BinaryExpression(bl, BinaryExpression.Operator.COMPLEQ, LHS, RHS_LTEQ_LTEQ);
            }
            return expr;
	    }
	    
}
