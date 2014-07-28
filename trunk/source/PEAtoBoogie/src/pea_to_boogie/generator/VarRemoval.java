package pea_to_boogie.generator;

import pea.*;
import java.util.*;
public class VarRemoval {
	
	public CDD getRangeCDDs (CDD cdd) {
		
	    if (cdd == CDD.TRUE) {	         	     	
            return CDD.TRUE;
        }
        if (cdd == CDD.FALSE) {
            return CDD.FALSE;
        }
        
    	CDD[] childs = cdd.getChilds();
    	Decision decision = cdd.getDecision();
    	CDD decisionCDD = CDD.TRUE;
      	if (decision instanceof RangeDecision) {
      	   CDD[] newChilds = new CDD[childs.length];
           for (int i = 0; i < childs.length; i++) {
        	newChilds[i] = getRangeCDDs(childs[i]);	            	
           } 
           return  cdd.getDecision().simplify(newChilds);	
      	} else {
  			assert childs.length == 2;
  		    decisionCDD = getRangeCDDs(childs[0]).or(getRangeCDDs(childs[1]));
      	}
      	return decisionCDD;       
    }
	public CDD excludeRangeCDDs (CDD cdd) {
		
	    if (cdd == CDD.TRUE) {	         	     	
            return CDD.TRUE;
        }
        if (cdd == CDD.FALSE) {
            return CDD.FALSE;
        }
        
    	CDD[] childs = cdd.getChilds();
    	Decision decision = cdd.getDecision();
    	CDD decisionCDD = CDD.TRUE;
      	if (decision instanceof RangeDecision) {
  			assert childs.length == 2;
  		    decisionCDD = excludeRangeCDDs (childs[0]).or(excludeRangeCDDs (childs[1]));
      	} else {
       	   CDD[] newChilds = new CDD[childs.length];
           for (int i = 0; i < childs.length; i++) {
        	newChilds[i] = excludeRangeCDDs (childs[i]);	            	
           } 
           return  cdd.getDecision().simplify(newChilds);
      	}
      	return decisionCDD;       
    }
	public CDD excludeEventsAndPrimedVars (CDD cdd, List<String> primedVars) {
	    if (cdd == CDD.TRUE) {	         	     	
            return CDD.TRUE;
        }
        if (cdd == CDD.FALSE) {
            return CDD.FALSE;
        }
        
    	CDD[] childs = cdd.getChilds();
    	Decision decision = cdd.getDecision();
    	CDD decisionCDD = CDD.TRUE;
      	if (decision instanceof RangeDecision || (decision instanceof BooleanDecision & !primedVars.contains(decision.getVar()))) {
      	   CDD[] newChilds = new CDD[childs.length];
           for (int i = 0; i < childs.length; i++) {
        	newChilds[i] =  excludeEventsAndPrimedVars(childs[i], primedVars);	            	
           } 
           return  cdd.getDecision().simplify(newChilds);	
      	} else {
  			assert childs.length == 2;
  		    decisionCDD =  excludeEventsAndPrimedVars (childs[0], primedVars).or( excludeEventsAndPrimedVars(childs[1], primedVars));
      	}
      	return decisionCDD; 
	}
	public CDD getUnPrimedVars (CDD cdd, List<String> stateVars) {
	    if (cdd == CDD.TRUE) {	         	     	
            return CDD.TRUE;
        }
        if (cdd == CDD.FALSE) {
            return CDD.FALSE;
        }
        
    	CDD[] childs = cdd.getChilds();
    	Decision decision = cdd.getDecision();
    	CDD decisionCDD = CDD.TRUE;
      	if (decision instanceof BooleanDecision & stateVars.contains(decision.getVar())) {
      	   CDD[] newChilds = new CDD[childs.length];
           for (int i = 0; i < childs.length; i++) {
        	newChilds[i] = getUnPrimedVars(childs[i], stateVars);	            	
           } 
           return  cdd.getDecision().simplify(newChilds);	
      	} else {
  			assert childs.length == 2;
  		    decisionCDD = getUnPrimedVars (childs[0], stateVars).or(getUnPrimedVars(childs[1], stateVars));
      	}
      	return decisionCDD; 
	} 

}
