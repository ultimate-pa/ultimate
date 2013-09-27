package pea_to_boogie.generator;
import pea.*;
import pea_to_boogie.translator.CDDTranslator;
import pea_to_boogie.translator.Translator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.model.*;

import java.util.*;
public class ConditionGenerator {
    public Translator translator;
    public Expression nonDLCGenerator (PhaseEventAutomata[] automata, List<Integer> automataPermutation, String fileName, 
			BoogieLocation bl) {

	    BoogieLocation blAssert = new BoogieLocation (fileName,
      		   0, 0, 0, 0, bl);
	    
		 
		Expression result = new BooleanLiteral(blAssert, true);
		List<List<Integer>> phasePermutations = new ArrayList<List<Integer>>();
		for(int i = automataPermutation.size(); i > 0; i--) {
			PhaseEventAutomata automaton = automata[automataPermutation.get(i - 1)];
			Phase[] phases = automaton.getPhases(); 
			List<Integer> tempList = new ArrayList<Integer>();
			for(int j = 0; j < phases.length; j++) {
				tempList.add(j);
			}
			phasePermutations.add(tempList);
		}
		
		phasePermutations = new Permutation().allPermutations(phasePermutations, 1);
		
		if (automataPermutation.size() == 1) {

        	PhaseEventAutomata automaton = automata[automataPermutation.get(0)];
        	Phase[] phases = automaton.getPhases(); 
        	List<CDD> cddList = new ArrayList<CDD>();
        	int trueCounter = 0;
        	int trueRemoval = 0;
        	for (int i = 0; i < phases.length; i++) {

           		List<Transition> transitions = phases[i].getTransitions();
           		for (int k = 0; k < transitions.size(); k++) {
                     CDD cddInner = genIntersectionAll (genGuardANDPrimedStInv(transitions.get(k)),
                    		   genStrictInv(transitions.get(k)));
                     cddList.add(cddInner);
            	}
           	  CDD cdd = genOr(cddList, 1);
           	  cdd = new VarRemoval().excludeEventsAndPrimedVars(cdd, this.translator.primedVars);
           	  if (cdd == CDD.TRUE) {
           		  trueRemoval++;
           		  continue;
           	  }
           	  trueCounter ++;
           	  Expression impliesRHS = new CDDTranslator().CDD_To_Boogie(cdd, fileName, blAssert);
              Expression implies = new BinaryExpression(blAssert, BinaryExpression.Operator.LOGICIMPLIES,
      				 genPCCompEQ(automataPermutation.get(0), i, fileName, blAssert), impliesRHS);
              cddList.clear();
              if (trueCounter == 1) {
            	  result = implies;
              }
              else {
           	      result = new BinaryExpression(blAssert, BinaryExpression.Operator.LOGICAND,
     				 implies, result);
              }
        	}
        	if (trueRemoval == phases.length) return null; // thereby, ignoring 'assert true'. 
        } 
        else { // automata in parallel
        int trueCounter = 0;
        int trueRemoval = 0;
		for (int i = 0; i < phasePermutations.size(); i++) {
            List<Integer> list = new ArrayList<Integer>();
            list = phasePermutations.get(i);
    		List<CDD> cddListInner = new ArrayList<CDD>();
    		List<CDD> cddListOuter = new ArrayList<CDD>();
    		Expression impliesLHS = new BooleanLiteral(blAssert, true);
        	for (int j = 0; j < list.size(); j++) {
        		PhaseEventAutomata automaton = automata[automataPermutation.get(j)];
        		Phase[] phases = automaton.getPhases(); 
        		Phase phase = phases[list.get(j)];
           		List<Transition> transitions = phase.getTransitions();
           		for (int k = 0; k < transitions.size(); k++) {
                     CDD cddInner = genIntersectionAll(genGuardANDPrimedStInv(transitions.get(k)),
                    		   genStrictInv(transitions.get(k)));  
                   
                     cddListInner.add(cddInner);
            	}
           		CDD OrCDDInner = genOr(cddListInner, 1);
           		cddListOuter.add(OrCDDInner);
           		cddListInner.clear();
           		if (j == 0) {
           			impliesLHS = genPCCompEQ(automataPermutation.get(j), list.get(j), fileName, blAssert);
           		}
           		else {
            	    impliesLHS = new BinaryExpression(blAssert, BinaryExpression.Operator.LOGICAND,
       				    genPCCompEQ(automataPermutation.get(j), list.get(j), fileName, blAssert), impliesLHS); 
           		}
        	}
        	    CDD AndCDDOuter = genAnd(cddListOuter, 1);
        	    CDD cdd = new VarRemoval().excludeEventsAndPrimedVars(AndCDDOuter, this.translator.primedVars);
        	    if (cdd == CDD.TRUE) {
        	    	trueRemoval++;
        	    	continue;
        	    }
        	    trueCounter ++;
             	Expression impliesRHS = new CDDTranslator().CDD_To_Boogie(cdd, fileName, blAssert);
                Expression implies = new BinaryExpression(blAssert, BinaryExpression.Operator.LOGICIMPLIES,
                		  impliesLHS , impliesRHS);
                if (trueCounter == 1) {
                	result = implies;
                }else {
                    result = new BinaryExpression(blAssert, BinaryExpression.Operator.LOGICAND,
         		       implies, result);
                }
        }
		if (trueRemoval == phasePermutations.size()) return null;
       }
      return result;
        
	}
 /*   
	public Expression nonDLCGeneratorToy (PhaseEventAutomata[] automata, String fileName, 
			BoogieLocation bl) {

	    BoogieLocation blAssert = new BoogieLocation (fileName,
      		   0, 0, 0, 0, bl);

		Expression OrExprOuter = new BooleanLiteral(blAssert, false);
		Expression ANDExprInner = new BooleanLiteral(blAssert, true);
		Expression ANDExprOuter = new BooleanLiteral(blAssert, true);
		CDD OrCDDInner = CDD.FALSE;
		CDD AndCDDInner = CDD.TRUE;
		
        for (int i = 0; i < automata.length; i++) {
        	PhaseEventAutomata automaton = automata[i];
        	Phase[] phases = automaton.getPhases(); 
        	for (int j = 0; j < phases.length; j++) {
        		List<Transition> transitions = phases[j].getTransitions();
        		for (int k = 0; k < transitions.size(); k++) {
                   CDD cddInner = genPropsIntersection (genGuardANDPrimedStInv(transitions.get(k)),
                		   genStrictInv(transitions.get(k)));	
                   OrCDDInner = OrCDDInner.or(cddInner);
        		}
        		   AndCDDInner = genPCCompEQ(i, j).and(OrCDDInner);
        		   OrCDDInner = CDD.FALSE;
        		   ANDExprInner = new CDDTranslator().CDD_To_Boogie(AndCDDInner, fileName, blAssert);
        		   if (j == 0) {
        			   OrExprOuter =  ANDExprInner;
        		   }
        		   else {
        		     OrExprOuter = new BinaryExpression(bl, BinaryExpression.Operator.LOGICOR,
         	     		ANDExprInner, OrExprOuter);
        		   }
        	}
        	if (i == 0) {
        		ANDExprOuter = OrExprOuter;
        	}
        	else {
            	ANDExprOuter = new BinaryExpression(bl, BinaryExpression.Operator.LOGICAND,
       				 OrExprOuter, ANDExprOuter);
        	}     	
        }
		return ANDExprOuter;
	}
*/
	public void setTranslator(Translator translator) {
		this.translator = translator;
	}
	public CDD genIntersectionAll (CDD cdd1, CDD cdd2) {
		return (cdd1.and(cdd2));
	}
	public CDD genStrictInv(Transition transition) {
	    Phase phase = transition.getDest();
	    String[] resetVars = transition.getResets();
	    List<String> resetList = new ArrayList<String>();
	    for (int i = 0; i < resetVars.length; i++) {
	    	resetList.add(resetVars[i]);
	    }
	    CDD cdd = new StrictInvariant().genStrictInv(phase.getClockInvariant(), resetList);
  	    return cdd;
	}
	public CDD genGuardANDPrimedStInv(Transition transition) {
		CDD guard = transition.getGuard();
		Phase phase = transition.getDest();
		CDD primedStInv = phase.getStateInvariant().prime();
		CDD cdd = guard.and(primedStInv);
	//	cdd = new VarRemoval().varRemoval(cdd, this.translator.primedVars, this.translator.eventVars);
		return cdd;
	}
	public CDD genOr(List<CDD> list, int counter) {
		if(list.size() == 0) {
			return CDD.FALSE; // in practice all phases have at least one transition (self loop). 
		}
		if(list.size() == 1) {
			return list.get(0);
		}
		if(counter == list.size()) {
			return list.get(counter - 1);
		}
		CDD result = list.get(counter - 1);
		result = result.or(genOr(list, counter + 1));
		return result;
	}
	public CDD genAnd(List<CDD> list, int counter) {
		if(list.size() == 0) {
			return CDD.FALSE; // in practice all phases have at least one transition (self loop). 
		}
		if(counter == list.size()) {
			return list.get(counter - 1);
		}
		CDD result = list.get(counter - 1);
		result = result.and(genAnd(list, counter + 1));
		return result;
	}
    public Expression genPCCompEQ(int autIndex, int phaseIndex, String fileName, BoogieLocation bl) {
		    BoogieLocation blLHS = new BoogieLocation (fileName,
	      		   0, 0, 0, 0, bl);
	     	BoogieLocation blRHS = new BoogieLocation (fileName,
	       		   0, 0, 0, 0, bl);
	     	IdentifierExpression identifier = new IdentifierExpression(blLHS, "pc"+autIndex);
	     	IntegerLiteral intLiteral = new IntegerLiteral(blRHS, Integer.toString(phaseIndex));
	     	BinaryExpression binaryExpr = new BinaryExpression(bl, BinaryExpression.Operator.COMPEQ,
	     			identifier, intLiteral);
    	 return binaryExpr;  	    
    }
    
}