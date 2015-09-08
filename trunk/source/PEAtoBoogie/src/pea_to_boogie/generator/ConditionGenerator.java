/*
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 * 
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission 
 * to convey the resulting work.
 */
package pea_to_boogie.generator;
import pea.*;
import pea_to_boogie.translator.CDDTranslator;
import pea_to_boogie.translator.Translator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.location.BoogieLocation;
import java.util.*;
public class ConditionGenerator {
    public Translator translator;
    public Expression nonDLCGenerator (PhaseEventAutomata[] automata, int[] automataPermutation, String fileName, 
			BoogieLocation bl) {

		int[][] phases = new int[automataPermutation.length][];
		for (int i = 0; i < automataPermutation.length; i++) {
			PhaseEventAutomata automaton = automata[automataPermutation[i]];
			int phaseCount = automaton.getPhases().length;
			phases[i] = new int[phaseCount];
			for (int j = 0; j < phaseCount; j++)
				phases[i][j] = j;
		}
		
		List<int[]> phasePermutations = new Permutation().crossProduct(phases);
		List<Expression> conditions = new ArrayList<Expression>();
		for (int[] vector : phasePermutations) {
			assert(vector.length == automataPermutation.length);
			CDD cddOuter = CDD.TRUE;
    		List<Expression> impliesLHS = new ArrayList<Expression>();
        	for (int j = 0; j < vector.length; j++) {
    			CDD cddInner = CDD.FALSE;
        		PhaseEventAutomata automaton = automata[automataPermutation[j]];
        		Phase phase = automaton.getPhases()[vector[j]];
           		List<Transition> transitions = phase.getTransitions();
           		for (int k = 0; k < transitions.size(); k++) {
           			cddInner = cddInner
           				.or(genIntersectionAll(genGuardANDPrimedStInv(transitions.get(k)),
                    		   genStrictInv(transitions.get(k))));  
            	}
           		cddOuter = cddOuter.and(cddInner);
           		impliesLHS.add(genPCCompEQ(automataPermutation[j], vector[j], fileName, bl));
        	}
       	    CDD cdd = new VarRemoval().excludeEventsAndPrimedVars(cddOuter, this.translator.primedVars);
       	    if (cdd == CDD.TRUE) {
       	    	continue;
       	    }
       	    Expression impliesRHS = new CDDTranslator().CDD_To_Boogie(cdd, fileName, bl);
       	    Expression implies = new BinaryExpression(bl, BinaryExpression.Operator.LOGICIMPLIES,
       	    		buildBinaryExpression(bl, BinaryExpression.Operator.LOGICAND, impliesLHS), impliesRHS);
       	    conditions.add(implies);
		}
		if (conditions.isEmpty())
			return null;
		return buildBinaryExpression(bl, BinaryExpression.Operator.LOGICAND, conditions);
	}
    
    private Expression buildBinaryExpression(BoogieLocation bl,
			Operator op, List<Expression> conditions) {
    	assert (!conditions.isEmpty());
    	int offset = conditions.size() - 1;
    	Expression result = conditions.get(offset);
    	while (offset > 0) {
    		offset--;
    		result = new BinaryExpression(bl, op, conditions.get(offset), result);
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
    public Expression genPCCompEQ(int autIndex, int phaseIndex, String fileName, BoogieLocation bl) {
	     	IdentifierExpression identifier = new IdentifierExpression(bl, "pc"+autIndex);
	     	IntegerLiteral intLiteral = new IntegerLiteral(bl, Integer.toString(phaseIndex));
	     	BinaryExpression binaryExpr = new BinaryExpression(bl, BinaryExpression.Operator.COMPEQ,
	     			identifier, intLiteral);
    	 return binaryExpr;  	    
    }
    
}
