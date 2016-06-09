package de.uni_freiburg.informatik.ultimate.PeaToBoogieTranslator;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SystemInformation;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import pea.Phase;
import pea.PhaseEventAutomata;

public class SimplePositiveTestTranslator extends BasicTranslator {
	
	private SystemInformation sysInfo;

	public SimplePositiveTestTranslator(PhaseEventAutomata[] peas, SystemInformation sysInfo) {
		super(peas);
		this.sysInfo = sysInfo;
	} 

	/**
	 * Generate assumption that refers to the initial assignment of all the systems variables.
	 * @param location
	 * @param peas
	 * @return
	 */
	@Override
	protected Expression generateInitialPhaseAssumptionArgument(BoogieLocation location, PhaseEventAutomata[] peas) {
		ArrayList<Expression> conjunction = new ArrayList<Expression>();
		ArrayList<Expression> disjunctsPerPea;
		//generates initialization for peas to start only in state 0
		for(int key: this.initialEdgesAssume.keySet()){
			disjunctsPerPea = new ArrayList<Expression>();
			for(Phase phase: this.initialEdgesAssume.get(key)){
				disjunctsPerPea.add(new BinaryExpression(location, BinaryExpression.Operator.COMPEQ,
						new IdentifierExpression(location, PHASE_COUNTER_PREFIX+key), 
						new IntegerLiteral(location, Integer.toString(this.getNoOfPhase(peas[key], phase)))));
			}
			conjunction.add(this.generateBinaryLogicExpression(location, disjunctsPerPea, BinaryExpression.Operator.LOGICOR));
		}
		for(String var: this.vars){
			conjunction.add(this.sysInfo.getInitialAssignmentPredicate(var));
		}
		return this.generateBinaryLogicExpression(location, conjunction, BinaryExpression.Operator.LOGICAND);
	}

	@Override
	protected ArrayList<Statement> generatePhaseInvariant(PhaseEventAutomata pea, String file, BoogieLocation location, Phase phase) {
		ArrayList<Statement> stmt = super.generatePhaseInvariant(pea, file, location, phase);
		if(phase.getName().equals("sttrap")){ 
			stmt.add(new AssertStatement(location, 
					new BooleanLiteral(location, false)					
					));
		}
		return stmt;
	}
	
	

	
}
