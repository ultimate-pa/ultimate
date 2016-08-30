package de.uni_freiburg.informatik.ultimate.PeaToBoogieTranslator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.PeaSystemModel;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SystemInformation;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.DeductionGuardTransformation;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import pea.BoogieBooleanExpressionDecision;
import pea.CDD;
import pea.CounterTrace;
import pea.CounterTrace.DCPhase;
import pea_to_boogie.translator.CDDTranslator;
import pea.Phase;
import pea.PhaseEventAutomata;
import pea.PhaseSet;

public class SimplePositiveTestTranslator extends BasicTranslator {
	
	protected ArrayList<PhaseEventAutomata> peas;
	protected HashSet<Phase> finalPhases = new HashSet<Phase>();
	protected PeaSystemModel model;
	
	private SystemInformation sysInfo;

	public SimplePositiveTestTranslator(PeaSystemModel model) {
		super(model);
		this.sysInfo = model.getSystemInformation();
		this.peas = model.getPeas();
		this.model = model;
		this.setTargetPhase(model.getCounterTraces());
	} 
	
	/***
	 * Grabs the final phase of the last PEA. Can be used to generate the 
	 * assert false in a final phase.
	 * @param counterTraces 
	 */
	private void setTargetPhase(ArrayList<CounterTrace> counterTraces){
		// peas already was altered, patterns has the right number
		PhaseEventAutomata pea = peas.get(counterTraces.size()-1);
		this.finalPhases.addAll( this.model.getFinalPhases(pea));
	}

	/**
	 * Generate assumption that refers to the initial assignment of all the systems variables.
	 * @param location
	 * @param peas
	 * @return
	 */
	@Override 
	protected Expression generateInitialPhaseAssumptionArgument(BoogieLocation location, ArrayList<PhaseEventAutomata> peas) {
		ArrayList<Expression> conjunction = new ArrayList<Expression>();
		ArrayList<Expression> disjunctsPerPea;
		//generates initialization for peas to start only in state 0
		for(int key: this.initialEdgesAssume.keySet()){
			disjunctsPerPea = new ArrayList<Expression>();
			for(Phase phase: this.initialEdgesAssume.get(key)){
				disjunctsPerPea.add(new BinaryExpression(location, BinaryExpression.Operator.COMPEQ,
						new IdentifierExpression(location, PHASE_COUNTER_PREFIX+key), 
						new IntegerLiteral(location, Integer.toString(this.getNoOfPhase(peas.get(key), phase)))));
			}
			conjunction.add(this.generateBinaryLogicExpression(location, disjunctsPerPea, BinaryExpression.Operator.LOGICOR));
		}
		for(String var: this.vars){
			//only fix input vars, rest will be determined from the input
			if(this.sysInfo.isInput(var)){
				conjunction.add(this.sysInfo.getInitialAssignmentPredicate(var));
			}
			//TODO: find nicer way to recognize the helper variables
			if(var.startsWith(DeductionGuardTransformation.DEDUCTION_MONITOR_PREFIX) ||
					var.startsWith(DeductionGuardTransformation.READ_GUARD_PREFIX)){
				conjunction.add(this.sysInfo.getInitialAssignmentPredicate(var));
			}
		}
		return this.generateBinaryLogicExpression(location, conjunction, BinaryExpression.Operator.LOGICAND);
	}

	/**
	 * Generate phases for one Pea resulting in a chain of if (else) statements. 
	 * Additionally in the last requirement a "assert false" is inserted into a final phase.
	 * @param location
	 * @param id
	 * @param pea
	 * @param phaseInvariants
	 * @return
	 */
	protected Statement[] generatePhase(BoogieLocation location, int id, PhaseEventAutomata pea, 
			HashMap<Phase, ArrayList<Statement>> phaseInvariants){
			Statement[] ifStatement = new Statement[]{};
			for(int i = 0; i < pea.getPhases().length; i++){
				ArrayList<Statement> invar = phaseInvariants.get(pea.getPhases()[i]);
				// if this phase is the final phase
				Statement targetReached = null;
				if(this.finalPhases.contains(pea.getPhases()[i])){
					// get what sould not happen and  assert it here
					CDD effectInvar = this.model.getPattern(pea).getEffect().negate();
					 targetReached = new IfStatement(location, 
							// if L_var for all var in effect
							this.generateCanReadVars(effectInvar), 
							// check if effect is fullfilled (and assert false if so)
							new Statement[]{this.generateAssertCDD(effectInvar, "", location)},
							new Statement[]{});
				}
				if (targetReached != null){
					invar.add(targetReached);
				}
				ifStatement = new Statement[]{this.generateIfPhaseCounterEquals(
						location, id, i, 
						invar, 
						ifStatement)};
			}
			return ifStatement;
		}
	
	protected Statement generateAssertCDD(CDD cdd, String file, BoogieLocation location){
		return new AssertStatement(location,
				new CDDTranslator().CDD_To_Boogie(cdd,file,location));
	}
	
	protected Expression generateCanReadVars(CDD cdd){
		CDD condition = CDD.TRUE;
		for(String var: cdd.getIdents()){
			CDD atom = BoogieBooleanExpressionDecision.create(
					new IdentifierExpression(noneLocation, DeductionGuardTransformation.READ_GUARD_PREFIX + var)
					);
			condition = condition.and(atom);			
		}
		return new CDDTranslator().CDD_To_Boogie(condition,"",noneLocation);
	}
	
	

	
}
