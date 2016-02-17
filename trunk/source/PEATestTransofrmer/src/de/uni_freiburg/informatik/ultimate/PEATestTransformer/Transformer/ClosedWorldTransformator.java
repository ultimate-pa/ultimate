package de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.BoogieAstSnippet;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SystemInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import pea.BoogieBooleanExpressionDecision;
import pea.CDD;
import pea.Phase;
import pea.PhaseEventAutomata;
import pea.Transition;
import srParse.pattern.PatternType;

/**
 * This class extends the PatternToPea by an added set of automata that guarantee that
 * internal variables of the PEA set can only be altered if a pea requests thata that 
 * variables is altered. 
 * 
 * @author Langenfeld
 *
 */
public class ClosedWorldTransformator extends BasicTransformer {
	
	private SystemInformation sysInfo;
	private final static String CLOSED_WORLD_PREFIX = "R_";
	private final static String CLOSED_WORLD_SEPR = "_";
	
	public ClosedWorldTransformator(SystemInformation sysInfo){
		this.sysInfo = sysInfo;
	}
	
	private HashMap<String, Integer> closedWorldCounter = new HashMap<String, Integer>();
	
	/**
	 * Collects the variables off CDDs with BoogieBooleanExpressionDecision and adds it to a set.
	 * @param cdd off which and of whos children variables shall be collected
	 * @param idents set the vars are added to
	 */
	private void collectIdentifiersFromCdd(CDD cdd, Set<String> idents){
		if(!(cdd.getDecision() instanceof BoogieBooleanExpressionDecision)){ 
			throw new UnsupportedOperationException("This Transformer only transforms Boogie Expressions");
		} else {
			for(String id: (((BoogieBooleanExpressionDecision)cdd.getDecision()).getVars().keySet()))
					idents.add(id);
		}
		for(CDD child: cdd.getChilds()){
			if(child != cdd.FALSE && child != cdd.TRUE){
				collectIdentifiersFromCdd(child,idents);
			}
		}
	}

	/**
	 * Append the automata for the closed world assumption on all variables that are not in the input set
	 */
	@Override
	protected ArrayList<PhaseEventAutomata> postProcess(ArrayList<PatternType> patterns, ArrayList<PhaseEventAutomata> peas) {
		//generate closed world automat
		for(String ident: this.closedWorldCounter.keySet()){
			Phase phase = new Phase("p0", CDD.TRUE);
			HashMap<String,String> variables = new HashMap<String,String>();
			//the variable stays the same
			CDD closedWorldContition = BoogieBooleanExpressionDecision.create(
						BoogieAstSnippet.createBooleanExpression(ident, ident+"'", BinaryExpression.Operator.COMPEQ)
					);
			//unless one automata allows it		
			for(int i = 1; i <= this.closedWorldCounter.get(ident); i++){
				closedWorldContition = closedWorldContition.or(BoogieBooleanExpressionDecision.create(
							BoogieAstSnippet.createIdentifier(CLOSED_WORLD_PREFIX+i+CLOSED_WORLD_SEPR+ident, "ClosedWorldAsumption")
						));
				variables.put(CLOSED_WORLD_PREFIX+i+CLOSED_WORLD_SEPR+ident, "bool");
			}
			phase.addTransition(phase, closedWorldContition, new String[]{});
			peas.add(new PhaseEventAutomata(
					"CW_" + ident,  			//name
					new Phase[]{phase}, 		//pahses
					new Phase[]{phase}, 		//initial pahses
					new ArrayList<String>(){}, 	//clocks
					variables, 					//variables and types thereof
					new HashSet<String>(){}, 	//events
					new ArrayList<String>(){}	//declatrations
					));
		}
		return super.postProcess(patterns, peas);
	}
	
	/**
	 * Appends a conjunction to the guard of the passed transition, that appends an closed world
	 * guard R_<varname> for the variable.
	 * @param trans
	 * @note guarantee that newIdentIndex is called once per pea for all its identifiers that are later
	 * used on a closed world edge.
	 */
	protected CDD createClosedWorldGuard(CDD consequence){
		Set<String> idents = new HashSet<String>();
		this.collectIdentifiersFromCdd(consequence, idents);
		return this.createClosedWorldGuard(idents);
	}
	protected CDD createClosedWorldGuard(Set<String> idents){
		//count for later use when building automata for every var
		CDD guard = CDD.TRUE;
		for(String ident: idents){
			//build actual new guard
			if(!this.sysInfo.isInput(ident)){
				guard = guard.and(BoogieBooleanExpressionDecision.create(
						BoogieAstSnippet.createIdentifier(
								CLOSED_WORLD_PREFIX+this.closedWorldCounter.get(ident)+CLOSED_WORLD_SEPR+ ident, "ClosedWorldAsumption"
								)).negate());
			}
		}
		return guard;
	}
	
	/**
	 * Helper for giving a unique x per automaton for a variable y for R_x_y edges.
	 * Must be called once per automaton in the beginning of the automaton creation.
	 */
	protected void newIdentIndex(CDD cdd){
		Set<String> idents = new HashSet<String>();
		this.collectIdentifiersFromCdd(cdd, idents);
		this.newIdentIndex(idents);
	}
	protected void newIdentIndex(Set<String> idents){
		for(String ident: idents){
			if(!this.sysInfo.isInput(ident)){
				if(!this.closedWorldCounter.containsKey(ident)){
					this.closedWorldCounter.put(ident, 1);
				} else {
					this.closedWorldCounter.put(ident, this.closedWorldCounter.get(ident)+1);
				}
			}
		}
	}

	@Override
	protected PhaseEventAutomata GlobalInvariantPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s) {
		PhaseEventAutomata pea = super.GlobalInvariantPattern(pattern, p, q, r, s);
		//collect all variables in the effect
		this.newIdentIndex(s);
		//add to self loop: P' or (!P' and !R_S)
		Transition transition = pea.getPhases()[0].getTransitions().get(0);
		transition.setGuard(transition.getGuard().and(
				p.prime()));		// P && R_s or
		Phase phase = pea.getPhases()[0]; 
		phase.addTransition(phase, 
				p.prime().negate().and(this.createClosedWorldGuard(s)),
				new String[]{});
		return pea;
	}

	@Override
	protected PhaseEventAutomata AfterInvariantPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s) {
		PhaseEventAutomata pea =  super.AfterInvariantPattern(pattern, p, q, r, s);
		this.newIdentIndex(s);
		Phase phase = pea.getPhases()[0]; //st0
		for(Transition transition: phase.getTransitions()){
			transition.setGuard(transition.getGuard().and(this.createClosedWorldGuard(s)));
		}
		phase = pea.getPhases()[1];  //st012
		for(Transition transition: phase.getTransitions()){
			transition.setGuard(transition.getGuard().and(
					p.prime().and(this.createClosedWorldGuard(s).negate())			// P && R_s or
					.or(p.prime().negate().and(this.createClosedWorldGuard(s)))));  // !P && !R_s
		}
		phase = pea.getPhases()[2];  //st02
		for(Transition transition: phase.getTransitions()){
			transition.setGuard(transition.getGuard().and(
					p.prime().and(this.createClosedWorldGuard(s).negate())			// P && R_s or
					.or(p.prime().negate().and(this.createClosedWorldGuard(s)))));  // !P && !R_s
		}
		return pea;
	}
	
	

	
	

}











