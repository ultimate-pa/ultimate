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
public class ClosedWorldTransformator extends PatternToPea {
	
	private SystemInformation sysInfo;
	
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
	 * Append the automata for the closed world assumption on all variabels that are not in the input set
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
							BoogieAstSnippet.createIdentifier("R_"+i+"_"+ident, "ClosedWorldAsumption")
						));
				variables.put("R_"+i+"_"+ident, "bool");
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
	 * TODO: nicht per edge sondern per automaton ein neues edge erstellen
	 * @param trans
	 * @note guarantee that newIdentIndex is called once per ident and Pea before this Method is called.
	 */
	private void createClosedWorldGuard(Transition transition, Set<String> idents){
		//count for later use when building automata for every var
		for(String ident: idents){
			//build actual new guard
			if(!this.sysInfo.isInput(ident)){
				CDD guard = transition.getGuard();
				if (guard == CDD.TRUE){
					transition.setGuard(BoogieBooleanExpressionDecision.create(
								BoogieAstSnippet.createIdentifier("R_"+this.closedWorldCounter.get(ident)+"_"+ ident, "ClosedWorldAsumption")).negate());
				} else {
					transition.setGuard(
							guard.and(BoogieBooleanExpressionDecision.create(
								BoogieAstSnippet.createIdentifier("R_"+this.closedWorldCounter.get(ident)+"_"+ident, "ClosedWorldAsumption")
							).negate()));	
				}
			}
		}
	}
	/**
	 * Must be called for an ident before createClosedWorld edge is called with the ident. This increases the R_x counter
	 * per ident and must be called per automaton. Inside the automaton one id can be used the whole time.
	 */
	private void newIdentIndex(Set<String> idents){
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
		Set<String> cddIdents = new HashSet<String>();
		this.collectIdentifiersFromCdd(s, cddIdents); //yes, s is correct!
		//add !R_varname to original (true) edge for every var in s. (may only change when not s)
		//TODO: ONLY if they are no input variables (compare with SystemInfo) not with I_ prefix
		Transition transition = pea.getPhases()[0].getTransitions().get(0);
		this.newIdentIndex(cddIdents);
		this.createClosedWorldGuard(transition, cddIdents);
		transition.setGuard(transition.getGuard().and(p));
		//add one edge that can be taken when !s
		pea.getPhases()[0].addTransition(
				pea.getPhases()[0], //selfloop
				p.negate(),
				new String[]{});
		return pea;
	}

	@Override
	protected PhaseEventAutomata AfterUniversality(PatternType pattern, CDD p, CDD q, CDD r, CDD s) {
		PhaseEventAutomata pea =  super.AfterUniversality(pattern, p, q, r, s);
		//collect all variables in the effect
		Set<String> cddIdents = new HashSet<String>();
		this.collectIdentifiersFromCdd(s, cddIdents);
		//select self loop of phase 0 to add closed world guard (altering other edges is not necessary)
		Transition transition = pea.getPhases()[0].getTransitions().get(0);
		this.newIdentIndex(cddIdents);
		this.createClosedWorldGuard(transition, cddIdents);
		return pea;
	}

	
	

}











