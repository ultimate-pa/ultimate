package de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.BoogieAstSnippet;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.PeaSystemModel;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SystemInformation;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import pea.BoogieBooleanExpressionDecision;
import pea.CDD;
import pea.CounterTrace;
import pea.CounterTrace.DCPhase;
import pea.Phase;
import pea.PhaseEventAutomata;
import pea.Transition;
import srParse.pattern.PatternType;

public class DeductionGuardTransformation implements IPeaTransformer {
	private SystemInformation sysInfo;
	private ILogger logger;
	private PeaSystemModel systemModel;
	public final static String DEDUCTION_MONITOR_PREFIX = "R_";
	public final static String CLOSED_WORLD_SEPR = "_";
	public final static String READ_GUARD_PREFIX = "L_";
	
	private HashMap<String, HashSet<String>> deductionMonitorVars = new HashMap<String, HashSet<String>>();

	public DeductionGuardTransformation(ILogger logger, PeaSystemModel systemModel) {
		this.systemModel = systemModel;
		this.sysInfo = this.systemModel.getSystemInformation();
		this.logger = logger;
	}

	/**
	 * 
	 */
	@Override
	public void translate() {
		ArrayList<PatternType> pats = this.systemModel.getPattern();
		// add deduction guard to every edge of the automaton
		this.logger.info("Beginning DeductionGuard transformation.");
		for (int i = 0; i < pats.size(); i++) {
			PhaseEventAutomata pea = this.systemModel.getPeas().get(i);
			CounterTrace counterTrace = this.systemModel.getCounterTraces().get(i);
			// get last active phase of counter trace automaton
			// int lastphase = counterTrace.getPhases().length -3;
			DCPhase lastPhase = counterTrace.getPhases()[counterTrace.getPhases().length - 3];
			for (Phase loc : pea.getPhases()) {
				for (Transition trans : loc.getTransitions()) {
					boolean destinationHasLastPhase = false;
					// build conjunct from phase invariants (invariant - seeps)
					// check if last phase of the allowed prefix of the counter
					// trace is in the phase
					CDD targetPhaseConj = CDD.TRUE;
					for (DCPhase phase : this.systemModel.getDcPhases(pea, trans.getDest())) {
						if (lastPhase == phase) {
							destinationHasLastPhase = true;
						}
						// also build conjunct of phases of the target state to
						// ignore seeping
						targetPhaseConj = targetPhaseConj.and(phase.getInvariant());
					}
					// create guard for edge
					logger.warn(trans.getDest().getStateInvariant().toString()+ " | isfinal: " + Boolean.toString(destinationHasLastPhase));
					// take the state invariant in the last phase (including
					// seeping invariants)
					if (destinationHasLastPhase) {
						targetPhaseConj = trans.getDest().getStateInvariant();
					}
					// if there is a conjunct that contains only effect variables
					// this must be an implication and has to be encoded differently
					CDD guard = trans.getGuard();
					CDD[] dnf = targetPhaseConj.toDNF();
					CDD resultingConjunct = CDD.FALSE;
					CDD temp = CDD.TRUE;
					for(CDD conjunct: dnf){
						temp = CDD.TRUE;
						if(destinationHasLastPhase){
							if (this.containsEffect(conjunct, i)){
								// conjunct && L_wholePhaseNecessary && !(all other conjuncts)
								//CDD l = this.encodeWriteInConjunct(targetPhaseConj, i, true);
								temp = conjunct.prime();//.and(l);
								for(CDD t: dnf){
									if(!this.containsEffect(t, i)){
										t = t.negate().prime();
										temp = temp.and(t);
									}
								}
							} else {
								// conjunct && !R_effect
								// may loop on not deducable but not effect triggering variables because it is an implication
								CDD r = this.encodeDeducedInConjunct(conjunct, i);
								temp = conjunct.prime().and(r);
							}
						} else {
							// conjunct && !R_effect && L_conjunt
							//CDD l = this.encodeWriteInConjunct(conjunct, i, false);
							CDD r = this.encodeDeducedInConjunct(conjunct, i);
							temp = conjunct.prime().and(r);//.and(l);
						}
						// add result to new conjunct
						resultingConjunct = resultingConjunct.or(temp);
					}
					trans.setGuard(guard.and(resultingConjunct));
				}
				
			}
		}
		this.generateDeductionAutomatonInstant();
		
	}
	
	/***
	 * one state with edge !L*_v || R_v_0 || R_v_1 || ...
	 */
	private void generateDeductionAutomatonInstant(){
		// Add deduction guard automata 
				for(String ident: this.deductionMonitorVars.keySet()){
					Phase phase = new Phase("p0", CDD.TRUE);
					HashMap<String,String> variables = new HashMap<String,String>();
					//the variable stays the same
					//CDD closedWorldContition = CDD.FALSE;
					CDD closedWorldContition = BoogieBooleanExpressionDecision.create(
								new IdentifierExpression(new BoogieLocation("",0,0,0,0,false),  READ_GUARD_PREFIX+ident+"'")
							).negate();
					//unless one automata allows it		
					for(String guardIdent: this.deductionMonitorVars.get(ident)){
						closedWorldContition = closedWorldContition.or(BoogieBooleanExpressionDecision.create(
									BoogieAstSnippet.createIdentifier(guardIdent+"'", "ClosedWorldAsumption")
								));
						variables.put(guardIdent, "bool");	
					}
					variables.put(READ_GUARD_PREFIX+ident, "bool");
					phase.addTransition(phase, closedWorldContition, new String[]{});
					this.systemModel.addPea(new PhaseEventAutomata(
							"CW_" + ident,  			//name
							new Phase[]{phase}, 		//pahses
							new Phase[]{phase}, 		//initial pahses
							new ArrayList<String>(){}, 	//clocks
							variables, 					//variables and types thereof
							new HashSet<String>(){}, 	//events
							new ArrayList<String>(){}	//declatrations
							));
				}
	}
	
	/***
	 * one state with edge (v == v')|| R_v_0 || R_v_1 || ...
	 */
	private void generateDeductionAutomatonInstantValueComp(){
		// Add deduction guard automata 
				for(String ident: this.deductionMonitorVars.keySet()){
					Phase phase = new Phase("p0", CDD.TRUE);
					HashMap<String,String> variables = new HashMap<String,String>();
					//the variable stays the same
					//CDD closedWorldContition = CDD.FALSE;
					CDD closedWorldContition = BoogieBooleanExpressionDecision.create(
								new BinaryExpression(new BoogieLocation("",0,0,0,0,false), BinaryExpression.Operator.COMPEQ,  
										new IdentifierExpression(new BoogieLocation("",0,0,0,0,false),ident+"'"),
										new IdentifierExpression(new BoogieLocation("",0,0,0,0,false),ident)
										)
							);
					//unless one automata allows it		
					for(String guardIdent: this.deductionMonitorVars.get(ident)){
						closedWorldContition = closedWorldContition.or(BoogieBooleanExpressionDecision.create(
									BoogieAstSnippet.createIdentifier(guardIdent+"'", "ClosedWorldAsumption")
								));
						variables.put(guardIdent, "bool");	
					}
					variables.put(READ_GUARD_PREFIX+ident, "bool");
					phase.addTransition(phase, closedWorldContition, new String[]{});
					this.systemModel.addPea(new PhaseEventAutomata(
							"CW_" + ident,  			//name
							new Phase[]{phase}, 		//pahses
							new Phase[]{phase}, 		//initial pahses
							new ArrayList<String>(){}, 	//clocks
							variables, 					//variables and types thereof
							new HashSet<String>(){}, 	//events
							new ArrayList<String>(){}	//declatrations
							));
				}
	}
	
	/***
	 * two states     q0{ !L*_v  } , q1{L*_v}
	 * edge q0->01{ R_v_0 || R_v_1 || ... }
	 * edge q1->00{ !(R_v_0 || R_v_1 || ...) }
	 * self loops with same guards as targets.
	 * 
	 * L_v is delayed one step by this, thus output can be consumed.
	 */
	private void generateDeductionAutomatonNextStep(){
		// Add deduction guard automata 
				for(String ident: this.deductionMonitorVars.keySet()){
					HashMap<String,String> variables = new HashMap<String,String>();
					CDD mayRead = BoogieBooleanExpressionDecision.create(
							new IdentifierExpression(BoogieAstSnippet.createDummyLocation(), this.READ_GUARD_PREFIX + ident +"'")
							);
					variables.put(READ_GUARD_PREFIX+ident, "bool");
					Phase phase0 = new Phase("p0", mayRead.negate());
					Phase phase1 = new Phase("p1", mayRead);
					//the variable stays the same
					//CDD closedWorldContition = CDD.FALSE;
					CDD closedWorldContition = CDD.FALSE;
					//unless one automata allows it		
					for(String guardIdent: this.deductionMonitorVars.get(ident)){
						closedWorldContition = closedWorldContition.or(BoogieBooleanExpressionDecision.create(
									BoogieAstSnippet.createIdentifier(guardIdent+"'", "ClosedWorldAsumption")
								));
						variables.put(guardIdent, "bool");	
					}
					// stay here if not written
					phase0.addTransition(phase0, closedWorldContition.negate(), new String[]{});
					// goto one if written
					phase1.addTransition(phase1, closedWorldContition, new String[]{});
					// go back if not written
					phase1.addTransition(phase0, closedWorldContition.negate(), new String[]{});
					// stay if written
					phase0.addTransition(phase1, closedWorldContition, new String[]{});
					
					this.systemModel.addPea(new PhaseEventAutomata(
							"CW_" + ident,  			//name
							new Phase[]{phase0, phase1}, 		//pahses
							new Phase[]{phase0}, 		//initial pahses
							new ArrayList<String>(){}, 	//clocks
							variables, 					//variables and types thereof
							new HashSet<String>(){}, 	//events
							new ArrayList<String>(){}	//declatrations
							));
				}
	}
	
	/*
	 * L_ ... anotniation
	 */
	private CDD encodeWriteInConjunct(CDD conjunct, int reqNo, boolean finalPhase){
		CDD result = CDD.TRUE;
		for(String ident: conjunct.getIdents()){
			if(finalPhase && this.systemModel.getPattern(reqNo).getEffectVariabels().contains(ident)){
				logger.warn("Effect Variabels:" + this.systemModel.getPattern(reqNo).getEffectVariabels().toString());
				// do not encode if variable is an effect AND its the last phase
				continue;
			}
			if(this.sysInfo.isInput(ident)){
				continue;
			}
			CDD temp = BoogieBooleanExpressionDecision.create(this.encodeInternalVar(ident));
			result = result.and(temp);
		}
		return result;
	}
	
	/* 
	 * R_... anotation
	 */
	private CDD encodeDeducedInConjunct(CDD conjunct, int reqNo){
		CDD result = CDD.TRUE;
		for(String ident: this.systemModel.getPattern(reqNo).getEffectVariabels()){
			CDD temp = BoogieBooleanExpressionDecision.create(this.encodeEffectVar(ident,reqNo)).negate();
			result = result.and(temp);
		}
		return result;
	}
	
	/**
	 * Encode internal identifiert o be checkt if readable 
	 * e.g. "a" -> "(L'_a && a')"
	 */
	private Expression encodeInternalVar(String ident){
		if(!this.deductionMonitorVars.containsKey(ident)){
			this.deductionMonitorVars.put(ident, new HashSet<String>());
		}
		return new IdentifierExpression(BoogieAstSnippet.createDummyLocation(), this.READ_GUARD_PREFIX + ident + "'");
	}
	
	/**
	 * Encode an effect of a variable as true
	 * e.g. "a" -> "R'_a_reqNo"
	 */
	private Expression encodeEffectVar(String ident, int reqNo){	
		return new IdentifierExpression(BoogieAstSnippet.createDummyLocation(), this.getClosedWorldPrefix(ident, reqNo));
	}
	
	protected String getClosedWorldPrefix(String ident, int reqNo){
		String guardVar = this.DEDUCTION_MONITOR_PREFIX + ident + this.CLOSED_WORLD_SEPR + Integer.toString(reqNo);
		// book keeping for later generation of deduction monitors
		if(!this.deductionMonitorVars.containsKey(ident)){
			this.deductionMonitorVars.put(ident, new HashSet<String>());
		}
		this.deductionMonitorVars.get(ident).add(guardVar);
		return guardVar+"'";
	}
	
	/**
	 * Determines if one of the effect variabels is in the cdd.
	 * @param cdd
	 * @param reqNo
	 * @return
	 * 	true if effect variable in cdd, else false
	 */
	private boolean containsEffect(CDD cdd, int reqNo){
		for(String ident: this.systemModel.getPattern(reqNo).getEffectVariabels()){
			if(cdd.getIdents().contains(ident)){
				return true;
			}
		}
		return false;
	}

	protected Expression primeVars(Expression e){
			if(e instanceof BinaryExpression){
				BinaryExpression bchild = ((BinaryExpression)e);
				return new BinaryExpression(e.getLocation(),
						bchild.getOperator(),
						this.primeVars(bchild.getLeft()), this.primeVars(bchild.getRight()));
			}else if(e instanceof UnaryExpression){
				UnaryExpression bchild = ((UnaryExpression)e);
				return new UnaryExpression(e.getLocation(),
						bchild.getOperator(),
						this.primeVars(bchild.getExpr()));
			} else if(e instanceof IdentifierExpression){
				return new IdentifierExpression(e.getLocation(),
						((IdentifierExpression)e).getIdentifier()+"'");
			} else {
				return e;
			}
	}
	
	
	
	
	
	
	
	

}
