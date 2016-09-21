package de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

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
			DCPhase lastPhase = this.systemModel.getFinalPhase(counterTrace);
			for (Phase source : pea.getPhases()) {
				for (Transition trans : source.getTransitions()) {
					Phase dest = trans.getDest();
					ArrayList<String> identsToProof = this.getPhaseToPhaseToProve(counterTrace, pea, source, dest);
					boolean destFinal = false;
					// build conjunct from phase invariants (invariant - seeps)
					// check if last phase of the allowed prefix of the counter
					// trace is in the phase
					CDD targetPhaseConj = CDD.TRUE;
					for (DCPhase phase : this.systemModel.getDcPhases(pea, dest)) {
						if (lastPhase == phase) {
							destFinal = true;
						}
						// also build conjunct of phases of the target state to
						// ignore seeping
						targetPhaseConj = targetPhaseConj.and(phase.getInvariant());
					}
					// create guard for edge
					logger.warn(dest.getStateInvariant().toString()+ " | isfinal: " + Boolean.toString(destFinal));
					// take the state invariant in the last phase (including
					// seeping invariants)
					if (destFinal) {
						targetPhaseConj = dest.getStateInvariant();
					}
					CDD guard = trans.getGuard();
					targetPhaseConj = targetPhaseConj.and(guard.unprime());
					//handling for timed automata (only necessary for upper bounds on states)
					/// destFinal && bound is > or >= && sourceFinal && dest.timeinv != true && sourceinv != false
					/*if(this.systemModel.phaseIsUpperBoundFinal(pea, source) && 
							this.systemModel.phaseIsUpperBoundFinal(pea, dest)){
						// as timer is ticking all input has no effect
						guard = guard.and(this.encodeNotDeducedInConjunct(i));
					} else if (this.systemModel.phaseIsUpperBoundFinal(pea, source)){
						// on leaving the timer the effect must be marked to be deduced
						// wich is to do noting!
					} else if(this.systemModel.phaseIsUpperBoundFinal(pea, dest)){
						// when jumping into a timer phase the precondition must be deduced
						guard = guard.and(this.encodeReadConjunct(guard, i, true, identsToProof));
						guard = guard.and(this.encodeNotDeducedInConjunct(i));
					} else {*/
						// if timer is running supress read guards on edges
						boolean timed = this.systemModel.phaseIsUpperBoundFinal(pea, source) && 
								this.systemModel.phaseIsUpperBoundFinal(pea, dest);
						// untimed or final and timed which means that this must set an effect (and an R_v)
						CDD deductionGuard = this.transformInvariantToDeductionGuard(targetPhaseConj, destFinal, i, timed, identsToProof );
						guard = guard.and(deductionGuard);
					//}
					trans.setGuard(guard);
				}			
			}
		}
		this.generateDeductionAutomatonInstant();	
	}
	
	/***
	 * Determine the values of variables that have to be proven to progress from PEA automaton
	 * phase source to pea automaton phase dest, without having to prove unnecessary facts.
	 * @param ct
	 * @param source
	 * @param dest
	 * @return
	 */
	private ArrayList<String> getPhaseToPhaseToProve(CounterTrace ct, PhaseEventAutomata pea, Phase source, Phase dest){
		ArrayList<String> result = new ArrayList<String>();
		int maxSource = this.systemModel.getDCPhasesMax(ct, pea, source);
		int maxDest = this.systemModel.getDCPhasesMax(ct, pea, dest);
		// add identifiers of all variables that must be deduced on the way from source to dest
		for(int i = maxSource +1; i <= maxDest; i++){
			result.addAll(ct.getPhases()[i].getInvariant().getIdents());
		}
		// selfloops
		if (maxDest == maxSource){
			result.addAll(ct.getPhases()[maxDest].getInvariant().getIdents());
		}
		// if final phase, add seeps
		if(maxDest == this.systemModel.getFinalPhaseNumber(ct)){
			result.addAll(ct.getPhases()[maxDest+1].getInvariant().getIdents());
		}
		return result; 
	}
	
	
	/**
	 * Transforms an invariant of a target state into the annotation deciding if the state can be entered
	 * because the model can currently deduce the values of all necessary variables.
	 */
	private CDD transformInvariantToDeductionGuard(CDD invariant, boolean destinationHasLastPhase, 
			int reqNo, boolean timed, List<String> identsToProof){
		CDD[] dnf = invariant.toDNF();
		CDD resultingConjunct = CDD.FALSE;
		CDD temp = CDD.TRUE;
		for(CDD conjunct: dnf){
			temp = CDD.TRUE;
			if(destinationHasLastPhase){
				if (this.containsEffect(conjunct, reqNo)){
					// conjunct && L_wholePhaseNecessary && !(all other conjuncts)
					CDD l = this.encodeReadConjunct(invariant, reqNo, true, identsToProof);
					if (timed) l = CDD.TRUE; //TODO: HACK
					temp = conjunct.prime().and(l);
					for(CDD t: dnf){
						if(!this.containsEffect(t, reqNo)){
							t = t.negate().prime();
							temp = temp.and(t);
						}
					}
				} else {
					// conjunct && !R_effect
					// may loop on not deducable but not effect triggering variables because it is an implication
					CDD r = this.encodeNotDeducedInConjunct(reqNo);
					temp = r;
				}
			} else {
				// conjunct && !R_effect && L_conjunt
				CDD l = this.encodeReadConjunct(conjunct, reqNo, false, identsToProof);
				CDD r = this.encodeNotDeducedInConjunct(reqNo);
				temp = conjunct.prime().and(r).and(l);
			}
			// add result to new conjunct
			resultingConjunct = resultingConjunct.or(temp);
		}
		return resultingConjunct;
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
					// and can prove that it is not blocking 
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
					// v = v'
					CDD mayReadSame = mayRead.and(BoogieBooleanExpressionDecision.create(
							new BinaryExpression(
									new BoogieLocation("",0,0,0,0,false), BinaryExpression.Operator.COMPEQ,  
									new IdentifierExpression(new BoogieLocation("",0,0,0,0,false),ident+"'"),
									new IdentifierExpression(new BoogieLocation("",0,0,0,0,false),ident)
									)
						));
					
					variables.put(READ_GUARD_PREFIX+ident, "bool");
					Phase phase0 = new Phase("p0", mayRead.negate());
					Phase phase1 = new Phase("p1", mayReadSame);
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
							new Phase[]{phase0, phase1},//pahses
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
	private CDD encodeReadConjunct(CDD conjunct, int reqNo, boolean finalPhase, List<String> neccesaryIdents){
		CDD result = CDD.TRUE;
		for(String ident: conjunct.getIdents()){
			if(finalPhase && this.systemModel.getPattern(reqNo).getEffectVariabels().contains(ident)){
				logger.warn("Effect Variabels:" + this.systemModel.getPattern(reqNo).getEffectVariabels().toString());
				// do not encode if variable is an effect AND its the last phase
				continue;
			}
			if(! neccesaryIdents.contains(ident)){
				logger.warn("Variable no necessary to deduce:"+ident );
				// do not encode if variable if its not listed in necessary idents
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
	private CDD encodeNotDeducedInConjunct(int reqNo){
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
	 * Determines if one of the effect variabels or its primed version is in the cdd.
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
			if(cdd.getIdents().contains(ident+"'")){
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
