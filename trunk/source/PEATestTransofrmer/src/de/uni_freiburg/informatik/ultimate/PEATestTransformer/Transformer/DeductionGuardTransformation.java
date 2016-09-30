package de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

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
	 * Initiate transformation.
	 */
	@Override
	public void translate() {
		ArrayList<PatternType> patterns = this.systemModel.getPattern();
		// add deduction guard to every edge of the automaton
		this.logger.info("Beginning DeductionGuard transformation.");
		for (int i = 0; i < patterns.size(); i++) {
			PhaseEventAutomata pea = this.systemModel.getPeas().get(i);
			CounterTrace counterTrace = this.systemModel.getCounterTraces().get(i);
			String clockVar = null;
			if (!pea.getClocks().isEmpty()){
				clockVar = pea.getClocks().get(0);
			}
			// get last active phase of counter trace automaton
			// int lastphase = counterTrace.getPhases().length -3;
			Set<String> effectVars = this.systemModel.getPattern(i).getEffectVariabels();
			DCPhase lastPhase = this.systemModel.getFinalPhase(counterTrace);
			this.transformPea(pea, counterTrace, lastPhase, clockVar, effectVars, i);
		}
		this.generateDeductionAutomatonInstant();	
	}
	
	private void transformPea(PhaseEventAutomata pea, CounterTrace ct, 
			DCPhase lastPhase, String clockVar, Set<String> effectVars, int reqNo){
		for (Phase source : pea.getPhases()) {
			for (Transition trans : source.getTransitions()) {
				Phase dest = trans.getDest();
				Set<String> identsToProof = this.getPhaseToPhaseToProve(ct, pea, source, dest);
				boolean destFinal = false;
				// build conjunct of all phases that are part of the PEA phase
				CDD targetPhaseConj = CDD.TRUE;
				for (DCPhase phase : this.systemModel.getDcPhases(pea, dest)) {
					if (lastPhase == phase) {
						destFinal = true;
					}
					targetPhaseConj = targetPhaseConj.and(phase.getInvariant());
				}	
				// determine which variables are seeping variables in the next state
				// Of the seeping vars only one must be deduceable to be sure that this is an ok state
				Set<String> seepVars = new HashSet<String>();
				if(!destFinal){
					Set<String> phaseVars = targetPhaseConj.getIdents();
					seepVars = dest.getStateInvariant().getIdents();
					seepVars.remove(clockVar);
					seepVars.removeAll(this.sysInfo.getInputs());
					seepVars.removeAll(lastPhase.getInvariant().getIdents());
					seepVars.removeAll(phaseVars); //vars not in the targetPhaseConjunct must be seep vars or timers
				}
				this.logger.info("State Invariant:" + dest.getStateInvariant()+ " | isfinal: " + Boolean.toString(destFinal));
				this.logger.info("SeepVars: " + seepVars.toString());
				//On a final destination it is always the whole invariant that we need to encode
				if (destFinal) {
					targetPhaseConj = dest.getStateInvariant();
				}

				CDD guard = trans.getGuard();
				// must guarantee that all variables in the guard are deduced too
				targetPhaseConj = targetPhaseConj.and(guard.unprime());
				//handling for timed automata (only necessary for upper bounds on states)
				// if timer is running supress read guards on edges
				boolean timed = this.systemModel.phaseIsUpperBoundFinal(pea, source) && 
						this.systemModel.phaseIsUpperBoundFinal(pea, dest);
				// untimed or final and timed which means that this must set an effect (and an R_v)
				CDD deductionGuard = this.transformInvariantToDeductionGuard(targetPhaseConj, destFinal, effectVars, 
						timed, identsToProof, clockVar, reqNo);
				CDD seepGuard = this.encodeNonSeepGuard(seepVars);
				guard = guard.and(deductionGuard).and(seepGuard);
				trans.setGuard(guard);
				this.logger.info("Finished Guard: " + guard.toString());
			}			
		}
	}
	
	private CDD encodeNonSeepGuard(Set<String> idents){
		CDD result = CDD.FALSE;
		for(String ident: idents){
			CDD temp = BoogieBooleanExpressionDecision.create(this.encodeInternalVar(ident));
			result = result.or(temp);
		}
		if (result == CDD.FALSE){
			return CDD.TRUE;
		}
		return result;
	}
	
	
	/***
	 * Determine all variables that have to be determined to get from phase "source" to phase "dest".
	 * @param ct
	 * @param source
	 * @param dest
	 * @return
	 */
	private Set<String> getPhaseToPhaseToProve(CounterTrace ct, PhaseEventAutomata pea, Phase source, Phase dest){
		Set<String> aux = new HashSet<String>();
		int maxSource = this.systemModel.getDCPhasesMax(ct, pea, source);
		int maxDest = this.systemModel.getDCPhasesMax(ct, pea, dest);
		// add identifiers of all variables that must be deduced on the way from source to effect phase
		for(int i = maxSource +1; i <= maxDest; i++){
			aux.addAll(ct.getPhases()[i].getInvariant().getIdents());
		}
		// selfloops
		if (maxDest == maxSource){
			aux.addAll(ct.getPhases()[maxDest].getInvariant().getIdents());
		}
		// if final phase, add seeps
		if(maxDest == this.systemModel.getFinalPhaseNumber(ct)){
			aux.addAll(ct.getPhases()[maxDest+1].getInvariant().getIdents());
		}
		// remove clocks that were added to the list 
		for(String clockIdent: pea.getClocks()){
			aux.remove(clockIdent);
		}
		return aux; 
	}
	
	
	/**
	 * Builds a guard that is true iff for all variables in the invariant passed, the models state can
	 * determine values for all variables in the invariant.
	 */
	private CDD transformInvariantToDeductionGuard(CDD invariant, boolean destinationHasLastPhase, 
			Set<String> effectVars, boolean timed, Set<String> identsToProof, String clockVar, int reqNo){
		CDD[] dnf = invariant.toDNF();
		CDD resultingConjunct = CDD.FALSE;
		CDD temp = CDD.TRUE;
		for(CDD conjunct: dnf){
			temp = CDD.TRUE;
			if(destinationHasLastPhase){
				if (this.containsEffect(conjunct, effectVars)){
					// conjunct && L_wholePhaseNecessary && !(all other conjuncts)
					CDD l = this.encodeReadConjunct(invariant, true, identsToProof, effectVars);
					if (timed) l = CDD.TRUE; //TODO: HACK
					temp = conjunct.prime(clockVar).and(l);
					for(CDD t: dnf){
						if(!this.containsEffect(t, effectVars)){
							t = t.negate().prime(clockVar);
							temp = temp.and(t);
						}
					}
				} else {
					// conjunct && !R_effect
					// may loop on not deducable but not effect triggering variables because it is an implication
					CDD r = this.encodeNotDeducedInConjunct(effectVars, reqNo);
					// encode that we still want to be able to read the lhs anytime
					CDD l = this.encodeReadConjunct(conjunct, true, identsToProof, effectVars);
					temp = r.and(l);
				}
			} else {
				// conjunct && !R_effect && L_conjunt
				CDD l = this.encodeReadConjunct(conjunct, false, identsToProof, effectVars);
				CDD r = this.encodeNotDeducedInConjunct(effectVars, reqNo);
				temp = conjunct.prime(clockVar).and(r).and(l);
			}
			// add result to new conjunct
			resultingConjunct = resultingConjunct.or(temp);
		}
		return resultingConjunct;
	}
	
	/***
	 * Generates the deduction monitor:
	 * Pea with one phase whose invariant is !L*_v || R_v_i || R_v_j || ... for an internal variable v and
	 * automata i, j,... that may determine the variables value.
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
							new ArrayList<String>(), 	//clocks
							variables, 					//variables and types thereof
							new HashSet<String>(), 	//events
							new ArrayList<String>()	//declatrations
							));
				}
	}
	
	/*
	 * L_ ... anotniation
	 */
	private CDD encodeReadConjunct(CDD conjunct, boolean finalPhase, 
			Set<String> neccesaryIdents, Set<String> effectVars){
		CDD result = CDD.TRUE;
		for(String ident: conjunct.getIdents()){
			if(finalPhase && effectVars.contains(ident)){
				// do not encode if variable is an effect AND its the last phase
				continue;
			}
			if(! neccesaryIdents.contains(ident)){
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
	private CDD encodeNotDeducedInConjunct(Set<String> effectVars, int reqNo){
		CDD result = CDD.TRUE;
		for(String ident: effectVars){
			CDD temp = BoogieBooleanExpressionDecision.create(this.encodeEffectVar(ident, reqNo)).negate();
			result = result.and(temp);
		}
		return result;
	}
	
	/**
	 * Encode if internal variable can be read
	 * e.g. "a" -> "(L'_a && a')"
	 */
	private Expression encodeInternalVar(String ident){
		if(!this.deductionMonitorVars.containsKey(ident)){
			this.deductionMonitorVars.put(ident, new HashSet<String>());
		}
		return new IdentifierExpression(BoogieAstSnippet.createDummyLocation(), this.READ_GUARD_PREFIX + ident + "'");
	}
	
	/**
	 * Encode an effect of a variable as determined
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
	private boolean containsEffect(CDD cdd, Set<String> effectVars){
		for(String ident: effectVars){
			if(cdd.getIdents().contains(ident)){
				return true;
			}
			if(cdd.getIdents().contains(ident+"'")){
				return true;
			}
		}
		return false;
	}
	
	
	
	
	
	
	
	

}
