package de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.BoogieAstSnippet;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SystemInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import pea.BoogieBooleanExpressionDecision;
import pea.CDD;
import pea.CounterTrace;
import pea.CounterTrace.DCPhase;
import pea.Decision;
import pea.Phase;
import pea.PhaseEventAutomata;
import pea.PhaseSet;
import pea.Trace2PEACompiler;
import pea.Transition;
import srParse.srParsePattern;
import srParse.pattern.PatternType;

public class DeductionGuardTransromation extends BasicTransformer {
	private SystemInformation sysInfo;
	private ILogger logger;
	private final static String CLOSED_WORLD_PREFIX = "R'_";
	private final static String CLOSED_WORLD_SEPR = "_";
	private final static String READ_GUARD_PREFIX = "L'_"; 
	
	public DeductionGuardTransromation(ILogger logger, SystemInformation sysInfo){
		this.sysInfo = sysInfo;
		this.logger = logger;
	}
	
	/**
	 * 
	 */
	@Override
	protected ArrayList<PhaseEventAutomata> postProcess(ArrayList<PatternType> pats, ArrayList<CounterTrace> counterTraces, 
			ArrayList<PhaseEventAutomata> peas){
		// add deduction guard to every edge of the automaton
		this.logger.info("Beginning DeductionGuard transformation.");
		for(int i = 0; i < pats.size(); i++){
			PhaseEventAutomata pea = peas.get(i);
			CounterTrace counterTrace = counterTraces.get(i);
			// get last active phase of counter trace automaton
			//int lastphase = counterTrace.getPhases().length -3;
			DCPhase lastPhase = counterTrace.getPhases()[counterTrace.getPhases().length-3];
			for(Phase loc: pea.getPhases()){
				for(Transition trans: loc.getTransitions()){
					boolean destinationHasLastPhase = false;
					//build conjunct from phase invariants (invariant - seeps)
					DCPhase[] phases = counterTrace.getPhases();
					PhaseSet activePhases = trans.getDest().getPhaseBits().getPhaseSet(phases);
					CDD targetPhaseConj = CDD.TRUE;
					//check if last phase of the allowed prefix of the counter trace is in the phase
					for(DCPhase phase: activePhases.getPhases()){
						if(lastPhase == phase){
							logger.warn("phase is final");
							destinationHasLastPhase = true;
						} else {
							logger.warn("phase is NOT final");
						}
						// also build conjunct of phases of the target state to ignore seeping
						targetPhaseConj = targetPhaseConj.and(phase.getInvariant());

					}
					// create guard for edge
					// if the edge targets a state with the last state in the phase, then take the hole invariant including 
					// seeping, else make a guard that is without seeping.
					CDD guard = trans.getGuard();
					if (destinationHasLastPhase){
						guard = guard.and(
							this.dmGuard(pats.get(i), trans.getDest().getStateInvariant(), destinationHasLastPhase, false, i));
					} else {
						guard = guard.and(
							this.dmGuard(pats.get(i), targetPhaseConj , destinationHasLastPhase, false, i));
						logger.warn(guard);
					}
					// if p' invariant does not talk about the effect, singal that effect is not set by the req
			        // ¬δ0 v,ρ | v ∈ effect(ρ) ∧ v ∈ vars(e)
					for(String id: pats.get(i).getEffectVariabels()){
						String dguard = this.CLOSED_WORLD_PREFIX+id+this.CLOSED_WORLD_SEPR+Integer.toString(i);
						//if \gamma_v_i is not part of the guard, it must be false
						if(guard.getIdents().contains(dguard)) continue;
						guard = guard.and(BoogieBooleanExpressionDecision.create(
								BoogieAstSnippet.createIdentifier(dguard)
								).negate());
					}
					trans.setGuard(guard);
				}
			}
		}
		//TODO: add deduction guard automata
		return peas;
	}
	
	/**
	 * Recursive method generates guards to incorporate deduction guards into set of peas.
	 * @param ct
	 * The counter trace of the pea
	 * @param invariant
	 * invariant of the next state, in later iterations part of the invariant that is to be encoded.
	 * @param hasLastPhase
	 * @param disjunction
	 * @return
	 */
	private CDD dmGuard(PatternType pattern, CDD invariant, boolean hasLastPhase, boolean disjunction, int reqNo){
			//end of tree, return 
			if (invariant == CDD.TRUE) {
	            return invariant;
	        }
	        if (invariant == CDD.FALSE) {
	            return invariant;
	        }

	        //generate guards from this CDD's decision
	        CDD result = BoogieBooleanExpressionDecision.create(
	        		this.dmGuard(pattern, ((BoogieBooleanExpressionDecision)invariant.getDecision()).getExpression()
	        				, hasLastPhase, disjunction, reqNo));
	        // process children
	        logger.warn(invariant.toString());
	        CDD newChild = CDD.FALSE;
	        List<CDD> conjuncts = new ArrayList<CDD>();
	        conjuncts.add(CDD.TRUE);
	        for (int i = 0; i < invariant.getChilds().length; i++) {
	        	/* newChildren = newChildren.or(dmGuard(pattern, invariant.getChilds()[i], hasLastPhase, true, reqNo));
	        	 logger.warn("---"+invariant.getChilds()[i].toString());
	        	//result = result.and(dmGuard(pattern, invariant.getChilds()[i],hasLastPhase,invariant.getChilds().length >1, reqNo)); 
	        	if (invariant.childDominates(i)) {
	                // sb.append(childs[i].toString("tex", true));
	        		if (result == null) result = CDD.FALSE;
	            	result.or(dmGuard(pattern, invariant.getChilds()[i] ,hasLastPhase, true, reqNo));
	            } else {
                    if (invariant.getChilds()[i] != CDD.TRUE) {
                    	if (result == null) result = CDD.TRUE; 
                    	result.and(dmGuard(pattern, invariant.getChilds()[i], hasLastPhase,false ,reqNo));
                    }
	            }*/
	            if (invariant.childDominates(i)) {
	            	conjuncts.add(newChild);
	            	 newChild = CDD.TRUE;
	            }
	            if (invariant.getChilds()[i] != CDD.TRUE) {
	                newChild = newChild.and(dmGuard(pattern, invariant.getChilds()[i], hasLastPhase, false, reqNo));
	            }
	                
	        }
	        conjuncts.add(newChild);
	        for(CDD conjunct: conjuncts){
	        	if(conjunct != CDD.TRUE)
	        		result = result.and(conjunct);
	        }
	        /*if (newChild != CDD.FALSE){
	        	result = result.and(newChild);
	        }*/
		return result; 
	}
	
	
	private Expression dmGuard(PatternType pattern, Expression e, boolean hasLastPhase, boolean disjunction, int reqNo){
		if(e instanceof BinaryExpression){
			BinaryExpression be = (BinaryExpression) e;
			switch(((BinaryExpression) e).getOperator()){
				case LOGICAND: 	//logic connectives should not happen here, so error
				case LOGICOR: 
					throw new RuntimeException("Logic operation implemented as Boogie (instead of CDD)!");
				default: 		//all other binary operators are ok
					new BinaryExpression(be.getLocation(), be.getOperator(), 
							this.dmGuard(pattern, be.getLeft(), hasLastPhase, disjunction, reqNo), 
							this.dmGuard(pattern, be.getRight(), hasLastPhase, disjunction, reqNo));
			}
		}
		if(e instanceof UnaryExpression){ //unary expresions can be passed along
			return new UnaryExpression(e.getLocation(), ((UnaryExpression)e).getOperator(), 
					this.dmGuard(pattern, ((UnaryExpression) e).getExpr(), hasLastPhase, disjunction, reqNo));
		}
		// add read or write monitor variables on the different expressions
		if(e instanceof IdentifierExpression){
			IdentifierExpression id = (IdentifierExpression) e; 
			String ident = id.getIdentifier();
			if(!this.sysInfo.isInput(ident)){
				if(pattern.isEffect(ident)){
					if(hasLastPhase){
						// R_v
						return new IdentifierExpression(e.getLocation(), this.CLOSED_WORLD_PREFIX+id.getIdentifier()+this.CLOSED_WORLD_SEPR+Integer.toString(reqNo));
					} else {
						// !R_v && L_v && v
						return BoogieAstSnippet.createConjunction(new Expression[]{
								new IdentifierExpression(e.getLocation(), this.CLOSED_WORLD_PREFIX+id.getIdentifier()+this.CLOSED_WORLD_SEPR+Integer.toString(reqNo)),
								new IdentifierExpression(e.getLocation(), id.getIdentifier()),
								new UnaryExpression(e.getLocation(), UnaryExpression.Operator.LOGICNEG, 
									new IdentifierExpression(e.getLocation(), this.CLOSED_WORLD_PREFIX+id.getIdentifier()+this.CLOSED_WORLD_SEPR+Integer.toString(reqNo)))
						});
					}
				} else {
					return new BinaryExpression(id.getLocation(), Operator.LOGICAND, new IdentifierExpression(e.getLocation(), this.READ_GUARD_PREFIX+id.getIdentifier()), 
							new IdentifierExpression(e.getLocation(), ident+"'" ));
				}
	
				/*if(hasLastPhase && !pattern.isEffect(ident) || !hasLastPhase){
					Expression readGuard = new IdentifierExpression(e.getLocation(), this.READ_GUARD_PREFIX+id.getIdentifier());
					if (false){ 		//L0v | v ∈ vars(e)
						return readGuard;	
					} else {				//(L0 v ∧ e) | v ∈ vars(e) 
						return new BinaryExpression(id.getLocation(), Operator.LOGICAND, readGuard, 
								new IdentifierExpression(e.getLocation(), ident+"'" ));
					}
				} else if (hasLastPhase && pattern.isEffect(ident)){
					//δ0v,ρ | v ∈ effect(ρ) ∧ v ∈ vars(e)δ0
					return new IdentifierExpression(e.getLocation(), 
							this.CLOSED_WORLD_PREFIX+id.getIdentifier()+this.CLOSED_WORLD_SEPR+Integer.toString(reqNo));	
				}*/
			}
		}
		return e;
	}
	
}
















