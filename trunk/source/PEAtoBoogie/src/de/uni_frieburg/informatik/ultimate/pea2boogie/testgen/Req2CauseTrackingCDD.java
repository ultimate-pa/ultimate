package de.uni_frieburg.informatik.ultimate.pea2boogie.testgen;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.BoogieBooleanExpressionDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;

public class Req2CauseTrackingCDD {
	
	private final ILogger mLogger;
	private final Map<String,String> mTrackingVars;
	 
	public Req2CauseTrackingCDD(final ILogger logger) {
		mLogger = logger;
		mTrackingVars = new HashMap<>();
	}
	
	public CDD transform(CDD cdd, Set<String> effectVars, Set<String> inputVars,  boolean isEffectPhase) {
		Set<String> vars = getCddVariables(cdd);
		vars.removeAll(inputVars);
		//if (isEffectPhase) {
			vars.removeAll(effectVars);
		//}
		return addTrackingGuards(cdd, vars);
	}
	
	private CDD addTrackingGuards(CDD cdd, Set<String> trackVars) {
		if (cdd == CDD.TRUE) return cdd;
		if (cdd == CDD.FALSE) return cdd;
		
		List<CDD> newChildren = new ArrayList<>();
		if (cdd.getChilds() != null) {
			for (final CDD child : cdd.getChilds()) {
				newChildren.add(addTrackingGuards(child, trackVars));
			}
		}
		
		cdd = CDD.create(cdd.getDecision(), newChildren.toArray(new CDD[newChildren.size()]));
		for(String v: getVarsFromDecision(cdd.getDecision())) {
			if(trackVars.contains(v)) {
				String varName = "u_" + v;
				mTrackingVars.put(varName, "bool");
				CDD trackGurad = CDD.create(new BooleanDecision(varName), CDD.TRUE_CHILDS);
				cdd = trackGurad.and(cdd);
			}
		}
		return cdd;
	}
	
	public Set<String> getEffectVariables(PatternType pattern){
		Set<String> variables = new HashSet<>();
		List<CDD> cdds = pattern.getCdds();
		if (cdds.size() > 0) {
			//lets just assume that the effect of your requirement is always mentioned at the end
			//  e.g. it is always the case that if _condition_ then _effect_ holds for at least 5 (scope does not matter)
			//TODO: do not rely on this ordering and mark the effect in some way during parsing
			CDD effect = cdds.get(0);
			extractVars(effect, variables);
		}
		mLogger.info(new StringBuilder("Effect Variables of ").append(pattern.toString()).append(": ").append(variables.toString()).toString());
		return variables;
	}
	
	public Set<String> getCddVariables(CDD cdd){
		Set<String> variables = new HashSet<>();
		extractVars(cdd, variables);
		return variables;
	}
	
	private void extractVars(CDD cdd, Set<String> variables){
		if (cdd == CDD.TRUE) return;
		if (cdd == CDD.FALSE) return;

		variables.addAll(getVarsFromDecision(cdd.getDecision()));
		
		if (cdd.getChilds() != null) {
			for (final CDD child : cdd.getChilds()) {
				extractVars(child, variables);
			}
		}
	} 
	
	private Set<String> getVarsFromDecision(Decision<?> dec){
		Set<String> variables = new HashSet<>();
		if (dec == null) {
			// may happen for true/false phases
		} else if (dec instanceof EventDecision) {
			// requirements ignore events so far
		} else if (dec instanceof BooleanDecision) {
			variables.add(((BooleanDecision) dec).getVar());
		} else if (dec instanceof BoogieBooleanExpressionDecision) {
			final BoogieBooleanExpressionDecision bbedec = (BoogieBooleanExpressionDecision) dec;
			for (final Entry<String, String> entry : bbedec.getVars().entrySet()) {
				variables.add(entry.getKey());
			}
		} else {
			throw new UnsupportedOperationException("Unknown decision type: " + dec.getClass());
		}
		return variables;
	}
	
	public Map<String,String> getTrackingVars(){
		return mTrackingVars;
	}

}
