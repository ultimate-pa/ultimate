package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;


import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public class VPDomainHelpers {
//	public static IProgramVar getIProgramVarFromTermVariable(TermVariable tv, TransFormula tf) {
//		for (Entry<IProgramVar, TermVariable> en : tf.getInVars().entrySet()) {
//			if (en.getValue() == tv) {
//				return en.getKey();
//			}
//		}
//		for (Entry<IProgramVar, TermVariable> en : tf.getOutVars().entrySet()) {
//			if (en.getValue() == tv) {
//				return en.getKey();
//			}
//		}
//		assert false : "should not happen";
//		return null;
//	}
	
	public static Map<TermVariable, IProgramVar> computeProgramVarMappingFromTransFormula(TransFormula tf) {
		return computeProgramVarMappingFromInVarOutVarMappings(tf.getInVars(), tf.getOutVars());
	}

	public static Map<TermVariable, IProgramVar> computeProgramVarMappingFromInVarOutVarMappings(
			Map<IProgramVar, TermVariable> map1, Map<IProgramVar, TermVariable> map2) {
		Map<TermVariable, IProgramVar> result = new HashMap<>();
		for (Entry<IProgramVar, TermVariable> en : map1.entrySet()) {
			result.put(en.getValue(), en.getKey());
		}
		for (Entry<IProgramVar, TermVariable> en : map2.entrySet()) {
			result.put(en.getValue(), en.getKey());
		}
		return result;
	}

	public static Map<Term, Term> computeNormalizingSubstitution(TransFormula tf) {
		return computeNormalizingSubstitution(computeProgramVarMappingFromTransFormula(tf));
	}

	/**
	 * compute a substitution mapping that translates the TermVariables in a Term to the corresponding default
	 * TermVariable of a IProgramVar. (TODO: not so happy with everything that is connected to this..)
	 *
	 * @param c
	 * @return
	 */
	public static Map<Term, Term> computeNormalizingSubstitution(final Map<TermVariable, IProgramVar> tvToPvMap) {
		final Map<Term, Term> substitionMap = new HashMap<>();
		for (final Entry<TermVariable, IProgramVar> en : tvToPvMap.entrySet()) {
			substitionMap.put(en.getKey(), en.getValue().getTerm());
		}
		return substitionMap;
	}

	public static boolean containsNoNullElement(Collection<VPState> states) {
		for (VPState state : states) {
			if (state == null) {
				return false;
			}
		}
		return true;
	}
	public static boolean allStateBuildersHaveSameVariables(Collection<VPStateBuilder> resultStates) {
		Set<VPState> mapped = 
				resultStates.stream()
				.map(builder -> builder.build())
				.collect(Collectors.toSet());
		return allStatesHaveSameVariables(mapped);
	}

	public static boolean allStatesHaveSameVariables(Collection<VPState> resultStates) {
		if (resultStates.isEmpty()) {
			return true;
		}
		boolean result = true;
		Set<IProgramVar> sample = resultStates.iterator().next().getVariables();
		for (VPState rs : resultStates) {
			result &= sample.equals(rs.getVariables());
		}
		return result;
	}

	public static IProgramVar getProgramVar(TermVariable newArray, Map<IProgramVar, TermVariable> map) {
		for (Entry<IProgramVar, TermVariable> en : map.entrySet()) {
			if (en.getValue() == newArray) {
				return en.getKey();
			}
		}
		return null;
	}

	public static Object getProgramVar(Term term, TransFormula tf) {
		if (!(term instanceof TermVariable)) {
			return null;
		}
		IProgramVar invarPv = getProgramVar((TermVariable) term, tf.getInVars());
		if (invarPv != null) {
			return invarPv;
		}
		IProgramVar outvarPv = getProgramVar((TermVariable) term, tf.getOutVars());
		if (outvarPv != null) {
			return outvarPv;
		}
		return null;
	}
}
