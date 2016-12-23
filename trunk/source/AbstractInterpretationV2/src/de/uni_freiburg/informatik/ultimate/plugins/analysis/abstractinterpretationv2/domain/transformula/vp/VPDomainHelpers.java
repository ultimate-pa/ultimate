package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;

public class VPDomainHelpers {
	// public static IProgramVar getIProgramVarFromTermVariable(TermVariable tv, TransFormula tf) {
	// for (Entry<IProgramVar, TermVariable> en : tf.getInVars().entrySet()) {
	// if (en.getValue() == tv) {
	// return en.getKey();
	// }
	// }
	// for (Entry<IProgramVar, TermVariable> en : tf.getOutVars().entrySet()) {
	// if (en.getValue() == tv) {
	// return en.getKey();
	// }
	// }
	// assert false : "should not happen";
	// return null;
	// }

	public static Map<TermVariable, IProgramVar> computeProgramVarMappingFromTransFormula(final TransFormula tf) {
		return computeProgramVarMappingFromInVarOutVarMappings(tf.getInVars(), tf.getOutVars());
	}

	public static Map<TermVariable, IProgramVar> computeProgramVarMappingFromInVarOutVarMappings(
			final Map<IProgramVar, TermVariable> map1, final Map<IProgramVar, TermVariable> map2) {
		final Map<TermVariable, IProgramVar> result = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> en : map1.entrySet()) {
			result.put(en.getValue(), en.getKey());
		}
		for (final Entry<IProgramVar, TermVariable> en : map2.entrySet()) {
			result.put(en.getValue(), en.getKey());
		}
		return result;
	}

	public static Map<Term, Term> computeNormalizingSubstitution(final TransFormula tf) {
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

	public static <T extends IIcfgTransition<IcfgLocation>> boolean
			containsNoNullElement(final Collection<VPState<T>> states) {
		for (final VPState<T> state : states) {
			if (state == null) {
				return false;
			}
		}
		return true;
	}

	public static <T extends IIcfgTransition<IcfgLocation>> boolean
			allStateBuildersHaveSameVariables(final Collection<VPStateBuilder<T>> resultStates) {
		final Set<VPState<T>> mapped =
				resultStates.stream().map(builder -> builder.build()).collect(Collectors.toSet());
		return allStatesHaveSameVariables(mapped);
	}

	public static <T extends IIcfgTransition<IcfgLocation>> boolean
			allStatesHaveSameVariables(final Collection<VPState<T>> resultStates) {
		if (resultStates.isEmpty()) {
			return true;
		}
		boolean result = true;
		final Set<IProgramVar> sample = resultStates.iterator().next().getVariables();
		for (final VPState<?> rs : resultStates) {
			result &= sample.equals(rs.getVariables());
		}
		return result;
	}

	public static IProgramVar getProgramVar(final TermVariable newArray, final Map<IProgramVar, TermVariable> map) {
		for (final Entry<IProgramVar, TermVariable> en : map.entrySet()) {
			if (en.getValue() == newArray) {
				return en.getKey();
			}
		}
		return null;
	}

	public static Object getProgramVar(final Term term, final TransFormula tf) {
		if (!(term instanceof TermVariable)) {
			return null;
		}
		final IProgramVar invarPv = getProgramVar((TermVariable) term, tf.getInVars());
		if (invarPv != null) {
			return invarPv;
		}
		final IProgramVar outvarPv = getProgramVar((TermVariable) term, tf.getOutVars());
		if (outvarPv != null) {
			return outvarPv;
		}
		return null;
	}
	
		/**
	 * Only keeps those entries in the given map whose value is a free variable in the given Term.
	 */
	public static Map<IProgramVar, TermVariable> projectToTerm(Map<IProgramVar, TermVariable> xVars, Term term) {
		Map<IProgramVar, TermVariable> result = new HashMap<>();
		for (Entry<IProgramVar, TermVariable> en : xVars.entrySet()) {
			if (Arrays.asList(term.getFreeVars()).contains(en.getValue())) {
				result.put(en.getKey(), en.getValue());
			}
		}
		return result;
	}
	
	public static Term getArrayTerm(ApplicationTerm at) {
		if (at.getFunction().getName().equals("select")) {
			MultiDimensionalSelect mds = new MultiDimensionalSelect(at);
			return mds.getArray();
		} else if (at.getFunction().getName().equals("store")) {
			MultiDimensionalStore mds = new MultiDimensionalStore(at);
			return mds.getArray();
		} else {
			assert false;
			return null;
		}
	}

	public static Map<IProgramVar, TermVariable> projectToVars(Map<IProgramVar, TermVariable> toBeProjected,
			Set<IProgramVar> projection) {
		Map<IProgramVar, TermVariable> result = new HashMap<>();
		for (Entry<IProgramVar, TermVariable> en : toBeProjected.entrySet()) {
//			if (en.getKey().getTerm().getSort().isArraySort()) {
//				// we keep all arrays 
//				result.put(en.getKey(), en.getValue());
//			}
			if (projection.contains(en.getKey())) {
				result.put(en.getKey(), en.getValue());
			}
		}
		return result;
	}
}
