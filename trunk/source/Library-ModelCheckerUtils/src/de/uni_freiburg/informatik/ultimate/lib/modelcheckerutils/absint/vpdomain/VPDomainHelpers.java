/*
 * Copyright (C) 2016 Yu-Wen Chen
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class VPDomainHelpers {

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

//	public static Map<Term, Term> computeNormalizingSubstitution(final Map<IProgramVar, TermVariable> map1,
//			final Map<IProgramVar, TermVariable> map2) {
//		return computeNormalizingSubstitution(computeProgramVarMappingFromInVarOutVarMappings(map1, map2));
//	}
//
//	public static Map<Term, Term> computeNormalizingSubstitution(final TransFormula tf) {
//		return computeNormalizingSubstitution(computeProgramVarMappingFromTransFormula(tf));
//	}

//	/**
//	 * compute a substitution mapping that translates the TermVariables in a Term to the corresponding default
//	 * TermVariable of a IProgramVar. (TODO: not so happy with everything that is connected to this..)
//	 *
//	 * @param c
//	 * @return
//	 */
//	public static Map<Term, Term> computeNormalizingSubstitution(final Map<TermVariable, IProgramVar> tvToPvMap) {
//		final Map<Term, Term> substitionMap = new HashMap<>();
//		for (final Entry<TermVariable, IProgramVar> en : tvToPvMap.entrySet()) {
//			substitionMap.put(en.getKey(), en.getValue().getTerm());
//		}
//		return substitionMap;
//	}

	public static IProgramVar getProgramVar(final TermVariable newArray, final Map<IProgramVar, TermVariable> map) {
		for (final Entry<IProgramVar, TermVariable> en : map.entrySet()) {
			if (en.getValue() == newArray) {
				return en.getKey();
			}
		}
		return null;
	}

	/**
	 * Only keeps those entries in the given map whose value is a free variable in the given Term.
	 */
	public static Map<IProgramVar, TermVariable> projectToTerm(final Map<IProgramVar, TermVariable> xVars,
			final Term term) {
		final Map<IProgramVar, TermVariable> result = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> en : xVars.entrySet()) {
			if (Arrays.asList(term.getFreeVars()).contains(en.getValue())) {
				result.put(en.getKey(), en.getValue());
			}
		}
		return result;
	}

	public static Term getArrayTerm(final Term t) {
		if (!(t instanceof ApplicationTerm)) {
			return t;
		}
		final ApplicationTerm at = (ApplicationTerm) t;

		if (at.getFunction().getName().equals("select")) {
			final MultiDimensionalSelect mds = new MultiDimensionalSelect(at);
			if (mds.getArray() instanceof ApplicationTerm
					&& (((ApplicationTerm) mds.getArray()).getFunction().getName().equals("select")
							|| ((ApplicationTerm) mds.getArray()).getFunction().getName().equals("store"))) {
				return getArrayTerm(mds.getArray());
			}
			return mds.getArray();
		} else if (at.getFunction().getName().equals("store")) {
			final MultiDimensionalStore mds = MultiDimensionalStore.convert(at);
			if (mds.getArray() instanceof ApplicationTerm
					&& (((ApplicationTerm) mds.getArray()).getFunction().getName().equals("select")
							|| ((ApplicationTerm) mds.getArray()).getFunction().getName().equals("store"))) {
				return getArrayTerm(mds.getArray());
			}
			return mds.getArray();
		} else {
			assert false;
			return null;
		}
	}

	public static Map<IProgramVar, TermVariable> projectToVars(final Map<IProgramVar, TermVariable> toBeProjected,
			final Set<IProgramVar> projection) {
		final Map<IProgramVar, TermVariable> result = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> en : toBeProjected.entrySet()) {
			if (projection.contains(en.getKey())) {
				result.put(en.getKey(), en.getValue());
			}
		}
		return result;
	}

	public static InOutStatusOfStateId getInOutStatusOfPvoc(final IProgramVarOrConst function, final TransFormula tf) {
		InOutStatusOfStateId functionInOutStatus;
		if (function instanceof IProgramVarOrConst) {
			functionInOutStatus = VPDomainHelpers.computeInOutStatus((IProgramVar) function, tf);
		} else {
			// constants are like a THROUGH-variable for our purposes here
			functionInOutStatus = InOutStatusOfStateId.THROUGH;
		}
		return functionInOutStatus;
	}

	/**
	 * For a given IProgramVar pv and a TransFormula tf, computes whether pv is only an InVar, only an outVar, an update
	 * or a through (e.g. used in an assume) or does not occur in tf.
	 *
	 * @param pvoc
	 * @param tf
	 */
	public static InOutStatusOfStateId computeInOutStatus(final IProgramVar pv, final TransFormula tf) {
		final boolean isIn = tf.getInVars().containsKey(pv);
		final boolean isOut = tf.getOutVars().containsKey(pv);

		if (isIn && isOut) {
			if (tf.getInVars().get(pv) == tf.getOutVars().get(pv)) {
				return InOutStatusOfStateId.THROUGH;
			} else {
				return InOutStatusOfStateId.UPDATE;
			}
		} else if (isIn && !isOut) {
			return InOutStatusOfStateId.IN;
		} else if (!isIn && isOut) {
			return InOutStatusOfStateId.OUT;
		} else {
			assert !isIn && !isOut;
			return InOutStatusOfStateId.NONE;
		}
	}

	/**
	 * in out status of a node identifier in a "normal" state (not transition state)
	 *
	 * @author alex
	 *
	 */
	public enum InOutStatusOfStateId {
		IN, OUT, THROUGH, UPDATE, NONE;
	}

	/**
	 * Returns a map that is same as the given map except that, if present, the given IProgramVar's entry has been
	 * removed.
	 *
	 * @param inVars
	 * @param function
	 * @return
	 */
	public static Map<IProgramVar, TermVariable> projectOut(final Map<IProgramVar, TermVariable> inVars,
			final IProgramVarOrConst function) {
		final Map<IProgramVar, TermVariable> result = new HashMap<>(inVars);
		if (function instanceof IProgramVar) {
			result.remove(function);
		}
		return Collections.unmodifiableMap(result);
	}

	/**
	 * cross product computation
	 *
	 * @param
	 * @return the cross product, null if there was a timeout
	 */
	public static <T> Set<List<T>> computeCrossProduct(final List<Set<T>> nodesWithSideConditions,
			final IUltimateServiceProvider services) {

		Set<List<T>> result = new HashSet<>();
		result.add(new ArrayList<>());
		for (final Set<T> nwscs : nodesWithSideConditions) {
			final Set<List<T>> newResult = new HashSet<>();

			// check timeout
			if (!services.getProgressMonitorService().continueProcessing()) {
				return null;
			}

			for (final List<T> index : result) {
				for (final T nwsc : nwscs) {
					final List<T> newIndex = new ArrayList<>(index);
					newIndex.add(nwsc);

					newResult.add(newIndex);
				}
			}

			result = newResult;
		}
		return result;
	}

	public static Map<IProgramVar, TermVariable> projectToTermAndVars(final Map<IProgramVar, TermVariable> varMapping,
			final Term projectionTerm, final Set<IProgramVar> projectionVars) {
		return projectToTerm(projectToVars(varMapping, projectionVars), projectionTerm);
	}

	public static <T> Set<T> intersect(final Set<T> s1, final Set<T> s2) {
		final Set<T> result = new HashSet<>(s1);
		result.retainAll(s2);
		return Collections.unmodifiableSet(result);
	}

	public static <K, V> boolean imageIsNeverNull(final Map<K, V> map) {
		for (final Entry<K, V> en : map.entrySet()) {

			if (en.getValue() == null) {
				return false;
			}
		}
		return true;
	}

	public static <NODE extends IEqNodeIdentifier<NODE>> boolean
			constraintFreeOfVars(final Collection<Term> varsToProjectAway,
					final EqConstraint<NODE> unfrozen,
					final Script script) {
		if (varsToProjectAway.isEmpty()) {
			return true;
		}

		final Set<Term> mixArrayThirdArgs = new HashSet<>();

		for (final NODE node : unfrozen.getAllNodes()) {
			if (node.isMixFunction()) {
				// a mix function has a third argument but does not depend on it!
				if (varsToProjectAway.contains(node.getMixFunction1())) {
					assert false;
					return false;
				}
				if (varsToProjectAway.contains(node.getMixFunction2())) {
					assert false;
					return false;
				}
				mixArrayThirdArgs.add(((ApplicationTerm) node.getTerm()).getParameters()[2]);
			} else {
				final Set<Term> intersection = DataStructureUtils.intersection(
						new HashSet<Term>(Arrays.asList(node.getTerm().getFreeVars())),
						new HashSet<Term>(varsToProjectAway));
				if (!intersection.isEmpty()) {
					assert false;
					return false;
				}

			}
		}

//		if (varsToProjectAway.stream().map(tv ->
//			unfrozen.getAllNodes().stream()
//				.anyMatch(node ->
//					VPDomainHelpers.arrayContains(node.getTerm().getFreeVars(), tv)))
//				.reduce((a, b) -> a || b)
//			.get()) {
//			assert false;
//			return false;
//		}
		if (script != null && Arrays.asList(unfrozen.getTerm(script)
				.getFreeVars()).stream()
				.anyMatch(fv -> varsToProjectAway.contains(fv)
						&& !mixArrayThirdArgs.contains(fv))) {
			assert false;
			return false;
		}
		return true;
	}

//	public static Term normalizeTerm(final Term term, final TransFormula tf, final ManagedScript mgdScript) {
//		final Map<Term, Term> subs = computeNormalizingSubstitution(tf);
//		return new Substitution(mgdScript, subs).transform(term);
//	}

//	public static Term normalizeTerm(final Term t, final Map<IProgramVar, TermVariable> newInVars,
//			final Map<IProgramVar, TermVariable> newOutVars, final ManagedScript mgdScript) {
//		final Map<Term, Term> subs = computeNormalizingSubstitution(newInVars, newOutVars);
//		return new Substitution(mgdScript, subs).transform(t);
//	}

//	public static ArrayIndex normalizeArrayIndex(final ArrayIndex index, final TransFormula tf,
//			final ManagedScript script) {
//		return new ArrayIndex(index.stream()
//				.map(t -> normalizeTerm(t, tf, script))
//				.collect(Collectors.toList()));
//	}


//	public static ArrayIndex normalizeArrayIndex(final ArrayIndex index, final Map<IProgramVar, TermVariable> newInVars,
//			final Map<IProgramVar, TermVariable> newOutVars, final ManagedScript script) {
//		return new ArrayIndex(index.stream()
//				.map(t -> normalizeTerm(t, newInVars, newOutVars, script))
//				.collect(Collectors.toList()));
//	}

	public static <T> boolean arrayContains(final T[] array, final T elem) {
		for (final T t : array) {
			if (t.equals(elem)) {
				return true;
			}
		}
		return false;
	}

	public static <NODE extends IEqNodeIdentifier<NODE>> boolean haveSameType(final NODE func1, final NODE func2) {
		if (func1.getTerm().getSort() != func2.getTerm().getSort()) {
			assert false;
			return false;
		}
		return true;
	}

	public static <K, V> void transformRelationInPlace(final HashRelation<K, V> relation, final Function<K, K> kTransformer,
			final Function<V, V> vTransformer) {
		for (final Entry<K, V> pair : new HashRelation<>(relation)) {
			relation.removePair(pair.getKey(), pair.getValue());
			relation.addPair(kTransformer.apply(pair.getKey()), vTransformer.apply(pair.getValue()));
		}
	}
}
