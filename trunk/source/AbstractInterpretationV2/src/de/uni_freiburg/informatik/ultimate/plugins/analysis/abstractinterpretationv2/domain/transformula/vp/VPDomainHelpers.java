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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

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
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqGraphNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.IVPStateOrTfState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.IVPStateOrTfStateBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPStateBuilder;

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
		final Set<IProgramVarOrConst> sample = resultStates.iterator().next().getVariables();
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
			final MultiDimensionalStore mds = new MultiDimensionalStore(at);
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

	public static <NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> boolean
			disEqualitySetContainsOnlyRepresentatives(final Set<VPDomainSymmetricPair<NODEID>> disEqualitySet,
					final IVPStateOrTfState<NODEID, ARRAYID> state) {
		for (final VPDomainSymmetricPair<NODEID> pair : disEqualitySet) {
			final EqGraphNode<NODEID, ARRAYID> firstEgn = state.getEqGraphNode(pair.getFirst());
			if (firstEgn.getRepresentative() != firstEgn) {
				return false;
			}
			final EqGraphNode<NODEID, ARRAYID> secondEgn = state.getEqGraphNode(pair.getSecond());
			if (secondEgn.getRepresentative() != secondEgn) {
				return false;
			}
		}
		return true;
	}
	
	public static <T extends IVPStateOrTfState<NODEID, ARRAYID>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID>
			boolean disEqualitySetContainsOnlyRepresentatives(final Set<VPDomainSymmetricPair<NODEID>> disEqualitySet,
					final IVPStateOrTfStateBuilder<T, NODEID, ARRAYID> builder) {
		for (final VPDomainSymmetricPair<NODEID> pair : disEqualitySet) {
			final EqGraphNode<NODEID, ARRAYID> firstEgn = builder.getEqGraphNode(pair.getFirst());
			if (firstEgn.getRepresentative() != firstEgn) {
				return false;
			}
			final EqGraphNode<NODEID, ARRAYID> secondEgn = builder.getEqGraphNode(pair.getSecond());
			if (secondEgn.getRepresentative() != secondEgn) {
				return false;
			}
		}
		return true;
	}

	public static <T extends IVPStateOrTfState<NODEID, ARRAYID>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID>
			boolean disEqualityRelationIrreflexive(final Set<VPDomainSymmetricPair<NODEID>> disEqualitySet,
					final IVPStateOrTfStateBuilder<T, NODEID, ARRAYID> builder) {
		for (final VPDomainSymmetricPair<NODEID> pair : disEqualitySet) {
			// both "==" and "equals" just to make sure..
			if (pair.getFirst() == pair.getSecond()) {
				return false;
			}
			if (pair.getFirst().equals(pair.getSecond())) {
				return false;
			}
		}
		return true;
	}
	
	/**
	 * cross product computation
	 *
	 * @param
	 * @return
	 */
	public static <T> Set<List<T>> computeCrossProduct(final List<Set<T>> nodesWithSideConditions) {
		
		Set<List<T>> result = new HashSet<>();
		result.add(new ArrayList<>());
		for (final Set<T> nwscs : nodesWithSideConditions) {
			final Set<List<T>> newResult = new HashSet<>();
			
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
	
	public static <ACTION extends IIcfgTransition<IcfgLocation>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID>
			boolean isHavocced(final ARRAYID array, final IVPStateOrTfState<NODEID, ARRAYID> resultState) {
		// TODO: fix the other isHavocced before using this
		for (final EqGraphNode<NODEID, ARRAYID> node : resultState.getAllEqGraphNodes()) {
			if (!node.mNodeIdentifier.getAllFunctions().contains(array)) {
				continue;
			}
			if (!isHavocced(node.mNodeIdentifier, resultState)) {
				return false;
			}
			
		}
		return true;
	}

	public static <ACTION extends IIcfgTransition<IcfgLocation>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID>
			boolean isHavocced(final NODEID nodeId, final IVPStateOrTfState<NODEID, ARRAYID> resultState) {
		final EqGraphNode<NODEID, ARRAYID> node = resultState.getEqGraphNode(nodeId);
		/*
		 * the node that has been havocced --> must be its own representative --> its set of reverseRepresentatives must
		 * be empty --> may not appear in a disequality ... -except- if there is a reason for propagation somewhere else
		 * in the graph(!) --> TODO: either account for this or don't use this method
		 */
		if (node.getRepresentative() != node) {
			return false;
		}
		if (!node.getReverseRepresentative().isEmpty()) {
			return false;
		}
		if (!resultState.getDisequalities(node.mNodeIdentifier).isEmpty()) {
			return false;
		}
		return true;
	}
}
