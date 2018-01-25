/*
 * Copyright (C) 2016-2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE HeapSeparator plug-in.
 *
 * The ULTIMATE HeapSeparator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE HeapSeparator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE HeapSeparator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE HeapSeparator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE HeapSeparator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Does a preanalysis on the program before the actual heap separation is done
 *
 * Computes of each icfg edge the subterms of the edge's TransFormula that are subject to transformation by the heap
 * separator.
 * These are divided into:
 * <li> cell updates (array updates where the lhs and rhs array refer to the same program variable)
 * <li> array relations (equalities where the lhs and rhs have array type -stores are allowed- and which are not cell
 *  updates )
 * <li> cell accesses (essentially select terms)
 *
 * Furthermore from the result of this preanalysis we can compute the groups of arrays whose partitioning has to be
 * aligned because they are assigned to each other.
 *
 * @author Alexander Nutz
 *
 */
public class HeapSepPreAnalysis {


	// unclear if ArrayUpdate is the right choice here -- what about store chains?, also it uses MultiDimensionalStore..
	private final HashRelation<EdgeInfo, ArrayUpdate> mEdgeToCellUpdates;

	private final HashRelation<EdgeInfo, ArrayEqualityAllowStores> mEdgeToArrayRelations;

	private final HashRelation<EdgeInfo, ArrayCellAccess> mEdgeToArrayCellAccesses;

	private final ManagedScript mMgdScript;

	private Set<SelectInfo> mSelectInfos;

	private Set<ArrayGroup> mArrayGroups;

	/**
	 *
	 * @param logger
	 * @param equalityProvider
	 */
	public HeapSepPreAnalysis(final ILogger logger, final ManagedScript mgdScript) {
		mMgdScript = mgdScript;

		mEdgeToCellUpdates = new HashRelation<>();
		mEdgeToArrayCellAccesses = new HashRelation<>();
		mEdgeToArrayRelations = new HashRelation<>();
	}

	public void processEdge(final IcfgEdge edge) {
		final UnmodifiableTransFormula tf = edge.getTransformula();

		final EdgeInfo edgeInfo = new EdgeInfo(edge);

		/*
		 * subterms that have already been put into one of the maps
		 */
		final Set<Term> visitedSubTerms = new HashSet<>();

		for (final ArrayUpdate au : ArrayUpdate.extractArrayUpdates(tf.getFormula())) {
			final IProgramVarOrConst newArrayPv = edgeInfo.getProgramVarOrConstForTerm(au.getNewArray());
			final IProgramVarOrConst oldArrayPv = edgeInfo.getProgramVarOrConstForTerm(au.getOldArray());

			assert au.getNewArray() != au.getOldArray() : "that would be a strange case, no?..";
			assert !au.isNegatedEquality() : "strange case";

			// we only keep array updates that have the same ProgramVar lhs und rhs
			if (newArrayPv.equals(oldArrayPv)) {
				mEdgeToCellUpdates.addPair(edgeInfo, au);
				visitedSubTerms.add(au.getArrayUpdateTerm());
			}
		}

		for (final ArrayEqualityAllowStores aeas
				: ArrayEqualityAllowStores.extractArrayEqualityAllowStores(tf.getFormula())) {
			if (visitedSubTerms.contains(aeas.getTerm(mMgdScript.getScript()))) {
				// term is already stored as a cell update
				continue;
			}
			mEdgeToArrayRelations.addPair(edgeInfo, aeas);
//			visitedSubTerms.add(aeas.getTerm(mMgdScript.getScript()));
		}

		for (final ArrayCellAccess aca : ArrayCellAccess.extractArrayCellAccesses(tf.getFormula())) {
//			assert !visitedSubTerms.contains(aca.getTerm(mMgdScript.getScript()));
			mEdgeToArrayCellAccesses.addPair(edgeInfo, aca);
		}
	}

	// not used right now --> remove?
	@Deprecated
	Set<Term> getArraysAsTerms() {
		assert false;
		return null;
	}

	// not used right now --> remove?
	@Deprecated
	Set<IProgramVar> getArraysAsProgramVars() {
		assert false;
		return null;
	}

//	/**
//	 * Helper to get a IProgramVar from a TermVariable via the In/OutVarsMapping
//	 *
//	 * @param tv
//	 * @param map
//	 * @return
//	 */
//	private static IProgramVar getVarForTerm(final TermVariable tv, final Map<IProgramVar, TermVariable> map) {
//		for (final Entry<IProgramVar, TermVariable> en: map.entrySet()) {
//			if (en.getValue() == tv) {
//				return en.getKey();
//			}
//		}
//		throw new IllegalArgumentException();
//	}

//	private static IProgramVarOrConst getVarOrConstForTerm(final TermVariable tv, final Map<IProgramVar, TermVariable> map) {
//		final IProgramVar var = getVarForTerm(tv, map);
//		if (var != null) {
//			return var;
//		}
//
//		throw new AssertionError();
//
//	}

	public Set<SelectInfo> getSelectInfos() {
		if (mSelectInfos == null) {
			throw new IllegalStateException("call finish first");
		}
		return mSelectInfos;
	}

//	public Set<ArrayGroup> getArrayGroups() {
//		if (mArrayGroups == null) {
//			throw new IllegalStateException("call finish first");
//		}
//		return mArrayGroups;
//	}

	public Map<IProgramVarOrConst, ArrayGroup> getArrayToArrayGroup() {
		if (mArrayGroups == null) {
			throw new IllegalStateException("call finish first");
		}
		final Map<IProgramVarOrConst, ArrayGroup> result = new HashMap<>();
		for (final ArrayGroup ag : mArrayGroups) {
			for (final IProgramVarOrConst a : ag.getArrays()) {
				result.put(a, ag);
			}
		}
		return Collections.unmodifiableMap(result);
	}

	public void finish() {
		mSelectInfos = new HashSet<>();
		for (final Entry<EdgeInfo, ArrayCellAccess> en : mEdgeToArrayCellAccesses) {
			final SelectInfo selectInfo = new SelectInfo(en.getValue(), en.getKey());
			mSelectInfos.add(selectInfo);
		}

		/*
		 * Compute the array groups. Rule: Whenever two arrays are related via "=" in any formula in the program, they
		 *  must be in the same array group.
		 */
		final UnionFind<IProgramVarOrConst> arrayPartition = new UnionFind<>();
		for (final Entry<EdgeInfo, ArrayEqualityAllowStores> en : mEdgeToArrayRelations) {
			final EdgeInfo edgeInfo = en.getKey();
			final ArrayEqualityAllowStores aeas = en.getValue();


			final IProgramVarOrConst lhsPvoc = edgeInfo.getProgramVarOrConstForTerm(aeas.getLhsArray());
			final IProgramVarOrConst rhsPvoc = edgeInfo.getProgramVarOrConstForTerm(aeas.getRhsArray());

			arrayPartition.findAndConstructEquivalenceClassIfNeeded(lhsPvoc);
			arrayPartition.findAndConstructEquivalenceClassIfNeeded(rhsPvoc);
			arrayPartition.union(lhsPvoc, rhsPvoc);
		}
		mArrayGroups = new HashSet<>();
		for (final Set<IProgramVarOrConst> block : arrayPartition.getAllEquivalenceClasses()) {
			mArrayGroups.add(new ArrayGroup(block));
		}

	}


}
