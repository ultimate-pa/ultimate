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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayCellAccess;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayEqualityAllowStores;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayGroup;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.EdgeInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.SelectInfo;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Does a preanalysis on the program before the actual heap separation is done
 *
 * Computes of each icfg edge the subterms of the edge's TransFormula that are subject to transformation by the heap
 * separator.
 * These are divided into:
 * <ul>
 * <li> cell updates (array updates where the lhs and rhs array refer to the same program variable, "array writes")
 * <li> array relations (equalities where the lhs and rhs have array type -stores are allowed- and which are not cell
 *  updates )
 * <li> cell accesses (essentially select terms, "array reads")
 * </ul>
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

	private final ManagedScript mMgdScript;

	private final Set<SelectInfo> mSelectInfos;

	private Set<ArrayGroup> mArrayGroups;

	private final List<IProgramVarOrConst> mHeapArrays;

	private final Map <IProgramVarOrConst, ArrayGroup> mArrayToArrayGroup;

	private final ILogger mLogger;

	private final HeapSeparatorBenchmark mStatistics;

	/**
	 *
	 * @param logger
	 * @param heapArrays
	 * @param statistics
	 * @param arrayToArrayGroup
	 * @param equalityProvider
	 */
	public HeapSepPreAnalysis(final ILogger logger, final ManagedScript mgdScript,
			final List<IProgramVarOrConst> heapArrays, final HeapSeparatorBenchmark statistics,
			final Map<IProgramVarOrConst, ArrayGroup> arrayToArrayGroup) {
		mMgdScript = mgdScript;
		mLogger = logger;
		mStatistics = statistics;
		mHeapArrays = heapArrays;
		mEdgeToCellUpdates = new HashRelation<>();
		mEdgeToArrayRelations = new HashRelation<>();
		mSelectInfos = new HashSet<>();
		mArrayToArrayGroup = arrayToArrayGroup;
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

			/*
			 * only track updates to one of the heap arrays
			 */
			if (!mHeapArrays.contains(newArrayPv)) {
				continue;
			}

			/* we only keep array updates that have the same ProgramVar lhs und rhs
			 * (the others are processed as ArrayEqualityAllowStores')
			 */
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

			final IProgramVarOrConst lhsPvoc = edgeInfo.getProgramVarOrConstForTerm(aeas.getLhsArray());
			final IProgramVarOrConst rhsPvoc = edgeInfo.getProgramVarOrConstForTerm(aeas.getRhsArray());
			// filter out aeas that do not relate to a heap array
			if (!mHeapArrays.contains(lhsPvoc) && !mHeapArrays.contains(rhsPvoc)) {
				continue;
			}

			mEdgeToArrayRelations.addPair(edgeInfo, aeas);
		}

		for (final ArrayCellAccess aca : ArrayCellAccess.extractArrayCellAccesses(tf.getFormula())) {

			final SelectInfo selectInfo = new SelectInfo(aca, edgeInfo, mMgdScript);
			if (mHeapArrays.contains(selectInfo.getArrayPvoc())) {
				mSelectInfos.add(selectInfo);
			}
		}
	}

	public Set<SelectInfo> getSelectInfos() {
		if (mSelectInfos == null) {
			throw new IllegalStateException("call finish first");
		}
		return mSelectInfos;
	}

	public Map<IProgramVarOrConst, ArrayGroup> getArrayToArrayGroup() {

		return Collections.unmodifiableMap(mArrayToArrayGroup);
	}

	public void finish() {
		/*
		 * compute array read statistics
		 */
		final Map<ArrayGroup, Integer> heapArrayGroupToReadCount = new HashMap<>();
		for (final SelectInfo selectInfo : mSelectInfos) {

			final ArrayGroup ag = mArrayToArrayGroup.get(selectInfo.getArrayPvoc());

			Integer oldCount = heapArrayGroupToReadCount.get(ag);
			if (oldCount == null) {
				oldCount = 0;
				heapArrayGroupToReadCount.put(ag, oldCount);
			}
			heapArrayGroupToReadCount.put(ag, oldCount + 1);
		}
		for (final Entry<ArrayGroup, Integer> en : heapArrayGroupToReadCount.entrySet()) {
			mLogger.info("Number of read from array group " + en.getKey() + " : " + en.getValue());
			mStatistics.registerPerArrayInfo(en.getKey(), HeapSeparatorStatistics.COUNT_ARRAY_READS, en.getValue());
		}

	}


}
