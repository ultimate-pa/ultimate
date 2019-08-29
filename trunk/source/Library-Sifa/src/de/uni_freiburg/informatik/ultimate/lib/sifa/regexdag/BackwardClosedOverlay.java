/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Overlay whose {@link #predecessorsOf()} always returns all predecessors.
 * Overlaid graphs always have exactly one source but can have multiple sinks.
 *
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @param <L> Type of letters that are used inside regex literals inside RegexDagNodes
 */
public class BackwardClosedOverlay<L> implements IDagOverlay<L> {

	private final HashRelation<RegexDagNode<L>, RegexDagNode<L>> mPredecessorRelation = new HashRelation<>();
	private final HashRelation<RegexDagNode<L>, RegexDagNode<L>> mSuccessorRelation = new HashRelation<>();
	private final Set<RegexDagNode<L>> mSinks = new HashSet<>();

	/**
	 * Adds all backward edges to this overlay starting from the predecessors of the given node.
	 * As a result, all paths from the DAG's source to the predecessors of the given node will be part of this overlay.
	 * Paths to the given node itself will <i>not</i> be added.
	 * @param targetNodeExclusive Node whose predecessors will be added
	 */
	public void addExclusive(final RegexDagNode<L> targetNodeExclusive) {
		targetNodeExclusive.getIncomingNodes().forEach(this::addInclusive);
	}

	/**
	 * Adds all backward edges to this overlay starting from the given node.
	 * As a result, all paths from the DAG's source to the given node will be part of this overlay.
	 * @param targetNodeInclusive Node to be added
	 */
	public void addInclusive(final RegexDagNode<L> targetNodeInclusive) {
		if (mSuccessorRelation.hasEmptyImage(targetNodeInclusive)) {
			mSinks.add(targetNodeInclusive);
		}
		addInclusiveIntern(targetNodeInclusive);
	}

	private void addInclusiveIntern(final RegexDagNode<L> targetNodeInclusive) {
		for (final RegexDagNode<L> predecessor : targetNodeInclusive.getIncomingNodes()) {
			if (mSuccessorRelation.addPair(predecessor, targetNodeInclusive)) {
				mPredecessorRelation.addPair(targetNodeInclusive, predecessor);
				mSinks.remove(predecessor);
				addInclusive(predecessor);
			}
		}
	}

	@Override
	public Collection<RegexDagNode<L>> successorsOf(final RegexDagNode<L> node) {
		return mSuccessorRelation.getImage(node);
	}

	@Override
	public Collection<RegexDagNode<L>> predecessorsOf(final RegexDagNode<L> node) {
		return mPredecessorRelation.getImage(node);
	}

	@Override
	public Collection<RegexDagNode<L>> sources(final RegexDag<L> dag) {
		return Collections.singleton(dag.getSource());
	}

	@Override
	public Collection<RegexDagNode<L>> sinks(final RegexDag<L> dag) {
		return mSinks;
	}

}
