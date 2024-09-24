/*
 * Copyright (C) 2024 Marcel Ebbinghaus
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Loop criterion only for testing!
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            The type of letters.
 */
public class LoopCriterion<L extends IIcfgTransition<?>> implements IConditionalCommutativityCriterion<L> {

	private final Set<? extends IcfgLocation> mLoopheads;
	private final Set<IcfgEdge> mLoopEdges;
	private ArrayDeque<IcfgEdge> mLetterStack;

	public LoopCriterion(final IIcfg<? extends IcfgLocation> icfg) {
		mLoopheads = icfg.getLoopLocations();
		mLoopEdges = new HashSet<>();

		for (final IcfgLocation loophead : mLoopheads) {
			mLetterStack = new ArrayDeque<>();
			for (final IcfgEdge edge : loophead.getOutgoingEdges()) {
				mLetterStack.add(edge);
				DFS(edge.getTarget(), loophead);
				mLetterStack.removeLast();
			}
		}
	}

	// TODO What does this method do exactly?
	// TODO It should likely not be here
	private void DFS(final IcfgLocation loc, final IcfgLocation loophead) {
		if (loc.equals(loophead)) {
			mLoopEdges.addAll(mLetterStack);
			return;
		}
		for (final IcfgEdge edge : loc.getOutgoingEdges()) {
			if (mLetterStack.contains(edge)) {
				return;
			}
			mLetterStack.add(edge);
			DFS(edge.getTarget(), loophead);
			mLetterStack.removeLast();
		}
	}

	@Override
	public boolean decide(final IPredicate state, final L letter1, final L letter2) {
		return mLoopEdges.contains(letter1) && mLoopEdges.contains(letter2);
	}

	@Override
	public boolean decide(final IPredicate condition) {
		// no filtering based on condition
		return true;
	}
}
