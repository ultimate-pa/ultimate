/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * A positional DFS order the approximates lock-step order.
 *
 * The idea is to consider whether the current line numbers for threads are even or odd. If the line number for the
 * first (enabled) thread is even, then threads with odd line numbers are preferred. Between threads whose line numbers
 * are either both even or both odd, we order by procedure name. One by one all threads with odd line numbers make a
 * step, reaching even line numbers as well. Once all (enabled) threads are at an odd line number, we now begin to
 * prefer threads with odd line numbers, until all of them have made a step and reached an even line number again.
 *
 * This is only an approximation, as line numbers are not completely reliable: blank lines and non-straightline control
 * flow (e.g. if/else) can lead to two successive CFG locations that both correspond to even (or both odd) line numbers.
 *
 * To retrieve current locations, we assume that states are given as {@link IMLPredicate}.
 *
 * TODO extend to support other ways to retrieve locations
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of actions. We use {@link IAction#getPrecedingProcedure()} to refer the the action's thread
 *            instance.
 */
public class PseudoLockstepOrder<L extends IAction> implements IDfsOrder<L, IPredicate> {
	@Override
	public Comparator<L> getOrder(final IPredicate state) {
		if (!(state instanceof IMLPredicate)) {
			return Comparator.comparingInt(Object::hashCode);
		}

		// pick next thread by considering line numbers
		final IMLPredicate mlState = (IMLPredicate) state;
		final String nextThread = getNextThread(mlState);

		return (x, y) -> {
			final String xThread = x.getPrecedingProcedure();
			final String yThread = y.getPrecedingProcedure();
			if (nextThread.compareTo(xThread) <= 0 && nextThread.compareTo(yThread) > 0) {
				return -1;
			}
			if (nextThread.compareTo(yThread) <= 0 && nextThread.compareTo(xThread) > 0) {
				return 1;
			}
			final int pref = xThread.compareTo(yThread);
			if (pref != 0) {
				return pref;
			}
			return x.hashCode() - y.hashCode();
		};
	}

	private static String getNextThread(final IMLPredicate state) {
		final List<IcfgLocation> locations = Arrays.asList(state.getProgramPoints());
		locations.sort(Comparator.comparing(IcfgLocation::getProcedure));
		assert !locations.isEmpty() : "empty state cannot be handled";

		final Set<IcfgEdge> enabledActions = Arrays.stream(state.getProgramPoints())
				.flatMap(x -> x.getOutgoingEdges().stream())
				.filter(x -> IcfgUtils.isEnabled(Set.of(state.getProgramPoints()), x)).collect(Collectors.toSet());

		// Find the first location with a known line number
		int firstLocIndex;
		ILocation firstLoc = null;
		for (firstLocIndex = 0; firstLocIndex < locations.size(); ++firstLocIndex) {
			firstLoc = ILocation.getAnnotation(locations.get(firstLocIndex));
			final boolean isEnabled =
					locations.get(firstLocIndex).getOutgoingEdges().stream().anyMatch(enabledActions::contains);
			if (isEnabled && firstLoc != null) {
				break;
			}
		}
		if (firstLoc == null || firstLocIndex >= locations.size()) {
			return locations.get(0).getProcedure();
		}
		final boolean firstIsEven = firstLoc.getStartLine() % 2 == 0;

		// Find the first location whose line number is even iff the line number of firstLoc is not even.
		for (int index = firstLocIndex + 1; index < locations.size(); ++index) {
			final ILocation loc = ILocation.getAnnotation(locations.get(index));
			final boolean isEven = loc != null && loc.getStartLine() % 2 == 0;
			final boolean isEnabled =
					locations.get(index).getOutgoingEdges().stream().anyMatch(enabledActions::contains);
			if (isEnabled && isEven != firstIsEven) {
				return locations.get(index).getProcedure();
			}
		}

		return locations.get(firstLocIndex).getProcedure();
	}

	@Override
	public boolean isPositional() {
		return true;
	}
}
