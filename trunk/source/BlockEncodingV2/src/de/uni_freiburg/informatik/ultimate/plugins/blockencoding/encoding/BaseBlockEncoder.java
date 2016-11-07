/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BlockEncodingV2 plug-in.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncodingV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncodingV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncodingV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.List;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collector;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class BaseBlockEncoder implements IEncoder {
	protected final IUltimateServiceProvider mServices;
	protected final ILogger mLogger;

	protected int mRemovedEdges;
	protected int mRemovedLocations;
	private BoogieIcfgContainer mResult;

	public BaseBlockEncoder(final BoogieIcfgContainer icfg, final IUltimateServiceProvider services) {
		assert services != null;
		assert icfg != null;
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mRemovedEdges = 0;
		mRemovedLocations = 0;
	}

	@Override
	public abstract boolean isGraphChanged();

	@Override
	public BoogieIcfgContainer getResult(final BoogieIcfgContainer icfg) {
		if (mResult == null) {
			mResult = createResult(icfg);
			assert mResult != null;
		}
		return mResult;
	}

	protected abstract BoogieIcfgContainer createResult(BoogieIcfgContainer icfg);

	protected List<IcfgLocation> getSuccessors(final IcfgLocation point) {
		final List<IcfgLocation> rtr = new ArrayList<>();
		for (final IcfgEdge edge : point.getOutgoingEdges()) {
			rtr.add(edge.getTarget());
		}
		return rtr;
	}

	protected void removeDisconnectedLocations(final BoogieIcfgContainer root) {
		final Set<BoogieIcfgLocation> initial =
				root.getEntryNodes().entrySet().stream().map(a -> a.getValue()).collect(Collectors.toSet());

		// get all locations without incoming edges that are not initial
		final Deque<BoogieIcfgLocation> locationsWithoutInEdge = root.getProgramPoints().entrySet().stream()
				.flatMap(a -> a.getValue().entrySet().stream()).map(a -> a.getValue())
				.filter(a -> !initial.contains(a) && a.getIncomingEdges().isEmpty()).collect(new DequeCollector<>());

		while (!locationsWithoutInEdge.isEmpty()) {
			final BoogieIcfgLocation current = locationsWithoutInEdge.removeFirst();
			final List<IcfgEdge> outEdges = new ArrayList<>(current.getOutgoingEdges());
			for (final IcfgEdge out : outEdges) {
				final BoogieIcfgLocation target = (BoogieIcfgLocation) out.getTarget();
				if (target.getIncomingEdges().size() == 1 && !initial.contains(target)) {
					// we will remove the only inEdge of target
					locationsWithoutInEdge.addLast(target);
				}
				out.disconnectSource();
				out.disconnectTarget();
				mRemovedEdges++;
			}
			removeDisconnectedLocation(root, current);
		}
	}

	protected void removeDisconnectedLocation(final BoogieIcfgContainer root, final IcfgLocation toRemove) {
		final String procName = toRemove.getProcedure();
		final String debugIdentifier = toRemove.getDebugIdentifier();

		final IcfgLocation removedPP = root.getProgramPoints().get(procName).remove(debugIdentifier);

		final BoogieIcfgLocation procExit = root.getExitNodes().get(procName);
		if (toRemove.equals(procExit)) {
			root.getExitNodes().remove(procName);
		}

		final BoogieIcfgLocation procEntry = root.getEntryNodes().get(procName);
		if (toRemove.equals(procEntry)) {
			root.getEntryNodes().remove(procName);
		}

		root.getLoopLocations().remove(toRemove);
		root.getPotentialCycleProgramPoints().remove(toRemove);
		final Collection<BoogieIcfgLocation> errorsInProc = root.getErrorNodes().get(procName);
		if (errorsInProc != null) {
			errorsInProc.remove(toRemove);
		}

		assert toRemove.equals(removedPP);
		mRemovedLocations++;
	}

	private static class DequeCollector<T> implements Collector<T, Deque<T>, Deque<T>> {

		private static final Set<java.util.stream.Collector.Characteristics> CHARACTERISTICS =
				Collections.singleton(Characteristics.IDENTITY_FINISH);

		@Override
		public Supplier<Deque<T>> supplier() {
			return () -> new ArrayDeque<>();
		}

		@Override
		public BiConsumer<Deque<T>, T> accumulator() {
			return (a, b) -> a.addFirst(b);
		}

		@Override
		public BinaryOperator<Deque<T>> combiner() {
			return this::combiner;
		}

		@Override
		public Function<Deque<T>, Deque<T>> finisher() {
			return a -> a;
		}

		@Override
		public Set<java.util.stream.Collector.Characteristics> characteristics() {
			return CHARACTERISTICS;
		}

		private Deque<T> combiner(final Deque<T> a, final Deque<T> b) {
			final Deque<T> rtr = new ArrayDeque<>(a.size() + b.size() + 1);
			rtr.addAll(a);
			rtr.addAll(b);
			return rtr;
		}
	}
}
