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
import java.util.Deque;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.stream.Collector;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.BlockEncodingBacktranslator;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class BaseBlockEncoder<LOC extends IcfgLocation> implements IEncoder<LOC> {
	protected final IUltimateServiceProvider mServices;
	protected final ILogger mLogger;
	private final BlockEncodingBacktranslator mBacktranslator;

	protected int mRemovedEdges;
	protected int mRemovedLocations;
	private BasicIcfg<LOC> mResult;

	public BaseBlockEncoder(final ILogger logger, final IUltimateServiceProvider services,
			final BlockEncodingBacktranslator backtranslator) {
		assert services != null;
		mServices = services;
		mLogger = logger;
		mRemovedEdges = 0;
		mRemovedLocations = 0;
		mBacktranslator = backtranslator;
	}

	@Override
	public BasicIcfg<LOC> getResult(final BasicIcfg<LOC> icfg) {
		if (mResult == null) {
			mResult = createResult(icfg);
			mBacktranslator.removeIntermediateMappings();
			assert mResult != null;
		}
		return mResult;
	}

	public int getRemovedEdges() {
		return mRemovedEdges;
	}

	public int getRemovedLocations() {
		return mRemovedLocations;
	}

	protected abstract BasicIcfg<LOC> createResult(BasicIcfg<LOC> icfg);

	protected List<IcfgLocation> getSuccessors(final IcfgLocation point) {
		final List<IcfgLocation> rtr = new ArrayList<>();
		for (final IcfgEdge edge : point.getOutgoingEdges()) {
			rtr.add(edge.getTarget());
		}
		return rtr;
	}

	protected void removeDisconnectedLocations(final BasicIcfg<LOC> root) {
		// check all locations without incoming edges that are not initial or which are initial sinks
		final Set<IcfgLocation> initial =
				root.getProcedureEntryNodes().entrySet().stream().map(a -> a.getValue()).collect(Collectors.toSet());
		final Predicate<IcfgLocation> filter =
				a -> (!initial.contains(a) || a.getOutgoingEdges().isEmpty()) && a.getIncomingEdges().isEmpty();
		final Deque<IcfgLocation> locationsWithoutInEdge =
				root.getProgramPoints().entrySet().stream().flatMap(a -> a.getValue().entrySet().stream())
						.map(a -> a.getValue()).filter(filter).collect(new DequeCollector<>());

		while (!locationsWithoutInEdge.isEmpty()) {
			final IcfgLocation current = locationsWithoutInEdge.removeFirst();
			final List<IcfgEdge> outEdges = new ArrayList<>(current.getOutgoingEdges());
			for (final IcfgEdge out : outEdges) {
				final IcfgLocation target = out.getTarget();
				if (target.getIncomingEdges().size() == 1) {
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

	protected void removeDisconnectedLocation(final BasicIcfg<LOC> root, final IcfgLocation toRemove) {
		root.removeLocation(toRemove);
		mRemovedLocations++;
	}

	protected void rememberEdgeMapping(final IIcfgTransition<?> newEdge, final IIcfgTransition<?> originalEdge) {
		mBacktranslator.mapEdges((IcfgEdge) newEdge, (IcfgEdge) originalEdge);
	}

	private static class DequeCollector<T> implements Collector<T, Deque<T>, Deque<T>> {

		private static final Set<Collector.Characteristics> CHARACTERISTICS =
				EnumSet.of(Characteristics.IDENTITY_FINISH);

		@Override
		public Supplier<Deque<T>> supplier() {
			return ArrayDeque::new;
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
		public Set<Collector.Characteristics> characteristics() {
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
