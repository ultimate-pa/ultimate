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
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.BlockEncodingBacktranslator;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class InterproceduralSequenzer extends BaseBlockEncoder<IcfgLocation> {

	private final IcfgEdgeBuilder mEdgeBuilder;

	public InterproceduralSequenzer(final IcfgEdgeBuilder edgeBuilder, final IUltimateServiceProvider services,
			final BlockEncodingBacktranslator backtranslator, final ILogger logger) {
		super(logger, services, backtranslator);
		mEdgeBuilder = edgeBuilder;
	}

	@Override
	protected BasicIcfg<IcfgLocation> createResult(final BasicIcfg<IcfgLocation> icfg) {
		final Deque<IcfgEdge> edges = new ArrayDeque<>();
		final Set<IcfgEdge> closed = new HashSet<>();

		edges.addAll(icfg.getInitialOutgoingEdges());

		// find sequences of the form l --call--> l' --e--> l'' --return--> l''' and merge them to one sequential
		// composition

		while (!edges.isEmpty()) {
			final IcfgEdge current = edges.removeFirst();
			if (!closed.add(current)) {
				continue;
			}
			IcfgLocation target;
			if (current instanceof IIcfgCallTransition<?>) {
				target = createInterproceduralSequenceIfPossible((IIcfgCallTransition<?>) current);
			} else {
				target = current.getTarget();
			}

			if (target == null) {
				// can happen if we see an edge that was disconnected during createInterproceduralSequenceIfPossible but
				// was already in the queue
				continue;
			}

			edges.addAll(target.getOutgoingEdges());
		}
		if (isGraphStructureChanged()) {
			removeDisconnectedLocations(icfg);
			mLogger.info("Removed " + mRemovedEdges + " edges and " + mRemovedLocations
					+ " locations during generation of interprocedural sequences");
		}
		return icfg;
	}

	private IcfgLocation createInterproceduralSequenceIfPossible(final IIcfgCallTransition<?> callTransition) {
		final IcfgLocation oldTarget = callTransition.getTarget();
		final List<IcfgEdge> outCall = oldTarget.getOutgoingEdges();
		if (outCall.size() > 1) {
			// cannot merge
			return oldTarget;
		}
		final IcfgEdge intermediateCb =
				outCall.stream().findAny().orElseThrow(() -> new AssertionError("Call with no out-edge"));
		final IcfgLocation intermediateTarget = intermediateCb.getTarget();
		final List<IcfgEdge> outIntermediate = intermediateTarget.getOutgoingEdges();
		if (outIntermediate.size() > 1) {
			// cannot merge
			// TODO: be able to merge
			return oldTarget;
		}

		final Optional<IIcfgReturnTransition<?, ?>> optionalReturn = findReturn(callTransition, outIntermediate);
		if (!optionalReturn.isPresent()) {
			// cannot merge
			return oldTarget;
		}
		// now we have to remove the summary for this call
		// TODO: We treated summaries different but in the IIcfg setting we cannot differentiate them
		// final List<Summary> summaries = callTransition.getSource().getOutgoingEdges().stream().filter(a -> a
		// instanceof Summary)
		// .map(a -> (Summary) a).filter(a -> a.calledProcedureHasImplementation()
		// && a.getCallStatement().equals(callTransition.getCallStatement()))
		// .collect(Collectors.toList());
		// summaries.forEach(this::disconnect);

		final IcfgEdge ss =
				createInterproceduralSequentialComposition(callTransition, intermediateCb, optionalReturn.get());

		rememberEdgeMapping(ss, callTransition);
		rememberEdgeMapping(ss, intermediateCb);
		rememberEdgeMapping(ss, optionalReturn.get());

		return ss.getTarget();
	}

	private static Optional<IIcfgReturnTransition<?, ?>> findReturn(final IIcfgCallTransition<?> callTransition,
			final List<IcfgEdge> outIntermediate) {
		for (final IcfgEdge intermediate : outIntermediate) {
			if (intermediate instanceof IIcfgReturnTransition<?, ?>) {
				final IIcfgReturnTransition<?, ?> retTrans = (IIcfgReturnTransition<?, ?>) intermediate;
				if (retTrans.getCorrespondingCall().equals(callTransition)) {
					return Optional.of(retTrans);
				}
			}
		}
		return Optional.empty();
	}

	private IcfgEdge createInterproceduralSequentialComposition(final IIcfgCallTransition<?> callTrans,
			final IIcfgTransition<?> intermediateTrans, final IIcfgReturnTransition<?, ?> returnTrans) {
		final List<IcfgEdge> transitions = new ArrayList<>(3);
		transitions.add((IcfgEdge) callTrans);
		transitions.add((IcfgEdge) intermediateTrans);
		transitions.add((IcfgEdge) returnTrans);
		final IcfgEdge ss = mEdgeBuilder.constructInterproceduralSequentialComposition(callTrans.getSource(),
				returnTrans.getTarget(), callTrans, intermediateTrans, returnTrans);
		transitions.stream().forEach(this::disconnect);
		assert ss.getTarget() != null;
		return ss;
	}

	private void disconnect(final IcfgEdge cb) {
		cb.disconnectSource();
		cb.disconnectTarget();
		mRemovedEdges++;
	}

	@Override
	public boolean isGraphStructureChanged() {
		return mRemovedEdges > 0;
	}
}
