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
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class InterproceduralSequenzer extends BaseBlockEncoder {

	private final RcfgEdgeBuilder mEdgeBuilder;

	public InterproceduralSequenzer(final BoogieIcfgContainer product, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		super(product, services);
		mEdgeBuilder = new RcfgEdgeBuilder(product, services, simplificationTechnique, xnfConversionTechnique);
	}

	@Override
	protected BoogieIcfgContainer createResult(final BoogieIcfgContainer icfg) {
		final Deque<IcfgEdge> edges = new ArrayDeque<>();
		final Set<IcfgEdge> closed = new HashSet<>();

		icfg.getProcedureEntryNodes().values().stream().forEach(a -> edges.addAll(a.getOutgoingEdges()));

		// find sequences of the form l --call--> l' --e--> l'' --return--> l''' and merge them to one sequential
		// composition

		while (!edges.isEmpty()) {
			final IcfgEdge current = edges.removeFirst();
			if (!closed.add(current)) {
				continue;
			}
			IcfgLocation target;
			if (current instanceof Call) {
				target = createInterproceduralSequenceIfPossible((Call) current);
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

	private IcfgLocation createInterproceduralSequenceIfPossible(final Call callCb) {
		final IcfgLocation oldTarget = callCb.getTarget();
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

		final Optional<Return> optionalReturn = outIntermediate.stream().filter(a -> a instanceof Return)
				.map(a -> (Return) a).filter(a -> a.getCorrespondingCall().equals(callCb)).findAny();
		if (!optionalReturn.isPresent()) {
			// cannot merge
			return oldTarget;
		}
		// now we have to remove the summary for this call
		final List<Summary> summaries = callCb.getSource().getOutgoingEdges().stream().filter(a -> a instanceof Summary)
				.map(a -> (Summary) a).filter(a -> a.calledProcedureHasImplementation()
						&& a.getCallStatement().equals(callCb.getCallStatement()))
				.collect(Collectors.toList());
		summaries.forEach(this::disconnect);

		final SequentialComposition ss =
				createInterproceduralSequentialComposition(callCb, intermediateCb, optionalReturn);

		return ss.getTarget();
	}

	private SequentialComposition createInterproceduralSequentialComposition(final Call callCb,
			final IcfgEdge intermediateCb, final Optional<Return> optionalReturn) {
		final Return returnCb = optionalReturn.get();
		final List<CodeBlock> codeblocks = new ArrayList<>(3);
		codeblocks.add(callCb);
		codeblocks.add((CodeBlock) intermediateCb);
		codeblocks.add(returnCb);
		final SequentialComposition ss = mEdgeBuilder.constructSequentialComposition(
				(BoogieIcfgLocation) callCb.getSource(), (BoogieIcfgLocation) returnCb.getTarget(), codeblocks);
		codeblocks.stream().forEach(this::disconnect);
		assert ss.getTarget() != null;
		return ss;
	}

	private void disconnect(final CodeBlock cb) {
		cb.disconnectSource();
		cb.disconnectTarget();
		mRemovedEdges++;
	}

	@Override
	public boolean isGraphStructureChanged() {
		return mRemovedEdges > 0;
	}
}
