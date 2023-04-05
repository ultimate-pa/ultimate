/*
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022-2023 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgPetrifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.PetriInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.PetriLbeInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe.IcfgCompositionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.Activator;

/**
 * Performs Lipton reduction on a concurrent program, and returns a new ICFG for the reduced program.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class IcfgLiptonReducer {
	private final IIcfg<IcfgLocation> mPetrifiedIcfg;
	private final BasicIcfg<IcfgLocation> mNewIcfg;

	private final List<IcfgLocation> mInitialLocs;
	private final List<IcfgLocation> mErrorLocs;

	public IcfgLiptonReducer(final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg,
			final int numberOfInstances) {
		mPetrifiedIcfg = new IcfgPetrifier(services, icfg, numberOfInstances, false).getPetrifiedIcfg();
		final BoundedPetriNet<IcfgEdge, IPredicate> petriNet = getPetriNetWithLbe(mPetrifiedIcfg, services);
		mInitialLocs = getLocations(petriNet.getInitialPlaces());
		mErrorLocs = getLocations(petriNet.getAcceptingPlaces());

		mNewIcfg = new BasicIcfg<>(mPetrifiedIcfg.getIdentifier() + "_afterLipton", mPetrifiedIcfg.getCfgSmtToolkit(),
				mPetrifiedIcfg.getLocationClass());
		addLocations(mInitialLocs);
		addLocations(mErrorLocs);

		for (final Transition<IcfgEdge, IPredicate> transition : petriNet.getTransitions()) {
			final IcfgEdge edge = transition.getSymbol();

			final List<IcfgLocation> post = getLocations(transition.getSuccessors());
			final List<IcfgLocation> pre = getLocations(transition.getPredecessors());
			addLocations(pre);
			addLocations(post);

			if (edge instanceof IIcfgForkTransitionThreadOther<?>) {
				final var forkOther = (IIcfgForkTransitionThreadOther<IcfgLocation>) edge;
				final var forkCurrent = forkOther.getCorrespondingIIcfgForkTransitionCurrentThread();

				assert Objects.equals(forkOther.getSource(), forkCurrent.getSource());
				assert Objects.equals(pre, List.of(forkOther.getSource()));
				assert Objects.equals(post, List.of(forkOther.getTarget(), forkCurrent.getTarget()));

				forkOther.getSource().addOutgoing(edge);
				forkOther.getSource().addOutgoing((IcfgEdge) forkCurrent);
				forkOther.getTarget().addIncoming(edge);
				forkCurrent.getTarget().addIncoming((IcfgEdge) forkCurrent);
			} else if (edge instanceof IIcfgJoinTransitionThreadOther<?>) {
				final var joinOther = (IIcfgJoinTransitionThreadOther<IcfgLocation>) edge;
				final var joinCurrent = joinOther.getCorrespondingIIcfgJoinTransitionCurrentThread();

				assert Objects.equals(joinOther.getTarget(), joinCurrent.getTarget());
				assert Objects.equals(pre, List.of(joinOther.getSource(), joinCurrent.getSource()));
				assert Objects.equals(post, List.of(joinOther.getTarget()));

				joinOther.getSource().addOutgoing(edge);
				joinCurrent.getSource().addOutgoing((IcfgEdge) joinCurrent);
				joinOther.getTarget().addIncoming(edge);
				joinOther.getTarget().addIncoming((IcfgEdge) joinCurrent);
			} else {
				assert Objects.equals(pre, List.of(edge.getSource()));
				assert Objects.equals(post, List.of(edge.getTarget()));

				edge.getSource().addOutgoing(edge);
				edge.getTarget().addIncoming(edge);
			}
		}
	}

	private void addLocations(final Collection<IcfgLocation> locs) {
		for (final var loc : locs) {
			addLocation(loc);
		}
	}

	private void addLocation(final IcfgLocation loc) {
		final var procLocs = mNewIcfg.getProgramPoints().get(loc.getProcedure());
		if (procLocs == null) {
			mNewIcfg.addProcedure(loc.getProcedure());
		} else if (procLocs.containsKey(loc.getDebugIdentifier())) {
			// already added
			return;
		}

		// clean slate: remove all edges of location
		loc.removeAllIncoming(loc.getIncomingEdges());
		loc.removeAllOutgoing(loc.getOutgoingEdges());

		final var isProcEntry = Objects.equals(mPetrifiedIcfg.getProcedureEntryNodes().get(loc.getProcedure()), loc);
		final var isProcExit = Objects.equals(mPetrifiedIcfg.getProcedureExitNodes().get(loc.getProcedure()), loc);
		mNewIcfg.addLocation(loc, mInitialLocs.contains(loc), mErrorLocs.contains(loc), isProcEntry, isProcExit,
				mPetrifiedIcfg.getLoopLocations().contains(loc));
	}

	private static List<IcfgLocation> getLocations(final Collection<IPredicate> places) {
		final List<IcfgLocation> result = new ArrayList<>();
		for (final IPredicate p : places) {
			if (p instanceof ISLPredicate) {
				result.add(((ISLPredicate) p).getProgramPoint());
			}
		}
		return result;
	}

	private static BoundedPetriNet<IcfgEdge, IPredicate> getPetriNetWithLbe(final IIcfg<IcfgLocation> icfg,
			final IUltimateServiceProvider services) {
		final CfgSmtToolkit csToolkit = icfg.getCfgSmtToolkit();
		final PredicateFactory predicateFactory =
				new PredicateFactory(services, csToolkit.getManagedScript(), csToolkit.getSymbolTable());
		final PetriInitialAbstractionProvider<IcfgEdge> petriNetProvider =
				new PetriInitialAbstractionProvider<>(services, predicateFactory, true);
		final PetriLbeInitialAbstractionProvider<IcfgEdge> lbeProvider = new PetriLbeInitialAbstractionProvider<>(
				petriNetProvider, services, IcfgEdge.class, new IndependenceSettings(),
				new IcfgCompositionFactory(services, csToolkit), Activator.PLUGIN_ID);
		final Set<IcfgLocation> inUseLocs =
				new HashSet<>(icfg.getCfgSmtToolkit().getConcurrencyInformation().getInUseErrorNodeMap().values());
		final Set<IcfgLocation> errors = icfg.getProcedureErrorNodes().values().stream().flatMap(Collection::stream)
				.filter(x -> !inUseLocs.contains(x)).collect(Collectors.toSet());
		try {
			return lbeProvider.getInitialAbstraction(icfg, errors);
		} catch (final AutomataLibraryException e) {
			throw new AssertionError(e);
		}
	}

	public IIcfg<IcfgLocation> getResult() {
		return mNewIcfg;
	}
}
