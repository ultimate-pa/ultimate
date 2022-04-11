/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.RemoveDead;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.cfg2automaton.Cfg2Automaton;

/**
 * Provides an initial abstraction in the form of a Petri net. This is primarily applicable for concurrent programs.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of transitions
 */
public class PetriInitialAbstractionProvider<L extends IIcfgTransition<?>>
		implements IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>> {

	private static final boolean KEEP_USELESS_SUCCESSOR_PLACES = true;

	private final IUltimateServiceProvider mServices;
	private final PredicateFactory mPredicateFactory;
	private final boolean mRemoveDeadEnds;

	/**
	 * Create a new instance.
	 *
	 * @param services
	 *            Ultimate services used in the creation of the Petri net
	 * @param predicateFactory
	 *            A predicate factory used to construct places of the Petri net
	 * @param removeDeadEnds
	 *            {@code true} to remove dead ends from the created Petri net, {@code false} to return it unmodified
	 */
	public PetriInitialAbstractionProvider(final IUltimateServiceProvider services,
			final PredicateFactory predicateFactory, final boolean removeDeadEnds) {
		mServices = services;
		mPredicateFactory = predicateFactory;
		mRemoveDeadEnds = removeDeadEnds;
	}

	@Override
	public BoundedPetriNet<L, IPredicate> getInitialAbstraction(final IIcfg<? extends IcfgLocation> icfg,
			final Set<? extends IcfgLocation> errorLocs) throws AutomataOperationCanceledException {
		final BoundedPetriNet<L, IPredicate> net =
				Cfg2Automaton.constructPetriNetWithSPredicates(mServices, icfg, errorLocs, mPredicateFactory);
		if (!mRemoveDeadEnds) {
			return net;
		}

		try {
			return new RemoveDead<>(new AutomataLibraryServices(mServices), net, null, KEEP_USELESS_SUCCESSOR_PLACES)
					.getResult();
		} catch (final AutomataOperationCanceledException aoce) {
			final String taskDescription = "removing dead transitions from Petri net that has " + net.sizeInformation();
			aoce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
			throw aoce;
		} catch (final PetriNetNot1SafeException e) {
			throw new AssertionError(e);
		}
	}
}
