/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.initialabstraction;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CFG2NestedWordAutomaton;

public class PetriInitialAbstractionProvider<L extends IIcfgTransition<?>>
		implements IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>> {

	private static final boolean ADD_THREAD_USAGE_MONITORS = true;
	private static final boolean INTERPROCEDURAL = false;

	private final IUltimateServiceProvider mServices;
	private final PredicateFactory mPredicateFactory;
	private final IEmptyStackStateFactory<IPredicate> mStateFactory;

	public PetriInitialAbstractionProvider(final IUltimateServiceProvider services,
			final IEmptyStackStateFactory<IPredicate> stateFactory, final PredicateFactory predicateFactory) {
		mServices = services;
		mPredicateFactory = predicateFactory;
		mStateFactory = stateFactory;
	}

	@Override
	public BoundedPetriNet<L, IPredicate> getInitialAbstraction(final IIcfg<? extends IcfgLocation> icfg,
			final Set<? extends IcfgLocation> errorLocs) {
		return CFG2NestedWordAutomaton.constructPetriNetWithSPredicates(mServices, icfg, mStateFactory, errorLocs,
				INTERPROCEDURAL, mPredicateFactory, ADD_THREAD_USAGE_MONITORS);
	}
}
