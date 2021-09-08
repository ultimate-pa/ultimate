/*
 * Copyright (C) 2021 Dennis Wölfing
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstractionConcurrent plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstractionConcurrent plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstractionConcurrent plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstractionConcurrent plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstractionConcurrent plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

/**
 * A CEGAR loop for Petri nets that repeatedly applies Lipton Reduction after each iteration.
 *
 * @author Dennis Wölfing
 *
 * @param <L>
 *            The type of the letters of the transitions.
 */
public class CegarLoopForPetriNetWithRepeatedLiptonReduction<L extends IIcfgTransition<?>>
		extends CegarLoopForPetriNet<L> {

	/**
	 * Construct the CEGAR loop.
	 *
	 * @param name
	 * @param rootNode
	 * @param csToolkit
	 * @param predicateFactory
	 * @param taPrefs
	 * @param errorLocs
	 * @param services
	 * @param compositionFactory
	 * @param transitionClazz
	 */
	public CegarLoopForPetriNetWithRepeatedLiptonReduction(final DebugIdentifier name, final IIcfg<?> rootNode,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Set<IcfgLocation> errorLocs, final IUltimateServiceProvider services,
			final IPLBECompositionFactory<L> compositionFactory, final Class<L> transitionClazz) {
		super(name, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, services, compositionFactory,
				transitionClazz);
		if (mPref.useLbeInConcurrentAnalysis() == PetriNetLbe.OFF) {
			throw new IllegalArgumentException(getClass().getSimpleName() + "without Lipton reduction");
		}
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		final boolean result = super.refineAbstraction();
		mAbstraction = applyLargeBlockEncoding((BoundedPetriNet<L, IPredicate>) mAbstraction);
		return result;
	}
}
