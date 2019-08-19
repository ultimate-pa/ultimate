/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstractionConcurrent plug-in.
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;

public abstract class Icfg2PetriNet {

	protected final ILogger mLogger;
	protected final IUltimateServiceProvider mServices;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	private final BoogieIcfgContainer mIcfg;
	private final CfgSmtToolkit mCsToolkit;
	private final PredicateFactory mPredicateFactory;




	public Icfg2PetriNet(final BoogieIcfgContainer icfg,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final IUltimateServiceProvider services, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mIcfg = icfg;
		mCsToolkit = csToolkit;
		mPredicateFactory = predicateFactory;

		final Set<IcfgEdge> alphabet = new HashSet<>();

		final BoundedPetriNet<IcfgEdge, IPredicate> net = new BoundedPetriNet<>(
				new AutomataLibraryServices(services), alphabet, false);

		final Set<BoogieIcfgLocation> init = icfg.getInitialNodes();
		final Map<String, Set<BoogieIcfgLocation>> procErrorNodes = icfg.getProcedureErrorNodes();

		final IValueConstruction<BoogieIcfgLocation, IPredicate> valueConstruction =
				new IValueConstruction<BoogieIcfgLocation, IPredicate>() {

			@Override
			public IPredicate constructValue(final BoogieIcfgLocation key) {
				final IPredicate pred = predicateFactory.newDontCarePredicate(key);
				final boolean isInitial = init.contains(key);
				final String proc = key.getProcedure();
				final boolean isFinal = procErrorNodes.get(proc).contains(key);
				final IPredicate place = net.addPlace(pred, isInitial, isFinal);
				return place;
			}

		};
		final ConstructionCache<BoogieIcfgLocation, IPredicate> cc = new ConstructionCache<>(valueConstruction);

		for (final BoogieIcfgLocation loc : init) {
			cc.getOrConstruct(loc);
		}

		final IcfgEdgeIterator it = new IcfgEdgeIterator(icfg);
		while(it.hasNext()) {
			final IcfgEdge edge = it.next();
			final IPredicate pred = cc.getOrConstruct((BoogieIcfgLocation) edge.getSource());
			final IPredicate succ = cc.getOrConstruct((BoogieIcfgLocation) edge.getTarget());
			net.addTransition(edge, Collections.singleton(pred), Collections.singleton(succ));
		}
	}

}
