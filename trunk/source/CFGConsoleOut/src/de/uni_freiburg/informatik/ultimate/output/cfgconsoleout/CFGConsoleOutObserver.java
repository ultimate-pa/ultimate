/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CFGConsoleOut plug-in.
 *
 * The ULTIMATE CFGConsoleOut plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CFGConsoleOut plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CFGConsoleOut plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CFGConsoleOut plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CFGConsoleOut plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.output.cfgconsoleout;

import java.util.Collections;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CFG2NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

public class CFGConsoleOutObserver extends BaseObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	public CFGConsoleOutObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public boolean process(final IElement root) {
		if (root instanceof IIcfg<?>) {
			processIcfg((IIcfg<?>) root);
		}
		return false;
	}

	private void processIcfg(final IIcfg<?> icfg) {
		final IcfgEdgeIterator iter = new IcfgEdgeIterator(icfg);

		mLogger.info(
				"InitLocs: " + icfg.getInitialNodes().stream().map(a -> a.toString()).collect(Collectors.joining(",")));
		mLogger.info("LoopLocs: "
				+ icfg.getLoopLocations().stream().map(a -> a.toString()).collect(Collectors.joining(",")));
		mLogger.info("ErrorLocs: "
				+ IcfgUtils.getErrorLocations(icfg).stream().map(a -> a.toString()).collect(Collectors.joining(",")));
		mLogger.info("Axioms: " + icfg.getCfgSmtToolkit().getSmtSymbols());

		while (iter.hasNext()) {
			final IcfgEdge current = iter.next();
			mLogger.info(toString(current));
		}

		mLogger.info(getNwa(icfg));
	}

	private INestedWordAutomaton<IIcfgTransition<?>, IPredicate> getNwa(final IIcfg<?> icfg) {
		final CfgSmtToolkit toolkit = icfg.getCfgSmtToolkit();
		final PredicateFactory predicateFactory = new PredicateFactory(mServices, toolkit.getManagedScript(),
				toolkit.getSymbolTable());
		final IEmptyStackStateFactory<IPredicate> stateFac = new PredicateFactoryRefinement(mServices, toolkit.getManagedScript(),
				predicateFactory, false, Collections.emptySet());

		final INestedWordAutomaton<IIcfgTransition<?>, IPredicate> nwa = CFG2NestedWordAutomaton.constructAutomatonWithSPredicates(
				mServices, icfg, stateFac, IcfgUtils.getErrorLocations(icfg), true, predicateFactory);
		return nwa;
	}

	private String toString(final IcfgEdge current) {
		final StringBuilder sb = new StringBuilder();

		sb.append(current.getSource());
		sb.append(" -- ");
		if (current instanceof IIcfgInternalTransition<?>) {
			sb.append(current.getTransformula());
		} else if (current instanceof IIcfgCallTransition<?>) {
			final IIcfgCallTransition<?> call = (IIcfgCallTransition<?>) current;
			sb.append(call.getLocalVarsAssignment());
		} else if (current instanceof IIcfgReturnTransition<?, ?>) {
			final IIcfgReturnTransition<?, ?> ret = (IIcfgReturnTransition<?, ?>) current;
			sb.append("(");
			sb.append(ret.getCallerProgramPoint());
			sb.append(") ");
			sb.append(ret.getAssignmentOfReturn());
		}

		sb.append(" -- ");
		sb.append(current.getTarget());

		return sb.toString();
	}

}
