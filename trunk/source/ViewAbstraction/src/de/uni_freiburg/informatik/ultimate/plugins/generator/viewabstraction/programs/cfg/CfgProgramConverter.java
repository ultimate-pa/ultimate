/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ViewAbstraction plug-in.
 *
 * The ULTIMATE ViewAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ViewAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ViewAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ViewAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ViewAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.cfg;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Configuration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Program;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.ProgramState.ControllerState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.ProgramState.ThreadState;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;

public class CfgProgramConverter {
	private final IUltimateServiceProvider mServices;
	private final BoogieIcfgContainer mIcfg;
	private final Program<ProgramState<Map<IProgramNonOldVar, Object>, CfgThreadLocalState>> mProgram;

	public CfgProgramConverter(final IUltimateServiceProvider services, final BoogieIcfgContainer icfg) {
		mServices = services;
		mIcfg = icfg;

		final var rules = new IcfgEdgeIterator(icfg).asStream().map(this::createRule).collect(Collectors.toList());
		mProgram = new Program<>(ProgramState.class, (List) rules);
	}

	public Program<ProgramState<Map<IProgramNonOldVar, Object>, CfgThreadLocalState>> getProgram() {
		return mProgram;
	}

	public Configuration<ProgramState<Map<IProgramNonOldVar, Object>, CfgThreadLocalState>>
			getInitialConfiguration(final int k) {
		final var result = new ArrayList<ProgramState<Map<IProgramNonOldVar, Object>, CfgThreadLocalState>>();

		final var initialGlobals = getInitialGlobalState();
		result.add(new ControllerState<>(initialGlobals));

		final var threadTemplates = mIcfg.getCfgSmtToolkit().getProcedures();
		for (final var template : threadTemplates) {
			final var initialLoc = mIcfg.getProcedureEntryNodes().get(template);
			final var initialValues =
					getInitialAssignment(mIcfg.getCfgSmtToolkit().getSymbolTable().getLocals(template));
			for (int i = 0; i < k; ++i) {
				final var state = new CfgThreadLocalState(mIcfg.getCfgSmtToolkit().getSymbolTable(), template,
						initialLoc, initialValues);
				result.add(new ThreadState<>(state));
			}
		}

		return new Configuration<>(new ImmutableList<>(result));
	}

	private CfgRule<?> createRule(final IcfgEdge edge) {
		if (edge instanceof StatementSequence) {
			return new StatementSequenceRule(mServices, mIcfg.getCfgSmtToolkit().getSymbolTable(),
					(StatementSequence) edge);
		}
		throw new UnsupportedOperationException(
				"Edges of type " + edge.getClass().getSimpleName() + " not yet supported");
	}

	private Map<IProgramNonOldVar, Object> getInitialGlobalState() {
		return getInitialAssignment(mIcfg.getCfgSmtToolkit().getSymbolTable().getGlobals());
	}

	private static <V extends IProgramVar> Map<V, Object> getInitialAssignment(final Set<V> variables) {
		final var result = new HashMap<V, Object>();

		for (final var variable : variables) {
			result.put(variable, getInitialValue(variable.getSort()));
		}

		return result;
	}

	private static Object getInitialValue(final Sort sort) {
		if (SmtSortUtils.isIntSort(sort)) {
			return 0;
		}
		throw new UnsupportedOperationException("unknown sort " + sort);
	}
}
