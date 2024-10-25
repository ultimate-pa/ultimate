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
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Configuration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IRule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.ProgramState.ControllerState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.ProgramState.ThreadState;

public abstract class CfgRule<E extends CodeBlock>
		implements IRule<ProgramState<Map<IProgramNonOldVar, Object>, CfgThreadLocalState>> {
	protected final IUltimateServiceProvider mServices;
	protected final IIcfgSymbolTable mSymbolTable;

	// TODO extend it to fork-join programs
	// TODO - JoinThreadOther
	// TODO - ForkThreadOther
	//
	// TODO why not?
	// TODO - GotoEdge
	//
	// TODO add support for atomic blocks
	// TODO - SequentialComposition (suffices for atomic blocks containing sequences of simple statements)
	// TODO - ParallelComposition (needed for atomic blocks with branching)
	protected final E mEdge;

	private Configuration<ProgramState<Map<IProgramNonOldVar, Object>, CfgThreadLocalState>> mLastConfig;
	private List<Configuration<ProgramState<Map<IProgramNonOldVar, Object>, CfgThreadLocalState>>> mLastSuccessors;

	public CfgRule(final IUltimateServiceProvider services, final IIcfgSymbolTable symbolTable, final E edge) {
		mServices = services;
		mSymbolTable = symbolTable;
		mEdge = edge;
	}

	@Override
	public boolean isApplicable(
			final Configuration<ProgramState<Map<IProgramNonOldVar, Object>, CfgThreadLocalState>> config) {
		return !successors(config).isEmpty();
	}

	@Override
	public List<Configuration<ProgramState<Map<IProgramNonOldVar, Object>, CfgThreadLocalState>>>
			successors(final Configuration<ProgramState<Map<IProgramNonOldVar, Object>, CfgThreadLocalState>> config) {
		if (mLastConfig == config) {
			return mLastSuccessors;
		}

		Map<IProgramNonOldVar, Object> globalState = null;
		final List<Configuration<ProgramState<Map<IProgramNonOldVar, Object>, CfgThreadLocalState>>> successors =
				new ArrayList<>();
		for (int i = 0; i < config.size(); ++i) {
			final var state = config.get(i);
			assert (i == 0) == state.isControllerState();
			if (state.isControllerState()) {
				globalState = state.getControllerState();
				continue;
			}

			assert globalState != null;
			final var localState = state.getThreadState();
			if (!localState.getLocation().equals(mEdge.getSource())) {
				continue;
			}

			final var view = new CfgProgramStateView(mSymbolTable, globalState, localState);
			final var newState = apply(view);
			if (newState == null) {
				continue;
			}

			var newLocalState = newState.getLocalState();
			if (newLocalState.getLocation().equals(mEdge.getSource())) {
				newLocalState = newLocalState.updateLocation((BoogieIcfgLocation) mEdge.getTarget());
			}

			final var newConfig = config.replace(0, new ControllerState<>(newState.getGlobalState())).replace(i,
					new ThreadState<>(newLocalState));
			successors.add(newConfig);
		}

		mLastConfig = config;
		mLastSuccessors = successors;
		return successors;
	}

	protected abstract CfgProgramStateView apply(CfgProgramStateView stateView);

	@Override
	public abstract int extensionSize();
}