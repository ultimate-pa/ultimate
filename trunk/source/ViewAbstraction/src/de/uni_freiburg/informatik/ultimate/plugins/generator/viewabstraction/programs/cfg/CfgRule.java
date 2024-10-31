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

import java.util.Map;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IRule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.ProgramConfiguration;

public abstract class CfgRule<E extends CodeBlock>
		implements IRule<ProgramConfiguration<Map<IProgramNonOldVar, Object>, CfgThreadLocalState>> {
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
	// TODO - ParallelComposition (needed for atomic blocks with branching)
	protected final E mEdge;

	public CfgRule(final IUltimateServiceProvider services, final IIcfgSymbolTable symbolTable, final E edge) {
		mServices = services;
		mSymbolTable = symbolTable;
		mEdge = edge;
	}

	@Override
	public Stream<RuleInstantiation> possibleInstances(
			final ProgramConfiguration<Map<IProgramNonOldVar, Object>, CfgThreadLocalState> configuration) {
		return IntStream.range(0, configuration.numberOfThreads())
				.filter(thread -> configuration.getThread(thread).getLocation().equals(mEdge.getSource()))
				.mapToObj(thread -> new RuleInstantiation(thread));
	}

	@Override
	public Stream<ProgramConfiguration<Map<IProgramNonOldVar, Object>, CfgThreadLocalState>> successors(
			final ProgramConfiguration<Map<IProgramNonOldVar, Object>, CfgThreadLocalState> configuration,
			final RuleInstantiation instance) {
		assert instance.getThreads().length == 1;

		final int thread = instance.getThreads()[0];
		final var localState = configuration.getThread(thread);
		assert localState.getLocation().equals(mEdge.getSource());

		final var view = new CfgProgramStateView(mSymbolTable, configuration.getControllerState(), localState);
		return apply(view).map(newState -> updateConfig(configuration, thread, newState));
	}

	protected abstract Stream<CfgProgramStateView> apply(CfgProgramStateView stateView);

	private ProgramConfiguration<Map<IProgramNonOldVar, Object>, CfgThreadLocalState> updateConfig(
			final ProgramConfiguration<Map<IProgramNonOldVar, Object>, CfgThreadLocalState> config, final int thread,
			final CfgProgramStateView newState) {
		var newLocalState = newState.getLocalState();
		if (newLocalState.getLocation().equals(mEdge.getSource())) {
			newLocalState = newLocalState.updateLocation((BoogieIcfgLocation) mEdge.getTarget());
		}

		return config.replaceController(newState.getGlobalState()).replaceThread(thread, newLocalState);
	}

	@Override
	public abstract int extensionSize();

	@Override
	public boolean isSpecRule() {
		return ((BoogieIcfgLocation) mEdge.getTarget()).isErrorLocation();
	}

	@Override
	public String toString() {
		return mEdge.toString();
	}
}