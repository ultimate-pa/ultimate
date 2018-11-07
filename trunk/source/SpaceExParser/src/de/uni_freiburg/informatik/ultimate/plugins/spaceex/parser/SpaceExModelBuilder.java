/*
 * Copyright (C) 2016 Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE SpaceExParser plug-in.
 *
 * The ULTIMATE SpaceExParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SpaceExParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SpaceExParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SpaceExParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SpaceExParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.SmtSymbols;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.HybridModel;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridSystem;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg.HybridIcfgGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg.HybridIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg.HybridVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.Sspaceex;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SpaceExPreferenceContainer;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SpaceExPreferenceManager;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.util.HybridTranslatorConstants;
import de.uni_freiburg.informatik.ultimate.util.datastructures.SerialProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Constructs SpaceEx Ultimate model representation.
 *
 * @author greitsch@informatik.uni-freiburg.de
 * @author loefflju@informatik.uni-freiburg.de
 *
 */
public class SpaceExModelBuilder {

	private final ILogger mLogger;
	private final BasicIcfg<IcfgLocation> mModel;
	private final SpaceExPreferenceContainer mPreferenceContainer;
	private final SpaceExPreferenceManager mPreferenceManager;
	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage mToolchainStorage;
	private final HybridVariableManager mVariableManager;

	public SpaceExModelBuilder(final Sspaceex spaceEx, final ILogger logger,
			final SpaceExPreferenceContainer preferenceContainer, final SpaceExPreferenceManager preferenceManager,
			final IUltimateServiceProvider services, final IToolchainStorage toolchainStorage) throws Exception {
		mLogger = logger;
		mServices = services;
		mToolchainStorage = toolchainStorage;
		mPreferenceContainer = preferenceContainer;
		mPreferenceManager = preferenceManager;
		mVariableManager = new HybridVariableManager();
		mModel = createModel(spaceEx);
	}

	private BasicIcfg<IcfgLocation> createModel(final Sspaceex spaceEx) throws Exception {
		// Create the model
		mLogger.info("Starting creation of hybrid model...");
		final long startTime = System.nanoTime();
		final HybridModel model = new HybridModel(spaceEx, mLogger, mPreferenceContainer);
		final HybridSystem system = model.getSystemByName(mPreferenceContainer.getSystemName());
		mLogger.debug("SYSTEM:\n " + system);
		final long estimatedTime = System.nanoTime() - startTime;
		mLogger.info("Creation of hybrid model done in " + estimatedTime / (float) 1000000 + " milliseconds");

		// calculate the parallel Compositions of the different
		// preferencegroups.
		final Map<Integer, HybridAutomaton> parallelCompositions;

		// if the preferencemanager has preferencegroups, calculate the parallel
		// compositions for those groups.
		if (mPreferenceContainer.hasPreferenceGroups()) {
			mLogger.info("Starting Computation of parallel compositions...");
			parallelCompositions = model.calculateParallelCompositionsForGroups(system);
			mVariableManager.setGroupIdToParallelComposition(parallelCompositions);
		} else {
			parallelCompositions = new HashMap<>();
		}

		// get some parallel composition for the toolkit generation, anyone will
		// do,
		// because we only need the variables of the automata.
		HybridAutomaton automaton;
		if (!parallelCompositions.isEmpty()) {
			automaton = parallelCompositions.get(1);
		} else {
			if (!system.getAutomata().isEmpty()) {
				automaton = model.mergeAutomata(system, null);
			} else {
				throw new IllegalStateException("system does not have any automata");
			}
		}
		// generate a smt toolkit in order to build transformulas later on.
		final CfgSmtToolkit smtToolkit = generateToolkit(automaton);

		// transform parallel compositions
		final HybridIcfgGenerator gen =
				new HybridIcfgGenerator(mLogger, mPreferenceContainer, smtToolkit, mVariableManager);
		return gen.createIfcgFromComponents(automaton);
	}

	private CfgSmtToolkit generateToolkit(final HybridAutomaton automaton) {
		final Set<String> procedures = new HashSet<>();
		procedures.add(HybridTranslatorConstants.PROC_NAME);

		final Script script = SolverBuilder.buildAndInitializeSolver(mServices, mToolchainStorage,
				mPreferenceManager.getSolverMode(), mPreferenceManager.getSolverSettings(),
				mPreferenceManager.isDumpUsatCoreTrackBenchmark(), mPreferenceManager.isDumpMainTrackBenchmark(),
				mPreferenceManager.getLogicForExternalSolver(), "SpaceExTA");

		final ManagedScript managedScript = new ManagedScript(mServices, script);
		mVariableManager.setScript(managedScript);

		final HybridIcfgSymbolTable symbolTable = new HybridIcfgSymbolTable(managedScript, automaton,
				HybridTranslatorConstants.PROC_NAME, mVariableManager);

		final DefaultIcfgSymbolTable defaultTable = new DefaultIcfgSymbolTable(symbolTable, procedures);
		defaultTable.finishConstruction();

		final HashRelation<String, IProgramNonOldVar> proc2globals = new HashRelation<>();

		final ModifiableGlobalsTable modifiableGlobalsTable = new ModifiableGlobalsTable(proc2globals);

		final Map<String, List<ILocalProgramVar>> inParams =
				Collections.singletonMap(HybridTranslatorConstants.PROC_NAME, Collections.emptyList());
		final Map<String, List<ILocalProgramVar>> outParams = inParams;
		return new CfgSmtToolkit(modifiableGlobalsTable, managedScript, defaultTable, procedures, inParams, outParams,
				new IcfgEdgeFactory(new SerialProvider()), null, new SmtSymbols(script));
	}

	public BasicIcfg<IcfgLocation> getModel() {
		return mModel;
	}
}
