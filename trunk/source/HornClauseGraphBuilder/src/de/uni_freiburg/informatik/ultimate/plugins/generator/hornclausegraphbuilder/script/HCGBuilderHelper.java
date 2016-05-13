package de.uni_freiburg.informatik.ultimate.plugins.generator.hornclausegraphbuilder.script;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.hornclausegraphbuilder.HornClauseGraphBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.hornclausegraphbuilder.preferences.HornClauseGraphBuilderPreferenceInitializer;

public class HCGBuilderHelper {
	public static Script constructAndInitializeBackendSmtSolver(IUltimateServiceProvider services, IToolchainStorage storage,
			String filename) {
		final SolverMode solverMode = (new UltimatePreferenceStore(HornClauseGraphBuilder.s_PLUGIN_ID))
				.getEnum(HornClauseGraphBuilderPreferenceInitializer.LABEL_Solver, SolverMode.class);
		
		final String commandExternalSolver = (new UltimatePreferenceStore(HornClauseGraphBuilder.s_PLUGIN_ID))
				.getString(HornClauseGraphBuilderPreferenceInitializer.LABEL_ExtSolverCommand);
		
		final String logicForExternalSolver = (new UltimatePreferenceStore(HornClauseGraphBuilder.s_PLUGIN_ID))
				.getString(HornClauseGraphBuilderPreferenceInitializer.LABEL_ExtSolverLogic);

		final Settings solverSettings = SolverBuilder.constructSolverSettings(
				filename, solverMode, commandExternalSolver, false, null);

		return SolverBuilder.buildAndInitializeSolver(services, 
				storage, 
				solverMode, 
				solverSettings, 
//				dumpUsatCoreTrackBenchmark, 
				false, 
//				dumpMainTrackBenchmark,
				false,
				logicForExternalSolver, 
				"HornClauseSolverBackendSolverScript");		

	}
}
