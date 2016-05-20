package de.uni_freiburg.informatik.ultimate.plugins.generator.hornclausegraphbuilder.script;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.hornclausegraphbuilder.HornClauseGraphBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.hornclausegraphbuilder.preferences.HornClauseGraphBuilderPreferenceInitializer;

public class HCGBuilderHelper {
	
	public static class ConstructAndInitializeBackendSmtSolver {
	
		private Settings m_SolverSettings;
		private String m_LogicForExternalSolver;
		private Script m_Script;

		public ConstructAndInitializeBackendSmtSolver(IUltimateServiceProvider services, 
				IToolchainStorage storage,
				String filename) {
			constructAndInitializeBackendSmtSolver(services, storage, filename);
		}

		void constructAndInitializeBackendSmtSolver(
				IUltimateServiceProvider services, 
				IToolchainStorage storage,
				String filename) {
			final SolverMode solverMode = (new RcpPreferenceProvider(HornClauseGraphBuilder.s_PLUGIN_ID))
					.getEnum(HornClauseGraphBuilderPreferenceInitializer.LABEL_Solver, SolverMode.class);

			final String commandExternalSolver = (new RcpPreferenceProvider(HornClauseGraphBuilder.s_PLUGIN_ID))
					.getString(HornClauseGraphBuilderPreferenceInitializer.LABEL_ExtSolverCommand);

			m_LogicForExternalSolver = (new RcpPreferenceProvider(HornClauseGraphBuilder.s_PLUGIN_ID))
					.getString(HornClauseGraphBuilderPreferenceInitializer.LABEL_ExtSolverLogic);

			m_SolverSettings = SolverBuilder.constructSolverSettings(
					filename, solverMode, commandExternalSolver, false, null);

			m_Script =  SolverBuilder.buildAndInitializeSolver(services, 
					storage, 
					solverMode, 
					m_SolverSettings, 
					//				dumpUsatCoreTrackBenchmark, 
					false, 
					//				dumpMainTrackBenchmark,
					false,
					m_LogicForExternalSolver, 
					"HornClauseSolverBackendSolverScript");		
		}

		public Settings getSolverSettings() {
			return m_SolverSettings;
		}

		public String getLogicForExternalSolver() {
			return m_LogicForExternalSolver;
		}

		public Script getScript() {
			return m_Script;
		}
	}
}
