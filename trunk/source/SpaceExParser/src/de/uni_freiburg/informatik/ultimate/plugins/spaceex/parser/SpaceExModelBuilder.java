package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.HybridModel;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridSystem;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg.HybridIcfgGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg.HybridIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg.HybridVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.Sspaceex;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SpaceExPreferenceManager;
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
	private final SpaceExPreferenceManager mPreferenceManager;
	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage mToolchainStorage;
	private HybridVariableManager mVariableManager;
	
	public SpaceExModelBuilder(final Sspaceex spaceEx, final ILogger logger,
			final SpaceExPreferenceManager preferenceManager, final IUltimateServiceProvider services,
			final IToolchainStorage toolchainStorage) throws Exception {
		mLogger = logger;
		mServices = services;
		mToolchainStorage = toolchainStorage;
		mVariableManager = null;
		mPreferenceManager = preferenceManager;
		mModel = createModel(spaceEx);
	}
	
	private BasicIcfg<IcfgLocation> createModel(final Sspaceex spaceEx) throws Exception {
		// Create the model
		mLogger.info("Starting creation of hybrid model...");
		final long startTime = System.nanoTime();
		final HybridModel model = new HybridModel(spaceEx, mLogger, mPreferenceManager);
		final long estimatedTime = System.nanoTime() - startTime;
		mLogger.info("Creation of hybrid model done in " + estimatedTime / (float) 1000000 + " milliseconds");
		// get the System specified in the config.
		final HybridSystem system = mPreferenceManager.getRegardedSystem(model);
		// calculate the parallel Compositions of the different preferencegroups.
		final Map<Integer, HybridAutomaton> parallelCompositions;
		// if the preferencemanager has preferencegroups, calculate the parallel compositions for those groups.
		if (mPreferenceManager.hasPreferenceGroups()) {
			mLogger.info("Starting Computation of parallel compositions...");
			parallelCompositions = model.calculateParallelCompositionsForGroups(system);
			mPreferenceManager.setGroupIdToParallelComposition(parallelCompositions);
		} else {
			parallelCompositions = new HashMap<>();
		}
		// set some automaton for the toolkit generation, anyone will do.
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
		final CfgSmtToolkit smtToolkit = generateToolkit(automaton);
		final HybridIcfgGenerator gen =
				new HybridIcfgGenerator(mLogger, mPreferenceManager, smtToolkit, mVariableManager);
		// return gen.getSimpleIcfg();
		return gen.createIfcgFromComponents(automaton);
	}
	
	private CfgSmtToolkit generateToolkit(final HybridAutomaton automaton) {
		IPredicate axioms = null;
		final Set<String> procedures = new HashSet<>();
		procedures.add("MAIN");
		final Script script = SolverBuilder.buildAndInitializeSolver(mServices, mToolchainStorage,
				mPreferenceManager.getSolverMode(), mPreferenceManager.getmSolverSettings(),
				mPreferenceManager.ismDumpUsatCoreTrackBenchmark(), mPreferenceManager.ismDumpMainTrackBenchmark(),
				mPreferenceManager.getmLogicForExternalSolver(), "SpaceExTA");
		final ManagedScript managedScript = new ManagedScript(mServices, script);
		mVariableManager = new HybridVariableManager(managedScript);
		final HybridIcfgSymbolTable symbolTable =
				new HybridIcfgSymbolTable(managedScript, automaton, "MAIN", mVariableManager);
		final DefaultIcfgSymbolTable defaultTable = new DefaultIcfgSymbolTable(symbolTable, procedures);
		defaultTable.finishConstruction();
		final HashRelation<String, IProgramNonOldVar> proc2globals = new HashRelation<>();
		final ModifiableGlobalsTable modifiableGlobalsTable = new ModifiableGlobalsTable(proc2globals);
		axioms = new IPredicate() {
			
			@Override
			public Set<IProgramVar> getVars() {
				return Collections.emptySet();
			}
			
			@Override
			public String[] getProcedures() {
				return procedures.toArray(new String[procedures.size()]);
			}
			
			@Override
			public Term getFormula() {
				return script.term("true");
			}
			
			@Override
			public Term getClosedFormula() {
				return script.term("true");
			}
		};
		return new CfgSmtToolkit(modifiableGlobalsTable, managedScript, defaultTable, axioms, procedures);
	}
	
	public BasicIcfg<IcfgLocation> getModel() {
		return mModel;
	}
}
