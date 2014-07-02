package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;

public class PreferenceInitializer extends UltimatePreferenceInitializer {

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<Boolean>(LABEL_IgnoreDownStates,
						false, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_DeterminizationOnDemand,
						true, PreferenceType.Boolean),
				new UltimatePreferenceItem<BInterpolantAutomaton>(
						LABEL_BuchiInterpolantAutomaton,
						BInterpolantAutomaton.Staged, PreferenceType.Combo,
						BInterpolantAutomaton.values()),
				new UltimatePreferenceItem<Boolean>(LABEL_BouncerStem,
						true, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_BouncerLoop,
						false, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_ScroogeNondeterminismStem,
						false, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_ScroogeNondeterminismLoop,
						false, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_CannibalizeLoop,
						false, PreferenceType.Boolean),
				new UltimatePreferenceItem<Integer>(LABEL_LoopUnwindings, 2,
						PreferenceType.Integer,
						new IUltimatePreferenceItemValidator.IntegerValidator(
								0, 1000000)),
				new UltimatePreferenceItem<INTERPOLATION>(
						TraceAbstractionPreferenceInitializer.LABEL_INTERPOLATED_LOCS, 
						INTERPOLATION.Craig_TreeInterpolation,
						PreferenceType.Combo, 
						TraceAbstractionPreferenceInitializer.INTERPOLATION.values()),
				new UltimatePreferenceItem<Boolean>(LABEL_ExtSolverRank,
						true, PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(LABEL_ExtSolverCommandRank,
						DEF_ExtSolverCommandRank, PreferenceType.String),
				new UltimatePreferenceItem<Boolean>(LABEL_NonLinearConstraints,
						false, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_TemplateBenchmarkMode,
						false, PreferenceType.Boolean),	
				new UltimatePreferenceItem<Boolean>(LABEL_DumpToFile,
						false, PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(LABEL_DumpPath,
						DEF_DumpPath, PreferenceType.Directory),
				new UltimatePreferenceItem<Boolean>(LABEL_TermcompProof,
						false, PreferenceType.Boolean),
		};
	}

	@Override
	protected String getPlugID() {
		return Activator.s_PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return "Buchi Automizer (Termination Analysis)";
	}
	
	public static final String LABEL_IgnoreDownStates = "Ignore down states";
	public static final String LABEL_DeterminizationOnDemand = "Determinization on demand";
	public static final String LABEL_BuchiInterpolantAutomaton = "Buchi interpolant automaton";
	public static final String LABEL_BouncerStem = "Bouncer stem";
	public static final String LABEL_BouncerLoop = "Bouncer loop";
	public static final String LABEL_ScroogeNondeterminismStem = "ScroogeNondeterminism stem";
	public static final String LABEL_ScroogeNondeterminismLoop = "ScroogeNondeterminism loop";
	public static final String LABEL_CannibalizeLoop = "Cannibalize loop";
	public static final String LABEL_LoopUnwindings = "Max number of loop unwindings";
	public static final String LABEL_ExtSolverRank = "Use external solver (rank synthesis)";
	public static final String LABEL_ExtSolverCommandRank = "Command for external solver (rank synthesis)";
	public static final String DEF_ExtSolverCommandRank = "z3 SMTLIB2_COMPLIANT=true -memory:256 -smt2 -in -t:5000";
	public static final String LABEL_NonLinearConstraints = "Allow nonlinear constraints";
	public static final String LABEL_TemplateBenchmarkMode = "Template benchmark mode";
	public static final String LABEL_DumpToFile = "Dump SMT script to file";
	public static final String LABEL_DumpPath = "To the following directory";
	public static final String DEF_DumpPath = "";
	public static final String LABEL_TermcompProof = "Construct termination proof for TermComp";
	
	public enum BInterpolantAutomaton { LassoAutomaton, EagerNondeterminism, ScroogeNondeterminism, Deterministic, Staged };
	
}