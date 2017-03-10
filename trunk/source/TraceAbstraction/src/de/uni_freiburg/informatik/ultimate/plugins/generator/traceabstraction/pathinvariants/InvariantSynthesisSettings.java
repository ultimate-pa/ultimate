package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.TemplateDimensionsStrategy;

public class InvariantSynthesisSettings {
	
	// The settings for the theorem solver, that is used for invariant synthesis.
	Settings mSolverSettings;
	private final boolean mUseNonlinearConstraints;
	private final boolean mUseUnsatCores;
	private final boolean mUseAbstractInterpretationPredicates;
	private final boolean mUseWPForPathInvariants;
	private final TemplateDimensionsStrategy mTemplateDimensionsStrat;
	
	public InvariantSynthesisSettings(Settings solverSettings, final TemplateDimensionsStrategy templateDimensionsStrat, 
			final boolean useNonlinearConstraints, 	final boolean useUnsatCores, 
			final boolean useAbstractInterpretationPredicates, final boolean useWPForPathInvariants) {
		mUseNonlinearConstraints = useNonlinearConstraints;
		mSolverSettings = solverSettings;
		mUseUnsatCores = useUnsatCores;
		mUseAbstractInterpretationPredicates = useAbstractInterpretationPredicates;
		mUseWPForPathInvariants = useWPForPathInvariants;
		mTemplateDimensionsStrat = templateDimensionsStrat;
	}
	
	public InvariantSynthesisSettings(Settings solverSettings, final boolean useNonlinearConstraints,
			final boolean useUnsatCores, final boolean useAbstractInterpretationPredicates, final boolean useWPForPathInvariants) {
		mUseNonlinearConstraints = useNonlinearConstraints;
		mSolverSettings = solverSettings;
		mUseUnsatCores = useUnsatCores;
		mUseAbstractInterpretationPredicates = useAbstractInterpretationPredicates;
		mUseWPForPathInvariants = useWPForPathInvariants;
		mTemplateDimensionsStrat = null;
	}
	
	public final boolean useNonLinearConstraints() {
		return mUseNonlinearConstraints;
	}
	
	public final boolean useUnsatCores() {
		return mUseUnsatCores;
	}
	
	public final boolean useAbstractInterpretation() {
		return mUseAbstractInterpretationPredicates;
	}
	
	public final boolean useWeakestPrecondition() {
		return mUseWPForPathInvariants;
	}
	
	public final Settings getSolverSettings() {
		return mSolverSettings;
	}
	
	public final TemplateDimensionsStrategy getTemplateDimensionsStrategy() {
		return mTemplateDimensionsStrat;
	}
	
}
