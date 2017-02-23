package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;

public class InvariantSynthesisSettings {
	
	// The settings for the theorem solver, that is used for invariant synthesis.
	Settings mSolverSettings;
	private final boolean mUseNonlinearConstraints;
	private final boolean mUseUnsatCores;
	private final boolean mUseAbstractInterpretationPredicates;
	private final boolean mUseWPForPathInvariants;
	
	public InvariantSynthesisSettings(Settings solverSettings, final boolean useNonlinearConstraints, 
			final boolean useUnsatCores, final boolean useAbstractInterpretationPredicates, final boolean useWPForPathInvariants) {
		mUseNonlinearConstraints = useNonlinearConstraints;
		mSolverSettings = solverSettings;
		mUseUnsatCores = useUnsatCores;
		mUseAbstractInterpretationPredicates = useAbstractInterpretationPredicates;
		mUseWPForPathInvariants = useWPForPathInvariants;
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
	
}
