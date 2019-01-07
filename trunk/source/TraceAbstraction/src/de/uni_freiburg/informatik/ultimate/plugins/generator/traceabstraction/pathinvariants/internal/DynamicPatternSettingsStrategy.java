package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.xnf.Dnf;

public class DynamicPatternSettingsStrategy extends LocationDependentLinearInequalityInvariantPatternStrategy {


	protected Map<IcfgLocation, Set<IProgramVar>> mLocations2LiveVariables;
	protected Map<IcfgLocation, PatternSetting> mLoc2PatternSetting;

	public DynamicPatternSettingsStrategy(final AbstractTemplateIncreasingDimensionsStrategy dimensionsStrat, final int maxRounds, final Set<IProgramVar> allProgramVariables,
			final boolean alwaysStrictAndNonStrictCopies, final boolean useStrictInequalitiesAlternatingly) {
		super(dimensionsStrat, maxRounds, allProgramVariables,
				alwaysStrictAndNonStrictCopies, useStrictInequalitiesAlternatingly);
		mLocations2LiveVariables = new HashMap<>();
		mLoc2PatternSetting = new HashMap<>();
	}

	public DynamicPatternSettingsStrategy(final AbstractTemplateIncreasingDimensionsStrategy dimensionsStrat, final int maxRounds, final Set<IProgramVar> allProgramVariables, final Map<IcfgLocation, Set<IProgramVar>> loc2LiveVariables,
			final boolean alwaysStrictAndNonStrictCopies, final boolean useStrictInequalitiesAlternatingly) {
		super(dimensionsStrat, maxRounds, allProgramVariables,
				alwaysStrictAndNonStrictCopies, useStrictInequalitiesAlternatingly);
		mLocations2LiveVariables = loc2LiveVariables;
		if (loc2LiveVariables == null) {
			mLocations2LiveVariables = new HashMap<>();
		}
		mLoc2PatternSetting = new HashMap<>();
	}

	protected Set<IProgramVar> getPatternVariablesInitially (final IcfgLocation loc) {
		if (mLocations2LiveVariables.containsKey(loc)) {
			return new HashSet<>(mLocations2LiveVariables.get(loc));
		} else {
			return new HashSet<>(mAllProgramVariables);
		}
	}

	protected Dnf<AbstractLinearInvariantPattern> constructInvariantPatternForSetting(final IcfgLocation location,
			final PatternSetting ps, final Script solver, final String prefix) {
		assert super.mLoc2PatternCoefficents != null : "Map mLoc2PatternCoefficents must not be null!";
		final Set<Term> patternCoefficients = new HashSet<>();
		// Build invariant pattern
		final Dnf<AbstractLinearInvariantPattern> disjunction = new Dnf<>(ps.mNumOfDisjuncts);
		for (int i = 0; i < ps.mNumOfDisjuncts; i++) {
			final Collection<AbstractLinearInvariantPattern> conjunction = new ArrayList<>(
					ps.mNumOfConjuncts);
			for (int j = 0; j < ps.mNumOfConjuncts; j++) {
				boolean[] invariantPatternCopies = new boolean[] { false };
				if (super.mUseStrictInequalitiesAlternatingly) {
					// if it is an odd conjunct, then construct a strict inequality
					if (j % 2 == 1) {
						invariantPatternCopies = new boolean[] { true };
					}
				}
				if (mAlwaysStrictAndNonStrictCopies) {
					invariantPatternCopies = new boolean[] { false, true };
				}
				for (final boolean strict : invariantPatternCopies) {
					final LinearPatternBase inequality = new LinearPatternBase (
							solver, ps.getPatternVariables(), prefix + "_" + newPrefix(), strict);
					conjunction.add(inequality);
					// Add the coefficients of the inequality to our set of pattern coefficients
					patternCoefficients.addAll(inequality.getCoefficients());
				}
			}
			disjunction.add(conjunction);
		}
		super.mLoc2PatternCoefficents.put(location, patternCoefficients);
		return disjunction;
	}

	@Override
	public Dnf<AbstractLinearInvariantPattern> getInvariantPatternForLocation(final IcfgLocation location,
			final int round, final Script solver, final String prefix) {
		PatternSetting ps;
		if (!mLoc2PatternSetting.containsKey(location)) {
			// Create new setting for this location
			final Set<IProgramVar> varsForThisPattern = getPatternVariablesInitially(location);
			ps = new PatternSetting(super.mDimensionsStrategy.getInitialDisjuncts(), super.mDimensionsStrategy.getInitialConjuncts(), varsForThisPattern);
			mLoc2PatternSetting.put(location, ps);
		} else {
			ps = mLoc2PatternSetting.get(location);
		}
		return constructInvariantPatternForSetting(location, ps, solver, prefix);
	}

	@Override
	public Dnf<AbstractLinearInvariantPattern> getInvariantPatternForLocation(final IcfgLocation location,
			final int round, final Script solver, final String prefix, final Set<IProgramVar> varsFromUnsatCore) {
		PatternSetting ps;
		if (!mLoc2PatternSetting.containsKey(location)) {
			// Create new setting for this location
			final Set<IProgramVar> varsForThisPattern = getPatternVariablesInitially(location);
			if (!varsFromUnsatCore.isEmpty() && varsForThisPattern.containsAll(varsFromUnsatCore)) {
				// If the current set of variables is a superset of the set of variables from the unsat core, then we remove the residual variables.
				varsForThisPattern.retainAll(varsFromUnsatCore);
			}
			final int[] dimension = super.mDimensionsStrategy.getDimensions(location, round);
			ps = new PatternSetting(dimension[0], dimension[1], varsForThisPattern);
			mLoc2PatternSetting.put(location, ps);
		} else {
			ps = mLoc2PatternSetting.get(location);
			if (ps.getPatternVariables().containsAll(varsFromUnsatCore)) { // TODO: is not empty
				ps.getPatternVariables().retainAll(varsFromUnsatCore);
			}
			if (mLocations2LiveVariables.containsKey(location)) {
				final Set<IProgramVar> liveVars = mLocations2LiveVariables.get(location);
				// Add those variables from unsat core to pattern which are also live.
				for (final IProgramVar var : varsFromUnsatCore ) {
					if (liveVars.contains(var)) {
						ps.getPatternVariables().add(var);
					}
				}
			} else {
				ps.getPatternVariables().addAll(varsFromUnsatCore);
			}
		}
		return constructInvariantPatternForSetting(location, ps, solver, prefix);
	}

	@Override
	public Set<IProgramVar> getPatternVariablesForLocation(final IcfgLocation location, final int round) {
		if (mLoc2PatternSetting.containsKey(location)) {
			return mLoc2PatternSetting.get(location).getPatternVariables();
		} else {
			throw new UnsupportedOperationException("There is no pattern setting for the given location: " + location);
		}
	}

	@Override
	public void changePatternSettingForLocation(final IcfgLocation location, final int round) {
		if (mLoc2PatternSetting.containsKey(location)) {
			mLoc2PatternSetting.get(location).changeSetting(location, round);
		} else {
//			throw new UnsupportedOperationException("There is no pattern setting for the given location: " + location);

		}
	}


	@Override
	public void changePatternSettingForLocation(final IcfgLocation location, final int round, final Set<IcfgLocation> locationsInUnsatCore) {
		// This strategy doesn't care about the set of locations in unsat core.
		changePatternSettingForLocation(location, round);
	}

	class PatternSetting {
		private int mNumOfConjuncts;
//		private static final int MAX_NUM_CONJUNCTS = 3;
		private int mNumOfDisjuncts;
//		private static final int MAX_NUM_DISJUNCTS = 3;
		private final Set<IProgramVar> mPatternVariables;

		public PatternSetting(final int disjuncts, final int conjuncts, final Set<IProgramVar> vars) {
			mNumOfConjuncts = conjuncts;
			mNumOfDisjuncts = disjuncts;
			mPatternVariables = new HashSet<IProgramVar>(vars);
		}

		public Set<IProgramVar> getPatternVariables() {
			return mPatternVariables;
		}

		public void changeSetting(final IcfgLocation location, final int round) {
			final int[] dims = mDimensionsStrategy.getDimensions(location, round + 1);
			mNumOfDisjuncts = dims[0];
			mNumOfConjuncts = dims[1];

//			if (mNumOfConjuncts < 2) {
//				mNumOfConjuncts++;
//			} else if (mNumOfDisjuncts < 2) {
//				mNumOfDisjuncts++;
//			} else {
//				if (mNumOfConjuncts < 4) {
//					mNumOfConjuncts++;
//				} else {
//					mNumOfDisjuncts++;
//					mNumOfConjuncts++;
//				}
//			}
//			if (mNumOfConjuncts < MAX_NUM_CONJUNCTS) {
////				mNumOfDisjuncts = mNumOfConjuncts;
//				mNumOfConjuncts++;
//			} else {
//				if (mNumOfDisjuncts < MAX_NUM_DISJUNCTS) {
//					mNumOfDisjuncts++;
//				} else {
//					throw new UnsupportedOperationException("Both number of conjuncts and disjuncts reached the maximum limit.");
//				}
//			}
		}

		public int getNumOfDisjuncts() {
			return mNumOfDisjuncts;
		}

		public int getNumOfConjuncts() {
			return mNumOfConjuncts;
		}
	}


}
