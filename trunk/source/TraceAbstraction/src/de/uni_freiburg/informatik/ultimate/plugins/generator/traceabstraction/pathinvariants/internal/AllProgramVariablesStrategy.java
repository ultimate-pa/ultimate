package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * For each location each inequality pattern contains all program variables.
 * @author Betim Musa <musab@informatik.uni-freiburg.de>
 *
 */
public class AllProgramVariablesStrategy extends LocationIndependentLinearInequalityInvariantPatternStrategy {
	
	private final Collection<Term> mPatternCoefficients;

	public AllProgramVariablesStrategy(int baseDisjuncts, int baseConjuncts, int disjunctsPerRound,
			int conjunctsPerRound, int maxRounds, Set<IProgramVar> allProgramVariables, Set<IProgramVar> patternVariables) {
		super(baseDisjuncts, baseConjuncts, disjunctsPerRound, conjunctsPerRound, maxRounds, allProgramVariables, patternVariables);
		mPatternCoefficients = new ArrayList<>();
	}

	@Override
	public Collection<Collection<LinearPatternBase>> getInvariantPatternForLocation(IcfgLocation location, int round, Script solver, String prefix) {
			final int[] dimensions = getDimensions(location, round);
			// Build invariant pattern
			final Collection<Collection<LinearPatternBase>> disjunction = new ArrayList<>(dimensions[0]);
			for (int i = 0; i < dimensions[0]; i++) {
				final Collection<LinearPatternBase> conjunction = new ArrayList<>(
						dimensions[1]);
				for (int j = 0; j < dimensions[1]; j++) {
					final boolean[] invariantPatternCopies;
//					if (mAlwaysStrictAndNonStrictCopies ) {
//						invariantPatternCopies = new boolean[] { false, true }; 
//					} else {
						invariantPatternCopies = new boolean[] { false };
//					}
					for (final boolean strict : invariantPatternCopies) {
						final LinearPatternBase inequality = new LinearPatternBase (
								solver, mAllProgramVariables, prefix, strict);
						Collection<Term> params = inequality.getVariables();
						mPatternCoefficients.addAll(params);
						conjunction.add(inequality);
					}
				}
				disjunction.add(conjunction);
			}
			return disjunction;
	}

	@Override
	public IPredicate applyConfiguration(Collection<Collection<LinearPatternBase>> pattern) {
		// TODO Auto-generated method stub
		return null;
	}

}
