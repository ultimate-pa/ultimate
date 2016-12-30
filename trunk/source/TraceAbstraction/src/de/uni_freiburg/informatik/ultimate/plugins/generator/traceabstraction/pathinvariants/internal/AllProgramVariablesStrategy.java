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
	
//	private final Collection<Term> mPatternCoefficients;

	public AllProgramVariablesStrategy(int baseDisjuncts, int baseConjuncts, int disjunctsPerRound,
			int conjunctsPerRound, int maxRounds, Set<IProgramVar> allProgramVariables, Set<IProgramVar> patternVariables) {
		super(baseDisjuncts, baseConjuncts, disjunctsPerRound, conjunctsPerRound, maxRounds, allProgramVariables, patternVariables);
//		mPatternCoefficients = new ArrayList<>();
	}



	@Override
	public IPredicate applyConfiguration(Collection<Collection<AbstractLinearInvariantPattern>> pattern) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<IProgramVar> getPatternVariablesForLocation(IcfgLocation location, int round) {
		return mAllProgramVariables;
	}

}
