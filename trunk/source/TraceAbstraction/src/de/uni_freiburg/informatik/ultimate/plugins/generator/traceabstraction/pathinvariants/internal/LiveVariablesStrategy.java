package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

//import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;


/**
 * 
 * @author Betim Musa <musab@informatik.uni-freiburg.de>
 *
 */
public class LiveVariablesStrategy extends LocationDependentLinearInequalityInvariantPatternStrategy {

	private Map<IcfgLocation, Set<IProgramVar>> mLocations2LiveVariables;

	public LiveVariablesStrategy(int baseDisjuncts, int baseConjuncts, int disjunctsPerRound, int conjunctsPerRound,
			int maxRounds, Set<IProgramVar> allProgramVariables, Map<IcfgLocation, Set<IProgramVar>> locs2LiveVariables) {
		super(baseDisjuncts, baseConjuncts, disjunctsPerRound, conjunctsPerRound, maxRounds, allProgramVariables);
		mLocations2LiveVariables = locs2LiveVariables;
	}



	@Override
	public IPredicate applyConfiguration(Collection<Collection<AbstractLinearInvariantPattern>> pattern) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<IProgramVar> getPatternVariablesForLocation(IcfgLocation location, int round) {
		return mLocations2LiveVariables.get(location);
	}

}
