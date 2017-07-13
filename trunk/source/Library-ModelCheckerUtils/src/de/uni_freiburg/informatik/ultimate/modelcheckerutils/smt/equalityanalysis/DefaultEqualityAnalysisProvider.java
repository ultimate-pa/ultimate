package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;

/**
 * Default implementation of {@link IEqualityAnalysisResultProvider}, simply always returns "unknown" as result.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class DefaultEqualityAnalysisProvider<LOC, CFG> implements IEqualityAnalysisResultProvider<LOC, CFG> {

	@Override
	public EqualityAnalysisResult getAnalysisResult(final LOC location, final Set<Doubleton<Term>> doubletons) {
		return new EqualityAnalysisResult(doubletons);
	}

	@Override
	public void preprocess(final CFG cfg) {
		// No preprocessing necessary, "unknown" is always returned
	}

	@Override
	public IEqualityProvidingState getEqualityProvidingStateForLocationSet(
			Set<IcfgLocation> arrayGroupAccessLocations) {
		// TODO Auto-generated method stub
		return null;
	}
}
