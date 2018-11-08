package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis;

import java.util.Collection;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
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

	/**
	 * added by Alexander Nutz in order to comply with the updated interface, crashes
	 */
	@Override
	public IEqualityProvidingState getEqualityProvidingStateForLocationSet(
			final Set<IcfgLocation> arrayGroupAccessLocations) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void announceAdditionalLiterals(final Collection<IProgramConst> collection) {
		throw new UnsupportedOperationException("do we need to implement this?");
	}

	@Override
	public IEqualityProvidingIntermediateState getEqualityProvidingIntermediateState(final IcfgEdge edge) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void setTrackedArrays(final List<String> trackedArrays) {
		throw new UnsupportedOperationException("do we need to implement this?");
	}

}
