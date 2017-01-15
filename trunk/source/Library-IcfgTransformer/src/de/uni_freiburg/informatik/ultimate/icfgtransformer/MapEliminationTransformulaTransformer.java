package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class MapEliminationTransformulaTransformer implements ITransformulaTransformer<ModifiableTransFormula> {
	private final ModifiableTransFormula mResult;

	public MapEliminationTransformulaTransformer(final TransFormula transformula,
			final MapEliminatorIcfg mapEliminator) {
		mResult = mapEliminator.transform(transformula);
	}

	@Override
	public ModifiableTransFormula getTransformationResult() {
		return mResult;
	}

	@Override
	public String getName() {
		return getClass().getSimpleName();
	}

}
