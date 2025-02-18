package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import java.util.ArrayDeque;
import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;

public class Tools {

	private Tools() {
		throw new IllegalStateException("Utility class");
	}

	public static <T> Deque<T> cloneDeque(final Deque<T> deque) {
		final Deque<T> clone = new ArrayDeque<>(deque);
		return clone;
	}

	public static UnmodifiableTransFormula negateUnmodifiableTransFormula(final ManagedScript mMgScript,
			final UnmodifiableTransFormula unmodifiableTransFormula) {
		final TransFormulaBuilder tfb = new TransFormulaBuilder(unmodifiableTransFormula.getInVars(),
				unmodifiableTransFormula.getOutVars(), false, unmodifiableTransFormula.getNonTheoryConsts(), false,
				unmodifiableTransFormula.getBranchEncoders(), true);
		tfb.setFormula(mMgScript.getScript().term("not", unmodifiableTransFormula.getFormula()));
		tfb.setInfeasibility(unmodifiableTransFormula.isInfeasible());
		tfb.finishConstruction(mMgScript);
		return tfb.finishConstruction(mMgScript);
	}
}
