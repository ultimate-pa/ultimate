package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class Tools{
	
	private Tools() {
	    throw new IllegalStateException("Utility class");
	  }

	public static <T> Deque<T> cloneDeque(final Deque<T> deque) {
		final Deque<T> clone = new ArrayDeque<>();
		for (final T item : deque) {
			clone.add(item);
		}
		return clone;
	}
	
	public static UnmodifiableTransFormula negateUnmodifiableTransFormula(final ManagedScript mMgScript, final UnmodifiableTransFormula unmodifiableTransFormula){
		final TransFormulaBuilder tfb = new TransFormulaBuilder(unmodifiableTransFormula.getInVars(), 
				unmodifiableTransFormula.getOutVars(), false, unmodifiableTransFormula.getNonTheoryConsts(), 
				false, unmodifiableTransFormula.getBranchEncoders(), true);
		tfb.setFormula(mMgScript.getScript().term("not", unmodifiableTransFormula.getFormula()));
		tfb.setInfeasibility(unmodifiableTransFormula.isInfeasible());
		tfb.finishConstruction(mMgScript);
		return tfb.finishConstruction(mMgScript);
	}
}
