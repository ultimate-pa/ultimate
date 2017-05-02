package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import java.util.Collections;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonConjunction;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class FastUPRFormulaBuilder {

	private final FastUPRUtils mUtils;
	private final ManagedScript mManagedScript;

	public FastUPRFormulaBuilder(FastUPRUtils utils, ManagedScript mgdScript) {
		mUtils = utils;
		mManagedScript = mgdScript;
	}

	public UnmodifiableTransFormula buildTransFormula(Term term, Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars) {
		final ModifiableTransFormula modFormula = new ModifiableTransFormula(term);
		for (final IProgramVar p : inVars.keySet()) {
			modFormula.addInVar(p, inVars.get(p));
		}
		for (final IProgramVar p : outVars.keySet()) {
			modFormula.addOutVar(p, outVars.get(p));
		}
		return TransFormulaBuilder.constructCopy(mManagedScript, modFormula, Collections.emptySet(),
				Collections.emptySet(), Collections.emptyMap());
	}

	public UnmodifiableTransFormula buildTransFormula(OctagonConjunction toCheck, Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars) {
		return buildTransFormula(toCheck.toTerm(mManagedScript.getScript()), inVars, outVars);
	}

	public UnmodifiableTransFormula buildConsistencyFormula(OctagonConjunction mConjunc, int count,
			Map<IProgramVar, TermVariable> inVars, Map<IProgramVar, TermVariable> outVars) {
		return null;
	}

}
