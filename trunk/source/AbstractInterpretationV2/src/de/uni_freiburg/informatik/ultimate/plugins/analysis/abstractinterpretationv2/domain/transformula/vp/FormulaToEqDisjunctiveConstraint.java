package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqConstraintFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqDisjunctiveConstraint;

/**
 * Helper class to convert formulas into EqDisjunctiveConstraints.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class FormulaToEqDisjunctiveConstraint {

	private final EqConstraintFactory<EqNode> mEqConstraintFactory;
	private final EqNodeAndFunctionFactory mEqNodeAndFunctionFactory;
	private final ManagedScript mMgdScript;
	private final IUltimateServiceProvider mServices;

	public FormulaToEqDisjunctiveConstraint(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit) {
		mServices = services;
		mMgdScript = csToolkit.getManagedScript();

		mEqNodeAndFunctionFactory = new EqNodeAndFunctionFactory(mServices, mMgdScript);
		mEqConstraintFactory = new EqConstraintFactory<>(mEqNodeAndFunctionFactory, services, csToolkit);
	}

	/**
	 * Constructs an EqDisjunctiveConstraint from the given formula.
	 *
	 * @param formula
	 * @return
	 */
	public EqDisjunctiveConstraint<EqNode> convertFormula(final Term formula) {
		final FormulaToEqDisjunctiveConstraintConverter<IcfgEdge> converter =
				new FormulaToEqDisjunctiveConstraintConverter<>(mServices, mMgdScript, mEqConstraintFactory,
						mEqNodeAndFunctionFactory, formula);
		return converter.getResult();
	}
}
