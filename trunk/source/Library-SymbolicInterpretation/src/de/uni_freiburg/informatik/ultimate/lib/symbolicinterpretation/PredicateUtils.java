/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

public class PredicateUtils {

	private final IIcfg<IcfgLocation> mIcfg;
	private final ManagedScript mScript;
	private final PredicateFactory mFactory;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mTransformer;
	private final IPredicate mTop;
	private final IPredicate mBottom;

	public PredicateUtils(final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg) {
		mIcfg = icfg;
		mScript = icfg.getCfgSmtToolkit().getManagedScript();
		// TODO decide which techniques to use or use a setting
		mFactory = new PredicateFactory(services, mScript, icfg.getCfgSmtToolkit().getSymbolTable(),
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		mTransformer = new PredicateTransformer<>(mScript, new TermDomainOperationProvider(services, mScript));
		mTop = mFactory.newPredicate(mScript.term(this, "true"));
		mBottom = mFactory.newPredicate(mScript.term(this, "false"));
	}

	public ManagedScript getScript() {
		return mScript;
	}
	
	public PredicateFactory getFactory() {
		return mFactory;
	}

	public IPredicate post(final IPredicate input, final IIcfgTransition<IcfgLocation> transition) {
		return mFactory.newPredicate(mTransformer.strongestPostcondition(input, transition.getTransformula()));
	}

	public IPredicate postCall(IPredicate input, final IIcfgCallTransition<IcfgLocation> transition) {
		final CfgSmtToolkit toolkit = mIcfg.getCfgSmtToolkit();
		final String calledProcedure = transition.getSucceedingProcedure();
		return mFactory.newPredicate(mTransformer.strongestPostconditionCall(input,
				transition.getLocalVarsAssignment(),
				toolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(calledProcedure),
				toolkit.getOldVarsAssignmentCache().getOldVarsAssignment(calledProcedure),
				toolkit.getModifiableGlobalsTable().getModifiedBoogieVars(calledProcedure)));
	}

	public IPredicate merge(final IPredicate first, final IPredicate second) {
		// TODO decide whether or not to use simplification or use a setting
		final boolean simplifyDDA = true;
		return mFactory.or(simplifyDDA, first, second);
	}

	public IPredicate top() {
		return mTop;
	}

	public IPredicate bottom() {
		return mBottom;
	}

}
