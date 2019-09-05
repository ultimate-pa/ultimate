/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierSequence;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms.UnfTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;

/**
 * SMT solver for logics with quantifiers. Passes all SMT command to a back end SMT solver, but tries to transform
 * asserted terms to quantifier-free terms before passing them to the back end SMT solver.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Max Barth (Max.Barth95@gmx.de)
 *
 */
public class UltimateEliminator extends WrapperScript {

	private static final boolean WRAP_BACKEND_SOLVER_WITH_QUANTIFIER_OVERAPPROXIMATION = true;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mMgdScript;
	private LBool mExpectedResult;
	private long mTreeSizeOfAssertedTerms = 0;

	public UltimateEliminator(final IUltimateServiceProvider services, final ILogger logger, final Script script) {
		super(wrapIfNecessary(services, logger, script));
		mServices = services;
		mLogger = logger;
		mMgdScript = new ManagedScript(services, mScript);

	}

	private static Script wrapIfNecessary(final IUltimateServiceProvider services, final ILogger logger,
			final Script script) {
		if (WRAP_BACKEND_SOLVER_WITH_QUANTIFIER_OVERAPPROXIMATION) {
			return new QuantifierOverapproximatingSolver(services, logger, script);
		}
		return script;
	}

	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException, SMTLIBException {
		// do not pass the original logic but the corresponding quantifier-free logic
		if (logic.startsWith("QF_")) {
			mScript.setLogic(logic);
		} else if (WRAP_BACKEND_SOLVER_WITH_QUANTIFIER_OVERAPPROXIMATION) {
			final String qFLogic = "QF_" + logic;
			if (Logics.valueOf(qFLogic) != null) {
				mScript.setLogic(qFLogic);
			} else {
				throw new AssertionError("No Quantifier Free Logic found for Overapproximation");
			}
		} else {
			mScript.setLogic(logic);
		}
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException, SMTLIBException {
		if (logic.isQuantified() && WRAP_BACKEND_SOLVER_WITH_QUANTIFIER_OVERAPPROXIMATION) {
			final Logics qFLogic = Logics.valueOf("QF_" + logic.toString());
			mScript.setLogic(qFLogic);
		} else {
			mScript.setLogic(logic);
		}
	}

	@Override
	public void setInfo(final String info, final Object value) {
		if (info.equals(":status")) {
			final String valueAsString = (String) value;
			mExpectedResult = LBool.valueOf(valueAsString.toUpperCase());
		} else {
			mScript.setInfo(info, value);
		}
	}

	@Override
	public void defineFun(final String fun, final TermVariable[] params, final Sort resultSort, final Term definition)
			throws SMTLIBException {
		if (!QuantifierUtils.isQuantifierFree(definition)) {
			throw new UnsupportedOperationException(
					"Cannot handle define-fun with quantified definition " + definition);
		}
		mScript.defineFun(fun, params, resultSort, definition);
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		final NamedTermWrapper ntw = new NamedTermWrapper(term);
		if (ntw.isIsNamed()) {
			// we alredy removed quantifiers
			mTreeSizeOfAssertedTerms += new DAGSize().treesize(ntw.getUnnamedTerm());
			return mScript.assertTerm(term);
		}
		final Term hopfullyQuantifierFree = makeQuantifierFree(ntw.getUnnamedTerm());
		mTreeSizeOfAssertedTerms += new DAGSize().treesize(hopfullyQuantifierFree);
		return mScript.assertTerm(hopfullyQuantifierFree);
	}

	private Term makeQuantifierFree(final Term term) {
		final Term letFree = new FormulaUnLet().transform(term);
		final Term annotationFree = new AnnotationRemover().transform(letFree);
		final Term unf = new UnfTransformer(mMgdScript.getScript()).transform(annotationFree);
		final Term lessQuantifier = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScript, unf,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final boolean furtherOptimizations = false;
		if (furtherOptimizations) {
			// TODO
		}
		if (!QuantifierUtils.isQuantifierFree(lessQuantifier)) {
			final Term pnf = new PrenexNormalForm(mMgdScript).transform(lessQuantifier);
			final QuantifierSequence qs = new QuantifierSequence(mMgdScript.getScript(), pnf);
			throw new AssertionError("Result of partial quantifier elimination is not quantifier-free but an "
					+ qs.buildQuantifierSequenceStringRepresentation() + " term.");
		}
		return lessQuantifier;
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		final LBool result = mScript.checkSat();
		if (mExpectedResult != null) {
			mLogger.info("Expected result: " + result);
			if (mExpectedResult == LBool.UNKNOWN) {
				if (result != LBool.UNKNOWN) {
					throw new AssertionError("Congratulations! We solved a difficult benchmark");
				}
			} else {
				if (result != LBool.UNKNOWN && result != mExpectedResult) {
					throw new AssertionError("Result incorrect: expected " + mExpectedResult + " obtained " + result
							+ ". Treesize of asserted terms " + mTreeSizeOfAssertedTerms);
				}

			}
		}
		mLogger.info("Computed result: " + result);
		return result;

	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException, UnsupportedOperationException {
		if (WRAP_BACKEND_SOLVER_WITH_QUANTIFIER_OVERAPPROXIMATION) {
			final QuantifierOverapproximatingSolver qos = (QuantifierOverapproximatingSolver) mScript;
			assert qos.isInUsatCoreMode();
			final Term[] uc = mScript.getUnsatCore();
			final Set<Term> result = new HashSet<>();
			result.addAll(qos.getAdditionalUnsatCoreContent());
			result.addAll(Arrays.asList(uc));
			return result.toArray(new Term[result.size()]);
		}
		throw new AssertionError("Unsat-core only available in combination with QuantifierOverapproximatingSolver");
	}

	@Override
	public void exit() {
		// mSmtSolver.exit();
	}

	@Override
	public Term annotate(final Term t, final Annotation... annotations) throws SMTLIBException {
		if (Arrays.stream(annotations).anyMatch(x -> x.getKey().equals(":named"))) {
			final Term hopfullyQuantifierFree = makeQuantifierFree(t);
			return mScript.annotate(hopfullyQuantifierFree, annotations);
		}
		return mScript.annotate(t, annotations);
	}
}
