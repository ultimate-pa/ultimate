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

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Map;
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
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;

/**
 * SMT solver for logics with quantifiers. Passes all SMT command to a back end
 * SMT solver, but tries to transform asserted terms to quantifier-free terms
 * before passing them to the back end SMT solver.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Max Barth (Max.Barth95@gmx.de)
 *
 */
public class UltimateEliminator implements Script {

	private static final boolean WRAP_BACKEND_SOLVER_WITH_QUANTIFIER_OVERAPPROXIMATION = true;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final Script mSmtSolver;
	private final ManagedScript mMgdScript;
	private LBool mExpectedResult;
	private long mTreeSizeOfAssertedTerms = 0;

	public UltimateEliminator(final IUltimateServiceProvider services, final ILogger logger, final Script script) {
		mServices = services;
		mLogger = logger;
		if (WRAP_BACKEND_SOLVER_WITH_QUANTIFIER_OVERAPPROXIMATION) {
			mSmtSolver = new QuantifierOverapproximatingSolver(services, logger, script);
		} else {
			mSmtSolver = script;
		}
		mMgdScript = new ManagedScript(services, mSmtSolver);

	}

	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException, SMTLIBException {
		// do not pass the original logic but the corresponding quantifier-free logic
		if (logic.startsWith("QF_")) {
			mSmtSolver.setLogic(logic);
		} else if (WRAP_BACKEND_SOLVER_WITH_QUANTIFIER_OVERAPPROXIMATION) {
			final String qFLogic = "QF_" + logic;
			if (Logics.valueOf(qFLogic) != null) {
				mSmtSolver.setLogic(qFLogic);
			} else {
				throw new AssertionError("No Quantifier Free Logic found for Overapproximation");
			}
		} else {
			mSmtSolver.setLogic(logic);
		}
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException, SMTLIBException {
		if (logic.isQuantified() && WRAP_BACKEND_SOLVER_WITH_QUANTIFIER_OVERAPPROXIMATION) {
			final Logics qFLogic = Logics.valueOf("QF_" + logic.toString());
			mSmtSolver.setLogic(qFLogic);
		} else {
			mSmtSolver.setLogic(logic);
		}
	}

	@Override
	public void setOption(final String opt, final Object value) throws UnsupportedOperationException, SMTLIBException {
		mSmtSolver.setOption(opt, value);
	}

	@Override
	public void setInfo(final String info, final Object value) {
		if (info.equals(":status")) {
			final String valueAsString = (String) value;
			mExpectedResult = LBool.valueOf(valueAsString.toUpperCase());
		} else {
			mSmtSolver.setInfo(info, value);
		}
	}

	@Override
	public void declareSort(final String sort, final int arity) throws SMTLIBException {
		mSmtSolver.declareSort(sort, arity);
	}

	@Override
	public void defineSort(final String sort, final Sort[] sortParams, final Sort definition) throws SMTLIBException {
		mSmtSolver.defineSort(sort, sortParams, definition);
	}

	@Override
	public void declareFun(final String fun, final Sort[] paramSorts, final Sort resultSort) throws SMTLIBException {
		mSmtSolver.declareFun(fun, paramSorts, resultSort);
	}

	@Override
	public void defineFun(final String fun, final TermVariable[] params, final Sort resultSort, final Term definition)
			throws SMTLIBException {
		if (!QuantifierUtils.isQuantifierFree(definition)) {
			throw new UnsupportedOperationException(
					"Cannot handle define-fun with quantified definition " + definition);
		}
		mSmtSolver.defineFun(fun, params, resultSort, definition);
	}

	@Override
	public void push(final int levels) throws SMTLIBException {
		mSmtSolver.push(levels);
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		mSmtSolver.pop(levels);
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		final NamedTermWrapper ntw = new NamedTermWrapper(term);
		if (ntw.isIsNamed()) {
			// we alredy removed quantifiers
			mTreeSizeOfAssertedTerms += new DAGSize().treesize(ntw.getUnnamedTerm());
			return mSmtSolver.assertTerm(term);
		} else {
			final Term hopfullyQuantifierFree = makeQuantifierFree(ntw.getUnnamedTerm());
			mTreeSizeOfAssertedTerms += new DAGSize().treesize(hopfullyQuantifierFree);
			return mSmtSolver.assertTerm(hopfullyQuantifierFree);
		}
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
		final LBool result = mSmtSolver.checkSat();
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
	public LBool checkSatAssuming(final Term... assumptions) throws SMTLIBException {
		return mSmtSolver.checkSatAssuming(assumptions);
	}

	@Override
	public Term[] getAssertions() throws SMTLIBException {
		return mSmtSolver.getAssertions();
	}

	@Override
	public Term getProof() throws SMTLIBException, UnsupportedOperationException {
		return mSmtSolver.getProof();
	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException, UnsupportedOperationException {
		if (WRAP_BACKEND_SOLVER_WITH_QUANTIFIER_OVERAPPROXIMATION) {
			final QuantifierOverapproximatingSolver qos = (QuantifierOverapproximatingSolver) mSmtSolver;
			assert qos.isInUsatCoreMode();
			final Term[] uc = mSmtSolver.getUnsatCore();
			final Set<Term> result = new HashSet<>();
			result.addAll(qos.getAdditionalUnsatCoreContent());
			result.addAll(Arrays.asList(uc));
			return result.toArray(new Term[result.size()]);
		} else {
			throw new AssertionError("Unsat-core only available in combination with QuantifierOverapproximatingSolver");
		}
	}

	@Override
	public Term[] getUnsatAssumptions() throws SMTLIBException, UnsupportedOperationException {
		return mSmtSolver.getUnsatAssumptions();
	}

	@Override
	public Map<Term, Term> getValue(final Term[] terms) throws SMTLIBException, UnsupportedOperationException {
		return mSmtSolver.getValue(terms);
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException, UnsupportedOperationException {
		return mSmtSolver.getAssignment();
	}

	@Override
	public Object getOption(final String opt) throws UnsupportedOperationException {
		return mSmtSolver.getOption(opt);
	}

	@Override
	public Object getInfo(final String info) throws UnsupportedOperationException, SMTLIBException {
		return mSmtSolver.getInfo(info);
	}

	@Override
	public void exit() {
		// mSmtSolver.exit();
	}

	@Override
	public Sort sort(final String sortname, final Sort... params) throws SMTLIBException {
		return mSmtSolver.sort(sortname, params);
	}

	@Override
	public Sort sort(final String sortname, final BigInteger[] indices, final Sort... params) throws SMTLIBException {
		return mSmtSolver.sort(sortname, indices, params);
	}

	@Override
	public Sort[] sortVariables(final String... names) throws SMTLIBException {
		return mSmtSolver.sortVariables(names);
	}

	@Override
	public Term term(final String funcname, final Term... params) throws SMTLIBException {
		return mSmtSolver.term(funcname, params);
	}

	@Override
	public Term term(final String funcname, final BigInteger[] indices, final Sort returnSort, final Term... params)
			throws SMTLIBException {
		return mSmtSolver.term(funcname, indices, returnSort, params);
	}

	@Override
	public TermVariable variable(final String varname, final Sort sort) throws SMTLIBException {
		return mSmtSolver.variable(varname, sort);
	}

	@Override
	public Term quantifier(final int quantor, final TermVariable[] vars, final Term body, final Term[]... patterns)
			throws SMTLIBException {
		return mSmtSolver.quantifier(quantor, vars, body, patterns);
	}

	@Override
	public Term let(final TermVariable[] vars, final Term[] values, final Term body) throws SMTLIBException {
		return mSmtSolver.let(vars, values, body);
	}

	@Override
	public Term annotate(final Term t, final Annotation... annotations) throws SMTLIBException {
		if (Arrays.stream(annotations).anyMatch(x -> x.getKey().equals(":named"))) {
			final Term hopfullyQuantifierFree = makeQuantifierFree(t);
			return mSmtSolver.annotate(hopfullyQuantifierFree, annotations);
		} else {
			return mSmtSolver.annotate(t, annotations);
		}
	}

	@Override
	public Term numeral(final String num) throws SMTLIBException {
		return mSmtSolver.numeral(num);
	}

	@Override
	public Term numeral(final BigInteger num) throws SMTLIBException {
		return mSmtSolver.numeral(num);
	}

	@Override
	public Term decimal(final String decimal) throws SMTLIBException {
		return mSmtSolver.decimal(decimal);
	}

	@Override
	public Term decimal(final BigDecimal decimal) throws SMTLIBException {
		return mSmtSolver.decimal(decimal);
	}

	@Override
	public Term hexadecimal(final String hex) throws SMTLIBException {
		return mSmtSolver.hexadecimal(hex);
	}

	@Override
	public Term binary(final String bin) throws SMTLIBException {
		return mSmtSolver.binary(bin);
	}

	@Override
	public Term string(final String str) throws SMTLIBException {
		return mSmtSolver.string(str);
	}

	@Override
	public Term simplify(final Term term) throws SMTLIBException {
		return mSmtSolver.simplify(term);
	}

	@Override
	public void reset() {
		mSmtSolver.reset();
	}

	@Override
	public void resetAssertions() {
		mSmtSolver.resetAssertions();
	}

	@Override
	public Term[] getInterpolants(final Term[] partition) throws SMTLIBException, UnsupportedOperationException {
		return mSmtSolver.getInterpolants(partition);
	}

	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree)
			throws SMTLIBException, UnsupportedOperationException {
		return mSmtSolver.getInterpolants(partition, startOfSubtree);
	}

	@Override
	public Model getModel() throws SMTLIBException, UnsupportedOperationException {
		return mSmtSolver.getModel();
	}

	@Override
	public Iterable<Term[]> checkAllsat(final Term[] predicates) throws SMTLIBException, UnsupportedOperationException {
		return mSmtSolver.checkAllsat(predicates);
	}

	@Override
	public Term[] findImpliedEquality(final Term[] x, final Term[] y) {
		return mSmtSolver.findImpliedEquality(x, y);
	}

	@Override
	public QuotedObject echo(final QuotedObject msg) {
		return mSmtSolver.echo(msg);
	}

}
