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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * Wrapper for an SMT solver that makes sure that the solver does not have to
 * deal with quantifiers. The idea of this class is that we overapproximate
 * asserted formulas if they contain quantifiers (e.g., we replace the formula
 * by "true"). If the SMT solver responds with 'sat' to a check-sat command we
 * return unknown if we overapproximated an asserted formula. If we did not
 * overapproximate or if the response was 'unsat' we may pass the response of
 * the solver.
 *
 * TODO As an optimization we may also try very inexpensive quantifier
 * elimination techniques or skolemization. TODO list these once these are
 * implemented
 *
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Max Barth (Max.Barth95@gmx.de)
 *
 */
public class QuantifierOverapproximatingSolver implements Script {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final Script mSmtSolver;
	private final ManagedScript mMgdScript;
	private LBool mExpectedResult;
	private Boolean mOverAprox;

	public QuantifierOverapproximatingSolver(final IUltimateServiceProvider services, final ILogger logger,
			final Script script) {
		mServices = services;
		mLogger = logger;
		mSmtSolver = script;
		mMgdScript = new ManagedScript(services, script);
		mOverAprox = false;

	}

	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException, SMTLIBException {
		// do not pass the original logic but the corresponding quantifier-free logic
		if (logic.startsWith("QF_")) {
			mSmtSolver.setLogic(logic);
		} else {
			final String qFLogic = "QF_" + logic.toString();
			if (Logics.valueOf(qFLogic) != null) {
				mSmtSolver.setLogic(qFLogic);
			} else {
				throw new AssertionError("No Quantifier Free Logic found for Overapproximation");
			}

		}
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException, SMTLIBException {
		if (logic.isQuantified()) {
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
		mSmtSolver.setInfo(info, value);
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
		mSmtSolver.defineFun(fun, params, resultSort, definition);
	}

	@Override
	public void push(final int levels) throws SMTLIBException {
		mSmtSolver.push(levels);
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		// TODO check if there is still an overapproximated term on the assertion stack
		mSmtSolver.pop(levels);
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		// TODO do overapproximation if necessary
		if (term instanceof QuantifiedFormula) {
			mOverAprox = true;
		}
		return mSmtSolver.assertTerm(term);
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		final LBool result = mSmtSolver.checkSat();
		if (result.equals(LBool.SAT) && mOverAprox) {
			return LBool.UNKNOWN;
		}
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
		return mSmtSolver.getUnsatCore();
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
		mSmtSolver.exit();
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
		return mSmtSolver.annotate(t, annotations);
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
