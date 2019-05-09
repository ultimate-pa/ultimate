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
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

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
	
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final Script mSmtSolver;
	private final ManagedScript mMgdScript;
	
	public UltimateEliminator(IUltimateServiceProvider services, ILogger logger, Script script) {
		mServices = services;
		mLogger = logger;
		mSmtSolver = script;
		mMgdScript = new ManagedScript(services, script);
		
	}

	public void setLogic(String logic) throws UnsupportedOperationException, SMTLIBException {
		mSmtSolver.setLogic(logic);
	}

	public void setLogic(Logics logic) throws UnsupportedOperationException, SMTLIBException {
		mSmtSolver.setLogic(logic);
	}

	public void setOption(String opt, Object value) throws UnsupportedOperationException, SMTLIBException {
		mSmtSolver.setOption(opt, value);
	}

	public void setInfo(String info, Object value) {
		mSmtSolver.setInfo(info, value);
	}

	public void declareSort(String sort, int arity) throws SMTLIBException {
		mSmtSolver.declareSort(sort, arity);
	}

	public void defineSort(String sort, Sort[] sortParams, Sort definition) throws SMTLIBException {
		mSmtSolver.defineSort(sort, sortParams, definition);
	}

	public void declareFun(String fun, Sort[] paramSorts, Sort resultSort) throws SMTLIBException {
		mSmtSolver.declareFun(fun, paramSorts, resultSort);
	}

	public void defineFun(String fun, TermVariable[] params, Sort resultSort, Term definition) throws SMTLIBException {
		mSmtSolver.defineFun(fun, params, resultSort, definition);
	}

	public void push(int levels) throws SMTLIBException {
		mSmtSolver.push(levels);
	}

	public void pop(int levels) throws SMTLIBException {
		mSmtSolver.pop(levels);
	}

	public LBool assertTerm(Term term) throws SMTLIBException {
		final Term lessQuantifier = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScript, term,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		return mSmtSolver.assertTerm(lessQuantifier);
	}

	public LBool checkSat() throws SMTLIBException {
		return mSmtSolver.checkSat();
	}

	public LBool checkSatAssuming(Term... assumptions) throws SMTLIBException {
		return mSmtSolver.checkSatAssuming(assumptions);
	}

	public Term[] getAssertions() throws SMTLIBException {
		return mSmtSolver.getAssertions();
	}

	public Term getProof() throws SMTLIBException, UnsupportedOperationException {
		return mSmtSolver.getProof();
	}

	public Term[] getUnsatCore() throws SMTLIBException, UnsupportedOperationException {
		return mSmtSolver.getUnsatCore();
	}

	public Term[] getUnsatAssumptions() throws SMTLIBException, UnsupportedOperationException {
		return mSmtSolver.getUnsatAssumptions();
	}

	public Map<Term, Term> getValue(Term[] terms) throws SMTLIBException, UnsupportedOperationException {
		return mSmtSolver.getValue(terms);
	}

	public Assignments getAssignment() throws SMTLIBException, UnsupportedOperationException {
		return mSmtSolver.getAssignment();
	}

	public Object getOption(String opt) throws UnsupportedOperationException {
		return mSmtSolver.getOption(opt);
	}

	public Object getInfo(String info) throws UnsupportedOperationException, SMTLIBException {
		return mSmtSolver.getInfo(info);
	}

	public void exit() {
		mSmtSolver.exit();
	}

	public Sort sort(String sortname, Sort... params) throws SMTLIBException {
		return mSmtSolver.sort(sortname, params);
	}

	public Sort sort(String sortname, BigInteger[] indices, Sort... params) throws SMTLIBException {
		return mSmtSolver.sort(sortname, indices, params);
	}

	public Sort[] sortVariables(String... names) throws SMTLIBException {
		return mSmtSolver.sortVariables(names);
	}

	public Term term(String funcname, Term... params) throws SMTLIBException {
		return mSmtSolver.term(funcname, params);
	}

	public Term term(String funcname, BigInteger[] indices, Sort returnSort, Term... params) throws SMTLIBException {
		return mSmtSolver.term(funcname, indices, returnSort, params);
	}

	public TermVariable variable(String varname, Sort sort) throws SMTLIBException {
		return mSmtSolver.variable(varname, sort);
	}

	public Term quantifier(int quantor, TermVariable[] vars, Term body, Term[]... patterns) throws SMTLIBException {
		return mSmtSolver.quantifier(quantor, vars, body, patterns);
	}

	public Term let(TermVariable[] vars, Term[] values, Term body) throws SMTLIBException {
		return mSmtSolver.let(vars, values, body);
	}

	public Term annotate(Term t, Annotation... annotations) throws SMTLIBException {
		return mSmtSolver.annotate(t, annotations);
	}

	public Term numeral(String num) throws SMTLIBException {
		return mSmtSolver.numeral(num);
	}

	public Term numeral(BigInteger num) throws SMTLIBException {
		return mSmtSolver.numeral(num);
	}

	public Term decimal(String decimal) throws SMTLIBException {
		return mSmtSolver.decimal(decimal);
	}

	public Term decimal(BigDecimal decimal) throws SMTLIBException {
		return mSmtSolver.decimal(decimal);
	}

	public Term hexadecimal(String hex) throws SMTLIBException {
		return mSmtSolver.hexadecimal(hex);
	}

	public Term binary(String bin) throws SMTLIBException {
		return mSmtSolver.binary(bin);
	}

	public Term string(String str) throws SMTLIBException {
		return mSmtSolver.string(str);
	}

	public Term simplify(Term term) throws SMTLIBException {
		return mSmtSolver.simplify(term);
	}

	public void reset() {
		mSmtSolver.reset();
	}

	public void resetAssertions() {
		mSmtSolver.resetAssertions();
	}

	public Term[] getInterpolants(Term[] partition) throws SMTLIBException, UnsupportedOperationException {
		return mSmtSolver.getInterpolants(partition);
	}

	public Term[] getInterpolants(Term[] partition, int[] startOfSubtree)
			throws SMTLIBException, UnsupportedOperationException {
		return mSmtSolver.getInterpolants(partition, startOfSubtree);
	}

	public Model getModel() throws SMTLIBException, UnsupportedOperationException {
		return mSmtSolver.getModel();
	}

	public Iterable<Term[]> checkAllsat(Term[] predicates) throws SMTLIBException, UnsupportedOperationException {
		return mSmtSolver.checkAllsat(predicates);
	}

	public Term[] findImpliedEquality(Term[] x, Term[] y) {
		return mSmtSolver.findImpliedEquality(x, y);
	}

	public QuotedObject echo(QuotedObject msg) {
		return mSmtSolver.echo(msg);
	}
	

}
