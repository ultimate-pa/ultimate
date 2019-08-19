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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierSequence;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierSequence.QuantifiedVariables;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

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
	private final Stack<Boolean> mOverapproxiamtionStack;
	private boolean mInUsatCoreMode;
	private Set<Term> mAdditionalUnsatCoreContent;

	public QuantifierOverapproximatingSolver(final IUltimateServiceProvider services, final ILogger logger,
			final Script script) {
		mServices = services;
		mLogger = logger;
		mSmtSolver = script;
		mMgdScript = new ManagedScript(services, script);
		mOverapproxiamtionStack = new Stack<Boolean>();
		mOverapproxiamtionStack.push(false);
	}

	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException, SMTLIBException {
		mSmtSolver.setLogic(logic);
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException, SMTLIBException {
		mSmtSolver.setLogic(logic);
	}

	@Override
	public void setOption(final String opt, final Object value) throws UnsupportedOperationException, SMTLIBException {
		if (opt.equals(":produce-unsat-cores")) {
			final Boolean b = (Boolean) value;
			if (b) {
				mInUsatCoreMode = true;
				assert mAdditionalUnsatCoreContent == null;
				mAdditionalUnsatCoreContent = new HashSet<>();
			}
		}
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
		for (int i=0; i<levels; i++) {
			mOverapproxiamtionStack.push(false);
		}
		mSmtSolver.push(levels);
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		// TODO check if there is still an overapproximated term on the assertion stack (optimization)
		for (int i=0; i<levels; i++) {
			mOverapproxiamtionStack.pop();
		}
		mSmtSolver.pop(levels);
	}

	private Term skolemizeOA(final QuantifiedFormula inputFormula) {

		final QuantifierSequence qs = new QuantifierSequence(mMgdScript.getScript(), inputFormula);

		final QuantifiedVariables qb = qs.getQuantifierBlocks().get(0);
		Term newInnerTerm = qs.getInnerTerm();

		for (int block = 0; block < qs.getQuantifierBlocks().size(); block++) {
			final List<QuantifiedVariables> qVar = qs.getQuantifierBlocks();
			if (qVar.get(block).getQuantifier() == QuantifiedFormula.EXISTS && block == 0) {
				final Map<Term, Term> subMap = new HashMap<>();
				for (final TermVariable qtv : qb.getVariables()) {
					final TermVariable ctv = mMgdScript.constructFreshTermVariable("skolemconst", qtv.getSort());
					final Term newConst = SmtUtils.termVariable2constant(mMgdScript.getScript(), ctv, true);
					subMap.put(qtv, newConst);
				}
				newInnerTerm = new Substitution(mMgdScript, subMap).transform(newInnerTerm);
			}
		}
		final Term reAddQuantifiers = qs.prependQuantifierSequence(mMgdScript.getScript(), qs.getQuantifierBlocks(),
				newInnerTerm);
		return reAddQuantifiers;
	}

	private Term overApproximate(final Term term) {
		final Term nnf = new NnfTransformer(mMgdScript, mServices, QuantifierHandling.KEEP, true).transform(term);
		// Optimization 2
		final Term pushed = new QuantifierPusher(mMgdScript, mServices, true, PqeTechniques.ALL_LOCAL).transform(nnf);
		Term qfree = mMgdScript.getScript().term("true");
		for (Term cojunct : SmtUtils.getConjuncts(pushed)) {
			if (!QuantifierUtils.isQuantifierFree(cojunct)) {
				// Optimization 3
				final Term pnfTerm = new PrenexNormalForm(mMgdScript).transform(cojunct);
				if (!QuantifierUtils.isQuantifierFree(pnfTerm)) {
					final Term snfTerm = skolemizeOA((QuantifiedFormula) pnfTerm);
					if (snfTerm instanceof QuantifiedFormula) {
						cojunct = mMgdScript.getScript().term("true");
					} else {
						cojunct = snfTerm;
					}
				}

			}
			qfree = SmtUtils.and(mMgdScript.getScript(), cojunct, qfree);
		}
		return qfree;
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		Term withoutLet = new FormulaUnLet().transform(term);
		if (!QuantifierUtils.isQuantifierFree(withoutLet)) {
			// there is an overapproxiamtion on the current level
			if (mOverapproxiamtionStack.peek() == false) {
				mOverapproxiamtionStack.pop();
				mOverapproxiamtionStack.push(true);
			}
			withoutLet = overApproximate(withoutLet);
		}
		final LBool result = mSmtSolver.assertTerm(withoutLet);
		if (result.equals(LBool.SAT) && wasSomeAssertedTermOverapproximated()) {
			return LBool.UNKNOWN;
		}
		return result;
	}

	private boolean wasSomeAssertedTermOverapproximated() {
		return mOverapproxiamtionStack.stream().anyMatch(x -> x == true);
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		final LBool result = mSmtSolver.checkSat();
		if (result.equals(LBool.SAT) && wasSomeAssertedTermOverapproximated()) {
			return LBool.UNKNOWN;
		}
		if (mInUsatCoreMode && result.equals(LBool.UNSAT)) {
			final Term[] uc = getUnsatCore();
			mAdditionalUnsatCoreContent.addAll(Arrays.asList(uc));
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

	public boolean isInUsatCoreMode() {
		return mInUsatCoreMode;
	}

	public Set<Term> getAdditionalUnsatCoreContent() {
		return mAdditionalUnsatCoreContent;
	}



}