/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TreeAutomizer Plugin.
 *
 * The ULTIMATE TreeAutomizer Plugin is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TreeAutomizer Plugin is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TreeAutomizer Plugin. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TreeAutomizer Plugin, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TreeAutomizer Plugin grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.parsing;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClause;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornUtilConstants;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class HornClauseParserScript extends NoopScript {

	/**
	 * Interface to the SMT solver that TreeAutomizer (or whoever else will used
	 * the HornClauseGraph) will use as a backend.
	 */
	private final ManagedScript mBackendSmtSolver;
	private final String mLogic;
	private final Settings mSolverSettings;
	private final HashSet<String> mDeclaredPredicateSymbols;
	private final List<HornClause> mCurrentHornClause;
	private final ArrayList<Term> mCurrentPredicateAtoms;
	private final ArrayList<Term> mCurrentTransitionAtoms;
	private final HCSymbolTable mSymbolTable;

	public HornClauseParserScript(ManagedScript smtSolverScript, String logic, Settings settings) {
		mBackendSmtSolver = smtSolverScript;
		mLogic = logic;
		mSolverSettings = settings;
		setupBackendSolver();
		mDeclaredPredicateSymbols = new HashSet<>();

		mCurrentHornClause = new ArrayList<>();
		mCurrentPredicateAtoms = new ArrayList<>();
		mCurrentTransitionAtoms = new ArrayList<>();
		
		mSymbolTable = new HCSymbolTable(mBackendSmtSolver);

	}

	public IElement getHornClauses() {
		mSymbolTable.finishConstruction();
		
		final Payload payload = new Payload();
		final HornAnnot annot = new HornAnnot(mCurrentHornClause, mBackendSmtSolver, mSymbolTable);
		payload.getAnnotations().put(HornUtilConstants.HORN_ANNOT_NAME, annot);
		
		return new HornClauseAST(payload);
	}
	
	/**
	 * Make the necessary settings in the background solver, like set-logic etc.
	 * 
	 * @param smtSolverScript
	 */
	private void setupBackendSolver() {

		// mBackendSmtSolver.setLogic(Logics.AUFLIRA); //TODO: do this according
		// to a setting

		// TODO possibly set some options etc.
	}

	@Override
	public void setLogic(String logic) throws UnsupportedOperationException {
		assert logic.equals("HORN") : "Error: the SmtParser-setting HornSolverMode is set, "
				+ "but the smt2 file sets the logic to something other than HORN";
		if (!logic.equals("HORN")) {
			throw new UnsupportedOperationException();
		}

		super.setLogic(mLogic);
	}

	@Override
	public void setLogic(Logics logic) throws UnsupportedOperationException {
		// TODO Auto-generated method stub
		super.setLogic(logic);
	}

	@Override
	public void setOption(String opt, Object value) throws UnsupportedOperationException, SMTLIBException {
		// just handing it over to the backend solver
		super.setOption(opt, value);
		// mBackendSmtSolver.setOption(opt, value);
	}

	@Override
	public void declareSort(String sort, int arity) throws SMTLIBException {
		super.declareSort(sort, arity);
		// mBackendSmtSolver.declareSort(sort, arity);
	}

	@Override
	public void declareFun(String fun, Sort[] paramSorts, Sort resultSort) throws SMTLIBException {
		// TODO: probably track uninterpreted predicates, i.e., the predicates
		// not known
		// to the theory of the backend solver
		// mBackendSmtSolver.declareFun(fun, paramSorts, resultSort);
		super.declareFun(fun, paramSorts, resultSort);
		if (resultSort.getName() == "Bool") {
			mDeclaredPredicateSymbols.add(fun);
		}
	}
	/**
	private String termsToString(Term[] terms) {
		String res = "";
		for (Term term : terms) {
			res += " ( " + term.toString() + " ) ";
		}
		if (res.length() > 0)
			return " { " + res + " } ";
		else
			return res;
	}

	private HornClausePredicateSymbol getHornPredicateSymbol(FunctionSymbol func) {
		if (!predicates.containsKey(func.getName())) {
			predicates.put(func.getName(), new HornClausePredicateSymbol(func.getName(), func.getParameterCount()));
		}
		return predicates.get(func.getName());
	}

	private Map<HornClausePredicateSymbol, ArrayList<TermVariable>> getPredicateSymbols(ApplicationTerm term) {
		HashMap<HornClausePredicateSymbol, ArrayList<TermVariable>> res = new HashMap<>();
		if (mDeclaredPredicateSymbols.contains(term.getFunction().getName())) {
			ArrayList<TermVariable> vars = new ArrayList<TermVariable>();
			for (Term par : term.getParameters()) {
				vars.add((TermVariable) par);
			}

			res.put(getHornPredicateSymbol(term.getFunction()), vars);
		}
		if (term.getFunction().getName().equals("and")) {
			for (Term literal : term.getParameters()) {
				Map<HornClausePredicateSymbol, ArrayList<TermVariable>> temp = getPredicateSymbols(
						(ApplicationTerm) literal);
				for (HornClausePredicateSymbol symbol : temp.keySet()) {
					res.put(symbol, temp.get(symbol));
				}
			}
		}

		if (term.getFunction().getName().equals("or")) {
			for (Term literal : term.getParameters()) {
				Map<HornClausePredicateSymbol, ArrayList<TermVariable>> temp = getPredicateSymbols(
						(ApplicationTerm) literal);
				for (HornClausePredicateSymbol symbol : temp.keySet()) {
					res.put(symbol, temp.get(symbol));
				}
			}
		}
		return res;
	}

	private Term getTransitionFormula(ApplicationTerm term) {
		if (term.getFunction().getName().equals("and")) {
			ArrayList<Term> terms = new ArrayList<>();
			for (Term literal : term.getParameters()) {
				terms.add(getTransitionFormula((ApplicationTerm) literal));
			}
			if (terms.size() > 0)
				return getTheory().and(terms.toArray(new Term[] {}));
			else
				return getTheory().mTrue;
		}
		if (!predicates.containsKey(term.getFunction().getName())) {
			return term;
		}
		return getTheory().mTrue;
	}
	*/

	private Cobody parseCobody(Term term) throws SMTLIBException {
		final ApplicationTerm t = (ApplicationTerm) term;

		if (t.getFunction().getName().equals("and")) {
			// t = And (y1 y2 ... yn)
			final Cobody tail = new Cobody();
			for (final Term literal : t.getParameters()) {
				final ApplicationTerm par = (ApplicationTerm) literal;
				if (mDeclaredPredicateSymbols.contains(par.getFunction().getName())) {
					//yi = I
					tail.addPredicate(par);
				} else if (par.getFunction().getName().equals("not") && mDeclaredPredicateSymbols
						.contains(((ApplicationTerm) par.getParameters()[0]).getFunction().getName())) {
					throw new SMTLIBException("The cobody has a negative predicate.");
				} else {
					//yi = formula
					tail.addTransitionFormula(par);
				}
			}
			return tail;
		}
		final Cobody tail = new Cobody();
		if (mDeclaredPredicateSymbols.contains(t.getFunction().getName())) {
			// yi = I
			tail.addPredicate(t);
		} else if (t.getFunction().getName().equals("not") && mDeclaredPredicateSymbols
				.contains(((ApplicationTerm) t.getParameters()[0]).getFunction().getName())) {
			throw new SMTLIBException("The cobody has a negative predicate.");
		} else {
			// yi = formula
			tail.addTransitionFormula(t);
		}

		return tail;
	}

	private Body parseBody(Term term) throws SMTLIBException {
		final ApplicationTerm t = (ApplicationTerm) term;
		if (t.getFunction().getName().equals("=>")) {
			// implication
			final Body head = parseBody(t.getParameters()[1]);
			final Cobody tail = parseCobody(t.getParameters()[0]);

			head.mergeCobody(tail);
			return head;
		}
		if (t.getFunction().getName().equals("or")) {
			// t = Or (y1 ... yn)
			final Body head = new Body();
			for (final Term literal : t.getParameters()) {
				final ApplicationTerm par = (ApplicationTerm) literal;
				if (mDeclaredPredicateSymbols.contains(par.getFunction().getName())) {
					// yi = I 
					if (!head.setHead(par)) {
						throw new SMTLIBException("The head has more than a positive predicate symbol.");
					}
				} else if (par.getFunction().getName().equals("not") && mDeclaredPredicateSymbols
						.contains(((ApplicationTerm) par.getParameters()[0]).getFunction().getName())) {
					// yi = ~I
					head.addPredicateToCobody((ApplicationTerm) par.getParameters()[0]);
				} else {
					// yi = formula
					if (!par.equals(getTheory().mFalse)) {
						head.addTransitionFormula(getTheory().not(par));
					}
				}
			}
			return head;
		}
		final Body head = new Body();
		if (mDeclaredPredicateSymbols.contains(t.getFunction().getName())) {
			if (!head.setHead(t)) {
				throw new SMTLIBException("The head has more than a positive predicate symbol.");
			}
		} else if (t.getFunction().getName().equals("not") && mDeclaredPredicateSymbols
				.contains(((ApplicationTerm) t.getParameters()[0]).getFunction().getName())) {
			head.addPredicateToCobody((ApplicationTerm) t.getParameters()[0]);
		} else {
			if (!t.equals(getTheory().mFalse)) {
				head.addTransitionFormula(getTheory().not(t));
			}
		}

		return head;
	}

	@Override
	public LBool assertTerm(Term term) throws SMTLIBException {
		if (term instanceof QuantifiedFormula) {

			final QuantifiedFormula thisTerm = (QuantifiedFormula) term;
			if (thisTerm.getQuantifier() == FORALL) {
				final Body body = parseBody(thisTerm.getSubformula());
				mCurrentHornClause.add(body.convertToHornClause(mBackendSmtSolver, mSymbolTable));
				//System.err.println(mCurrentHornClause.get(mCurrentHornClause.size() - 1));
			}
		}

		if (term instanceof ApplicationTerm && ((ApplicationTerm) term).getFunction().getName().equals("not")) {
			final Term nested = ((ApplicationTerm) term).getParameters()[0];
			if (nested instanceof QuantifiedFormula) {
				final QuantifiedFormula thisTerm = (QuantifiedFormula) nested;
				if (thisTerm.getQuantifier() == EXISTS) {
					final Cobody cobody = parseCobody(thisTerm.getSubformula());
					final Body body = cobody.negate();
					mCurrentHornClause.add(body.convertToHornClause(mBackendSmtSolver, mSymbolTable));
					
					//System.err.println(mCurrentHornClause.get(mCurrentHornClause.size() - 1));
				}
			}
		}
		System.err.println("Parsed: " + mCurrentHornClause);
		// for Horn clause solving we do no checks nothing until check-sat:
		return LBool.UNKNOWN;
	}

	@Override
	public LBool checkSat() {
		// TODO maybe tell the graph builder that we're finished, maybe do
		// nothing..
		return super.checkSat();
	}

	@Override
	public QuotedObject echo(QuotedObject msg) {
		// TODO possibly just write it through the logger..
		return super.echo(msg);
	}

	@Override
	public Sort sort(String sortname, Sort... params) throws SMTLIBException {
		return super.sort(sortname, params);
		// return mBackendSmtSolver.sort(sortname, params);
	}

	@Override
	public Sort sort(String sortname, BigInteger[] indices, Sort... params) throws SMTLIBException {
		return super.sort(sortname, indices, params);
		// return mBackendSmtSolver.sort(sortname, indices, params);
	}

	@Override
	public Sort[] sortVariables(String... names) throws SMTLIBException {
		// return mBackendSmtSolver.sortVariables(names);
		return super.sortVariables(names);
	}

	@Override
	public Term term(String funcname, Term... params) throws SMTLIBException {
		// return mBackendSmtSolver.term(funcname, params);
		return super.term(funcname, params);
	}

	@Override
	public Term term(String funcname, BigInteger[] indices, Sort returnSort, Term... params) throws SMTLIBException {
		// System.err.println("(" + funcname + " " + termsToString(params) +
		// ")");

		final Term result = super.term(funcname, indices, returnSort, params);

		// if (returnSort.getName().equals("Bool")) {
		//
		// }

		if (funcname.equals("=>")) {
			int i = 0;
			i++;

		} else if (mDeclaredPredicateSymbols.contains(funcname)) {
			mCurrentPredicateAtoms.add(result);

		} else {
			mCurrentTransitionAtoms.add(result);
		}

		// return mBackendSmtSolver.term(funcname, indices, returnSort, params);
		return result;
	}

	@Override
	public Theory getTheory() {
		return super.getTheory(); // TODO: maybe return the theory of the
									// backend solver
	}

	@Override
	public void setInfo(String info, Object value) {
		// TODO Auto-generated method stub
		super.setInfo(info, value);
	}

	@Override
	public void defineSort(String sort, Sort[] sortParams, Sort definition) throws SMTLIBException {
		super.defineSort(sort, sortParams, definition);
		// mBackendSmtSolver.defineSort(sort, sortParams, definition);
	}

	@Override
	public void defineFun(String fun, TermVariable[] params, Sort resultSort, Term definition) throws SMTLIBException {
		// TODO Auto-generated method stub
		super.defineFun(fun, params, resultSort, definition);
	}

	@Override
	public void push(int levels) {
		// TODO Auto-generated method stub
		super.push(levels);
	}

	@Override
	public void pop(int levels) throws SMTLIBException {
		// TODO Auto-generated method stub
		super.pop(levels);
	}

	@Override
	public Term[] getAssertions() throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.getAssertions();
	}

	@Override
	public Term getProof() throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return super.getProof();
	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return super.getUnsatCore();
	}

	@Override
	public Map<Term, Term> getValue(Term[] terms) throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return super.getValue(terms);
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return super.getAssignment();
	}

	@Override
	public Object getOption(String opt) throws UnsupportedOperationException {
		// TODO Auto-generated method stub
		return super.getOption(opt);
	}

	@Override
	public Object getInfo(String info) throws UnsupportedOperationException {
		// TODO Auto-generated method stub
		return super.getInfo(info);
	}

	@Override
	public Term simplify(Term term) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.simplify(term);
	}

	@Override
	public void reset() {
		// TODO Auto-generated method stub
		super.reset();
	}

	@Override
	public Term[] getInterpolants(Term[] partition) throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return super.getInterpolants(partition);
	}

	@Override
	public Term[] getInterpolants(Term[] partition, int[] startOfSubtree)
			throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return super.getInterpolants(partition, startOfSubtree);
	}

	@Override
	public void exit() {
		// TODO Auto-generated method stub
		super.exit();
	}

	@Override
	public Term quantifier(int quantor, TermVariable[] vars, Term body, Term[]... patterns) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.quantifier(quantor, vars, body, patterns);
	}

	@Override
	public Term let(TermVariable[] vars, Term[] values, Term body) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.let(vars, values, body);
	}

	@Override
	public Term annotate(Term t, Annotation... annotations) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.annotate(t, annotations);
	}

	@Override
	public Term numeral(String num) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.numeral(num);
	}

	@Override
	public Term numeral(BigInteger num) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.numeral(num);
	}

	@Override
	public Term decimal(String decimal) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.decimal(decimal);
	}

	@Override
	public Term decimal(BigDecimal decimal) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.decimal(decimal);
	}

	@Override
	public Term string(String str) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.string(str);
	}

	@Override
	public Term hexadecimal(String hex) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.hexadecimal(hex);
	}

	@Override
	public Term binary(String bin) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.binary(bin);
	}

	@Override
	public Model getModel() throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return super.getModel();
	}

	@Override
	public Iterable<Term[]> checkAllsat(Term[] predicates) throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return super.checkAllsat(predicates);
	}

	@Override
	public Term[] findImpliedEquality(Term[] x, Term[] y) throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return super.findImpliedEquality(x, y);
	}

	@Override
	public TermVariable variable(String varname, Sort sort) throws SMTLIBException {
		// return mBackendSmtSolver.variable(varname, sort);
		return super.variable(varname, sort);
	}

}
