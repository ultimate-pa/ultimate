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
package de.uni_freiburg.informatik.ultimate.source.smtparser.chc;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.ChcCategoryInfo;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornAnnot;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClauseAST;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet.UnletType;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.INonSolverScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.SkolemNormalForm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalforms.CnfTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.source.smtparser.Activator;
import de.uni_freiburg.informatik.ultimate.source.smtparser.SmtParserPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class HornClauseParserScript extends NoopScript implements INonSolverScript {

	private final String M_COMPLEX_TERM = "sbcnst";
	private final String M_REPEATING_VARS = "sbrptng";
	/**
	 * Interface to the SMT solver that TreeAutomizer (or whoever else will used the HornClauseGraph) will use as a
	 * backend.
	 */
	private final ManagedScript mBackendSmtSolver;
	private final String mLogic;
	private final SolverSettings mSolverSettings;
	private final HashSet<String> mDeclaredPredicateSymbols;
	private final List<HornClause> mParsedHornClauses;
	private final HcSymbolTable mSymbolTable;

	private final String mFilename;

	private final IUltimateServiceProvider mServices;

	/**
	 * ManagedScript wrapping this HornClauseParserScript instance
	 */
	private final ManagedScript mManagedScript;
	private final ILogger mLogger;

	/**
	 * Do sanity checks that require calls to an SMT solver. Note that this leads to crashes if the solver cannot handle
	 * quantifiers.
	 */
	private final boolean mDoSolverBasedSanityChecks = false;
	private boolean mSawCheckSat = false;
	private boolean mFinished;

	private final Stack<Triple<String, List<BigInteger>, List<Term>>> mSimplificationStack;

	private final IPreferenceProvider mPreferences;

	public HornClauseParserScript(final IUltimateServiceProvider services, final ILogger logger, final String filename,
			final ManagedScript smtSolverScript, final String logic, final SolverSettings settings) {
		mServices = services;
		mLogger = logger;
		mFilename = filename;
		mBackendSmtSolver = smtSolverScript;
		mLogic = logic;
		mSolverSettings = settings;
		setupBackendSolver();
		mDeclaredPredicateSymbols = new HashSet<>();

		mManagedScript = new ManagedScript(services, this);

		mParsedHornClauses = new ArrayList<>();

		mSymbolTable = new HcSymbolTable(mBackendSmtSolver);

		mSimplificationStack = new Stack<>();

		mPreferences = services.getPreferenceProvider(Activator.PLUGIN_ID);
	}

	private boolean isUninterpretedPredicateSymbol(final FunctionSymbol fs) {
		return mDeclaredPredicateSymbols.contains(fs.getName());
	}

	public IElement getHornClauses() {
		mFinished = true;
		mSymbolTable.finishConstruction();
		final HornAnnot annot =
				new HornAnnot(mFilename, mBackendSmtSolver, mSymbolTable, mParsedHornClauses, mSawCheckSat,
						new ChcCategoryInfo(Logics.ALL, true));
		return HornClauseAST.create(annot);
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
	public void setLogic(final String logic) throws UnsupportedOperationException {
		assert logic.equals("HORN") : "Error: the SmtParser-setting HornSolverMode is set, "
				+ "but the smt2 file sets the logic to something other than HORN";
		if (!logic.equals("HORN")) {
			throw new UnsupportedOperationException();
		}

		super.setLogic(mLogic);
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException {
		super.setLogic(logic);
	}

	@Override
	public void setOption(final String opt, final Object value) throws UnsupportedOperationException, SMTLIBException {
		// just handing it over to the backend solver
		super.setOption(opt, value);
		// mBackendSmtSolver.setOption(opt, value);
	}

	@Override
	public void declareSort(final String sort, final int arity) throws SMTLIBException {
		super.declareSort(sort, arity);
		// mBackendSmtSolver.declareSort(sort, arity);
	}

	@Override
	public void declareFun(final String fun, final Sort[] paramSorts, final Sort resultSort) throws SMTLIBException {
		// TODO: probably track uninterpreted predicates, i.e., the predicates
		// not known
		// to the theory of the backend solver
		// mBackendSmtSolver.declareFun(fun, paramSorts, resultSort);
		super.declareFun(fun, paramSorts, resultSort);
		if (SmtSortUtils.isBoolSort(resultSort)) {
			mDeclaredPredicateSymbols.add(fun);
		}
	}

	private List<HornClauseHead> parseCnf(final Term term) throws SMTLIBException {
		final List<HornClauseHead> result = new ArrayList<>();

		final Term quantifiersStripped;
		if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula qf = (QuantifiedFormula) term;
			if (qf.getQuantifier() == EXISTS) {
				throw new AssertionError("Input not skolemized??");
			}
			quantifiersStripped = ((QuantifiedFormula) term).getSubformula();
		} else {
			quantifiersStripped = term;
		}

		if (quantifiersStripped instanceof QuantifiedFormula) {
			throw new AssertionError("Input not skolemized??");
		}

		final Term[] clauses = SmtUtils.getConjuncts(quantifiersStripped);

		for (final Term clause : clauses) {
			final HornClauseHead head = new HornClauseHead(this);

			for (final Term literal : SmtUtils.getDisjuncts(clause)) {
				Term literalStripped = literal;
				boolean polarity = true;
				if (SmtUtils.isFunctionApplication(literal, "not")) {
					literalStripped = ((ApplicationTerm) literal).getParameters()[0];
					polarity = false;
				}

				if (literalStripped instanceof ApplicationTerm) {
					final ApplicationTerm lsAt = (ApplicationTerm) literalStripped;
					final FunctionSymbol fsym = lsAt.getFunction();
					if (isUninterpretedPredicateSymbol(fsym)) {
						// literalStripped is an uninterpreted predicate application
						if (polarity) {
							// head
							final boolean headWasNull = head.setHead(mapFormulasToVars(head, lsAt));
							if (!headWasNull) {
								throw new AssertionError("two positive literals in a clause --> not Horn!");
							}
						} else {
							// body ("cobody")
							head.addPredicateToBody(lsAt);
						}
					} else {
						// literalStripped is a constraint
						if (polarity) {
							// the constraint is in the head so we have to reverse polarity here
							head.addTransitionFormula(term("not", literal));
						} else {
							// note this case also catches Boolean variables in the body
							head.addTransitionFormula(lsAt);
						}
					}
				} else if (literalStripped instanceof TermVariable) {
					// literalStripped is a quantified Boolean variable (in the head, thus we have to reverse polarity)
					head.addTransitionFormula(term("not", literal));
				} else {
					throw new AssertionError("TODO: check this case");
				}
			}
			result.add(head);
		}

		return result;
	}

	private ApplicationTerm mapFormulasToVars(final HornClauseHead head, final Term term) {
		final ApplicationTerm func = (ApplicationTerm) term;
		final Term[] variables = new Term[func.getParameters().length];
		for (int i = 0; i < variables.length; ++i) {
			final Term t = func.getParameters()[i];
			final boolean variableHasBeenSeenAlready = Arrays.asList(variables).contains(t);
			if (t instanceof TermVariable && !variableHasBeenSeenAlready) {
				// argument is a variable that occurs for the first time in the argument list, leave it as is
				variables[i] = t;
			} else if (t instanceof TermVariable && variableHasBeenSeenAlready) {
				// argument is a variable that occurs not for the first time in the argument list --> substitute it
				variables[i] = mManagedScript.constructFreshTermVariable(M_REPEATING_VARS, t.getSort());
				head.addTransitionFormula(this.term("=", variables[i], t));
			} else {
				// argument is not a term variable, might be an arithmetic term for example --> substitute it
				variables[i] = mManagedScript.constructFreshTermVariable(M_COMPLEX_TERM, t.getSort());
				head.addTransitionFormula(this.term("=", variables[i], t));
			}
		}
		final ApplicationTerm ret = (ApplicationTerm) this.term(func.getFunction().getName(), variables);
		return ret;
	}

	@Override
	public LBool assertTerm(final Term rawTerm) throws SMTLIBException {
		assert !mFinished;

		final Term normalizedFormula = normalizeInputFormula(rawTerm);

		final List<HornClauseHead> parsedBodies = parseCnf(normalizedFormula);
		final List<HornClause> parsedHornClauses = new ArrayList<>();
		for (final HornClauseHead parsedBody : parsedBodies) {
			final HornClause parsedQuantification =
					parsedBody.convertToHornClause(mBackendSmtSolver, mSymbolTable, this);
			if (parsedQuantification != null) {
				parsedHornClauses.add(parsedQuantification);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("PARSED: " + parsedQuantification.debugString());
				}
			}
		}
		mParsedHornClauses.addAll(parsedHornClauses);
		assert !mDoSolverBasedSanityChecks
				|| checkEquivalence(normalizedFormula, SmtUtils.and(mManagedScript.getScript(), parsedHornClauses
						.stream().map(hc -> hc.constructFormula(mManagedScript, false)).collect(Collectors.toList())));

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Parsed so far: " + mParsedHornClauses);
			mLogger.debug("");
		}
		// for Horn clause solving we do no checks until check-sat
		return LBool.UNKNOWN;
	}

	/**
	 * plan:
	 * <li>prenex, nnf
	 * <li>let every subformula that has no uninterpreted predicates
	 * <li>cnf the body of the let
	 * <li>unlet result: a formula in prenex NF, with a CNF inside TODO: a TermCompiler and Clausifier a la SMTInterpol
	 * might be more efficient
	 */
	public Term normalizeInputFormula(final Term rawTerm) {

		final Term nrmlized = new NormalizingTermTransformer().transform(rawTerm);

		final Term unl = new FormulaUnLet(UnletType.SMTLIB).unlet(nrmlized);

		final Term nnf = new NnfTransformer(mManagedScript, mServices, QuantifierHandling.KEEP, true).transform(unl);

		final Term qnfTerm = new PrenexNormalForm(mManagedScript).transform(nnf);
		final SkolemNormalForm snf = new SkolemNormalForm(mManagedScript, qnfTerm);
		final Term snfTerm = snf.getSkolemizedFormula();
		mSymbolTable.announceSkolemFunctions(snf.getSkolemFunctions());

		Term snfBody;
		TermVariable[] snfVars;
		if (snfTerm instanceof QuantifiedFormula) {
			final QuantifiedFormula qf = (QuantifiedFormula) snfTerm;
			snfBody = qf.getSubformula();
			snfVars = qf.getVariables();
			assert qf.getQuantifier() == FORALL;
		} else {
			snfBody = snfTerm;
			snfVars = null;
		}
		final Set<Term> constraints =
				new SubTermFinder(term -> term.getSort().getName().equals("Bool") && hasNoUninterpretedPredicates(term),
						true).findMatchingSubterms(snfBody);
		final Map<Term, Term> subs = new HashMap<>();
		final Map<Term, Term> subsInverse = new HashMap<>();
		// replace constraints with a boolean constant
		for (final Term c : constraints) {
			final Term freshTv = mManagedScript.constructFreshTermVariable("cnstrnt", sort("Bool"));
			subs.put(c, freshTv);
			assert !subsInverse.containsValue(freshTv);
			subsInverse.put(freshTv, c);
		}
		final Term bodyWithConstraintsReplaced = new Substitution(this, subs).transform(snfBody);

		final Term cnfWConstraintsReplaced =
				new CnfTransformer(mManagedScript, mServices, true).transform(bodyWithConstraintsReplaced);

		final Term cnf = new Substitution(this, subsInverse).transform(cnfWConstraintsReplaced);

		Term normalizedTerm;
		if (snfTerm instanceof QuantifiedFormula) {
			normalizedTerm = quantifier(FORALL, snfVars, cnf);
		} else {
			normalizedTerm = cnf;
		}

		assert checkEquivalence(rawTerm, normalizedTerm) : "transformation unsound";
		return normalizedTerm;
	}

	public boolean checkEquivalence(final Term t1, final Term t2) {
		if (!mDoSolverBasedSanityChecks) {
			return true;
		}

		final TermTransferrer ttf = new TermTransferrer(mBackendSmtSolver.getScript());
		final Term unl1 = new FormulaUnLet(UnletType.SMTLIB).unlet(t1);
		final Term unl2 = new FormulaUnLet(UnletType.SMTLIB).unlet(t2);

		final LBool satResult = Util.checkSat(mBackendSmtSolver.getScript(),
				mBackendSmtSolver.getScript().term("distinct", ttf.transform(unl1), ttf.transform(unl2)));
		return satResult != LBool.SAT;
	}

	private boolean hasNoUninterpretedPredicates(final Term term) {
		final NoSubtermFulfillsPredicate nfsp = new NoSubtermFulfillsPredicate(t -> (t instanceof ApplicationTerm
				&& isUninterpretedPredicateSymbol(((ApplicationTerm) t).getFunction())));
		nfsp.transform(term);
		final boolean result = nfsp.getResult();
		return result;
	}

	@Override
	public LBool checkSat() {
		assert !mFinished;
		if (mSawCheckSat) {
			throw new UnsupportedOperationException("only one check-sat command is supported in Horn solver mode");
		}
		mSawCheckSat = true;
		// TODO maybe tell the graph builder that we're finished, maybe do
		// nothing..
		return super.checkSat();
	}

	@Override
	public QuotedObject echo(final QuotedObject msg) {
		// TODO possibly just write it through the logger..
		return super.echo(msg);
	}

	@Override
	public Sort sort(final String sortname, final Sort... params) throws SMTLIBException {
		return super.sort(sortname, params);
		// return mBackendSmtSolver.sort(sortname, params);
	}

	@Override
	public Sort sort(final String sortname, final BigInteger[] indices, final Sort... params) throws SMTLIBException {
		return super.sort(sortname, indices, params);
		// return mBackendSmtSolver.sort(sortname, indices, params);
	}

	@Override
	public Sort[] sortVariables(final String... names) throws SMTLIBException {
		// return mBackendSmtSolver.sortVariables(names);
		return super.sortVariables(names);
	}

	@Override
	public Term term(final String funcname, final Term... params) throws SMTLIBException {
		// return mBackendSmtSolver.term(funcname, params);
		return super.term(funcname, params);
	}

	@Override
	public Term term(final String funcname, final BigInteger[] indices, final Sort returnSort, final Term... params)
			throws SMTLIBException {

		// workaround to deal with unary and, which occurs in some chc-comp benchmarks (e.g. eldarica..) TODO: ugly!
		if (funcname.equals("and") && params.length == 1) {
			return term(funcname, params[0], term("true"));
		}

		if (!mPreferences.getBoolean(SmtParserPreferenceInitializer.LABEL_DoLocalSimplifications)) {
			// omit local simplifications
			return super.term(funcname, indices, returnSort, params);
		}

		final List<BigInteger> indicesList = indices == null ? null : Arrays.asList(indices);
		final List<Term> paramsList = params == null ? null : Arrays.asList(params);

		final Term result;
		if (!mSimplificationStack.isEmpty()
				&& mSimplificationStack.peek().equals(new Triple<>(funcname, indicesList, paramsList))) {
			result = super.term(funcname, indices, returnSort, params);
		} else {
			mSimplificationStack.push(new Triple<>(funcname, indicesList, paramsList));
			result = SmtUtils.termWithLocalSimplification(this, funcname, indices, returnSort, params);
			mSimplificationStack.pop();
		}
		return result;
	}

	@Override
	public Theory getTheory() {
		// TODO: maybe return the theory of the backend solver
		return super.getTheory();
	}

	@Override
	public void setInfo(final String info, final Object value) {
		// TODO Auto-generated method stub
		super.setInfo(info, value);
	}

	@Override
	public void defineSort(final String sort, final Sort[] sortParams, final Sort definition) throws SMTLIBException {
		super.defineSort(sort, sortParams, definition);
		// mBackendSmtSolver.defineSort(sort, sortParams, definition);
	}

	@Override
	public void defineFun(final String fun, final TermVariable[] params, final Sort resultSort, final Term definition)
			throws SMTLIBException {
		// TODO Auto-generated method stub
		super.defineFun(fun, params, resultSort, definition);
	}

	@Override
	public void push(final int levels) {
		// TODO Auto-generated method stub
		super.push(levels);
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
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
	public Map<Term, Term> getValue(final Term[] terms) throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return super.getValue(terms);
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return super.getAssignment();
	}

	@Override
	public Object getOption(final String opt) throws UnsupportedOperationException {
		// TODO Auto-generated method stub
		return super.getOption(opt);
	}

	@Override
	public Object getInfo(final String info) throws UnsupportedOperationException {
		// TODO Auto-generated method stub
		return super.getInfo(info);
	}

	@Override
	public Term simplify(final Term term) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.simplify(term);
	}

	@Override
	public void reset() {
		// TODO Auto-generated method stub
		super.reset();
	}

	@Override
	public Term[] getInterpolants(final Term[] partition) throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return super.getInterpolants(partition);
	}

	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree)
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
	public Term quantifier(final int quantor, final TermVariable[] vars, final Term body, final Term[]... patterns)
			throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.quantifier(quantor, vars, body, patterns);
	}

	@Override
	public Term let(final TermVariable[] vars, final Term[] values, final Term body) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.let(vars, values, body);
	}

	@Override
	public Term annotate(final Term t, final Annotation... annotations) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.annotate(t, annotations);
	}

	@Override
	public Term numeral(final String num) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.numeral(num);
	}

	@Override
	public Term numeral(final BigInteger num) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.numeral(num);
	}

	@Override
	public Term decimal(final String decimal) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.decimal(decimal);
	}

	@Override
	public Term decimal(final BigDecimal decimal) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.decimal(decimal);
	}

	@Override
	public Term string(final String str) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.string(str);
	}

	@Override
	public Term hexadecimal(final String hex) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.hexadecimal(hex);
	}

	@Override
	public Term binary(final String bin) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.binary(bin);
	}

	@Override
	public Model getModel() throws SMTLIBException, UnsupportedOperationException {
		return new Model() {

			@Override
			public Term getFunctionDefinition(final String func, final TermVariable[] args) {
				throw new UnsupportedOperationException();
			}

			@Override
			public Set<FunctionSymbol> getDefinedFunctions() {
				throw new UnsupportedOperationException();
			}

			@Override
			public Map<Term, Term> evaluate(final Term[] input) {
				throw new UnsupportedOperationException();
			}

			@Override
			public Term evaluate(final Term input) {
				throw new UnsupportedOperationException();
			}
		};
	}

	@Override
	public Iterable<Term[]> checkAllsat(final Term[] predicates) throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return super.checkAllsat(predicates);
	}

	@Override
	public Term[] findImpliedEquality(final Term[] x, final Term[] y)
			throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return super.findImpliedEquality(x, y);
	}

	@Override
	public TermVariable variable(final String varname, final Sort sort) throws SMTLIBException {
		// return mBackendSmtSolver.variable(varname, sort);
		return super.variable(varname, sort);
	}

	static class NoSubtermFulfillsPredicate extends TermTransformer {

		private boolean mResult;

		private final Predicate<Term> mPred;

		public NoSubtermFulfillsPredicate(final Predicate<Term> pred) {
			mPred = pred;
			mResult = true;
		}

		@Override
		protected void convert(final Term term) {
			if (mPred.test(term)) {
				mResult = false;
			}
			super.convert(term);
		}

		boolean getResult() {
			return mResult;
		}
	}

	/**
	 * Apply some normalizations to formulas we parsed. Similar in purpose to SMTInterpol's TermCompiler.
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 */
	class NormalizingTermTransformer extends TermTransformer {

		@Override
		public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
			final FunctionSymbol fsym = appTerm.getFunction();
			final Sort[] paramSorts = fsym.getParameterSorts();

			Term convertedAppTerm = appTerm;
			Term[] args = newArgs;

			/*
			 * modified copy from TermCompiler, "IRA-hack", i.e., if an literal is given at a place that needs a real
			 * wrap it in a to_real to make it explicit..
			 */
			if (paramSorts.length == 2 && paramSorts[0].getName().equals("Real") && paramSorts[1] == paramSorts[0]) {
				// IRA-Hack
				if (args == appTerm.getParameters()) {
					args = args.clone();
				}
				boolean changed = false;
				final Term[] desugarParams = new Term[args.length];
				final Term[] nargs = new Term[args.length];
				for (int i = 0; i < args.length; i++) {
					final Term arg = args[i];// mTracker.getProvedTerm(args[i]);
					if (arg.getSort().getName().equals("Int")) {
						desugarParams[i] = term("to_real", arg);
						nargs[i] = desugarParams[i];
						changed = true;
					} else {
						desugarParams[i] = arg;
						nargs[i] = arg;
					}
				}
				if (changed) {
					convertedAppTerm = term(fsym.getName(), nargs);
				}
			}

			/*
			 * inlining of defined functions, also taken from TermCompiler
			 */
			final Term[] params = ((ApplicationTerm) convertedAppTerm).getParameters();
			if (fsym.getDefinition() != null) {
				final HashMap<TermVariable, Term> substs = new HashMap<>();
				for (int i = 0; i < params.length; i++) {
					substs.put(fsym.getDefinitionVars()[i], params[i]);
				}
				final FormulaUnLet unletter = new FormulaUnLet();
				unletter.addSubstitutions(substs);
				final Term expanded = unletter.unlet(fsym.getDefinition());
				convertedAppTerm = expanded;
			}

			if (convertedAppTerm != appTerm) {
				setResult(convertedAppTerm);
			} else {
				super.convertApplicationTerm(appTerm, newArgs);
			}
		}

	}
}