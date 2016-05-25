package de.uni_freiburg.informatik.ultimate.plugins.generator.hornclausegraphbuilder.script;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;

public class HornClauseParserScript extends NoopScript {
	
	

	/**
	 * Interface to the SMT solver that TreeAutomizer (or whoever else will used 
	 * the HornClauseGraph) will use as a backend.
	 */
	private final Script mBackendSmtSolver;
	private final String mLogic;
	private final Settings mSolverSettings;
	private HashSet<String> mDeclaredPredicateSymbols;
	private HornClause mCurrentHornClause;
	private ArrayList<Term> mcurrentPredicateAtoms;
	private ArrayList<Term> mcurrentTransitionAtoms;

	public HornClauseParserScript(Script smtSolverScript, String logic, Settings settings) {
		
		
		mBackendSmtSolver = smtSolverScript;
		mLogic = logic;
		mSolverSettings = settings;
		setupBackendSolver();

	}

	/**
	 * Make the necessary settings in the background solver, like
	 * set-logic etc.
	 * @param smtSolverScript
	 */
	private void setupBackendSolver() {

//		mBackendSmtSolver.setLogic(Logics.AUFLIRA); //TODO: do this according to a setting
		
		//TODO possibly set some options etc.
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
		//		super.setLogic(logic);
		super.setLogic(logic);
	}

	@Override
	public void setOption(String opt, Object value) throws UnsupportedOperationException, SMTLIBException {
		// just handing it over to the backend solver
		super.setOption(opt, value);
//		mBackendSmtSolver.setOption(opt, value);
	}

	@Override
	public void declareSort(String sort, int arity) throws SMTLIBException {
		super.declareSort(sort, arity);
//		mBackendSmtSolver.declareSort(sort, arity);
	}

	@Override
	public void declareFun(String fun, Sort[] paramSorts, Sort resultSort) throws SMTLIBException {
		// TODO: probably track uninterpreted predicates, i.e., the predicates not known
		//  to the theory of the backend solver
//		mBackendSmtSolver.declareFun(fun, paramSorts, resultSort);
		super.declareFun(fun, paramSorts, resultSort);
		if (resultSort.getName() == "Bool") {
			mDeclaredPredicateSymbols.add(fun);
		}
	}

	@Override
	public LBool assertTerm(Term term) throws SMTLIBException {
		//TODO Go over the asserted formula
		// - identify the parts of the Horn clause
		//  -- identify the uninterpreted predicates
		//  -- identify the "statement"
		// - compute a TransFormula from the above
		// 
		mCurrentHornClause = new HornClause();
		
        // for Horn clause solving we do no checks nothing until check-sat:
		return LBool.UNKNOWN; 
	}

	@Override
	public LBool checkSat() {
		// TODO maybe tell the graph builder that we're finished, maybe do nothing..
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
//		return mBackendSmtSolver.sort(sortname, params);
	}

	@Override
	public Sort sort(String sortname, BigInteger[] indices, Sort... params) throws SMTLIBException {
		return super.sort(sortname, indices, params);
//		return mBackendSmtSolver.sort(sortname, indices, params);
	}

	@Override
	public Sort[] sortVariables(String... names) throws SMTLIBException {
//		return mBackendSmtSolver.sortVariables(names);
		return super.sortVariables(names);
	}

	@Override
	public Term term(String funcname, Term... params) throws SMTLIBException {
//		return mBackendSmtSolver.term(funcname, params);
		return super.term(funcname, params);
	}

	@Override
	public Term term(String funcname, BigInteger[] indices, Sort returnSort, Term... params) throws SMTLIBException {
		
		final Term result = super.term(funcname, indices, returnSort, params);

//		if (returnSort.getName().equals("Bool")) {
//			
//		}
		
		if (funcname.equals("=>")) {
			int i = 0;
			i++;
			
		} else if (mDeclaredPredicateSymbols.contains(funcname)) {
			mcurrentPredicateAtoms.add(result);
		} else {
			mcurrentTransitionAtoms.add(result);
		}
		
//		return mBackendSmtSolver.term(funcname, indices, returnSort, params);
		return result;
	}

	@Override
	public Theory getTheory() {
		return null; //TODO: maybe return the theory of the backend solver
	}

	@Override
	public void setInfo(String info, Object value) {
		// TODO Auto-generated method stub
		super.setInfo(info, value);
	}

	@Override
	public void defineSort(String sort, Sort[] sortParams, Sort definition) throws SMTLIBException {
		super.defineSort(sort, sortParams, definition);
//		mBackendSmtSolver.defineSort(sort, sortParams, definition);
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
//		return mBackendSmtSolver.variable(varname, sort);
		return super.variable(varname, sort);
	}
	
	
	
}
