package de.uni_freiburg.informatik.ultimate.lib.treeautomizer;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * This is our internal representation of a Horn clause. A Horn clause consists
 * of - a body with -- n uninterpreted predicate symbols (n >= 0) -- a
 * transition formula - a head with either -- an uninterpreted predicate symbol
 * or -- false - a mapping that assigns each of the argument positions of the
 * uninterpreted predicate a free variable in the transition formula
 *
 * Note that the uninterpreted predicate symbols may only have an arity and a
 * name. If in the formula there was a complex expression in one of the
 * arguments of the corresponding atom, this has to be encoded into the
 * transition formula.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class HornClause implements IRankedLetter {

	private final List<HornClausePredicateSymbol> mBodyPreds;

	private final List<List<TermVariable>> mBodyPredToTermVariables;

	/**
	 * Stores for the predicate symbol in the head at every argument position of
	 * the represented atom, which TermVariable in the transition formula
	 * represents that argument in the represented atom.
	 */
	private final List<TermVariable> mHeadPredTermVariables;
	private final HornClausePredicateSymbol mHeadPredicate;

	private final HCSymbolTable mHornClauseSymbolTable;
	
	private final Term mFormula;

	/**
	 * Standard constructor for a Horn clause as used by TreeAutomizer.
	 * 
	 * @param script
	 *            The script that will be used in TreeAutomizer (not the
	 *            HornClauseParserScript)
	 * @param symbolTable
	 * @param constraint
	 * @param headPred
	 * @param headVars
	 * @param bodyPreds
	 * @param bodyPredToTermVariables
	 */
	public HornClause(final ManagedScript script, final HCSymbolTable symbolTable, final Term constraint,
			final HornClausePredicateSymbol headPred, final List<TermVariable> headVars,
			final List<HornClausePredicateSymbol> bodyPreds, final List<List<TermVariable>> bodyPredToTermVariables, 
			int version) {

		mHornClauseSymbolTable = symbolTable;

		final TermTransferrer ttf = new TermTransferrer(script.getScript());

		/*
		 * send all the TermVariables through the TermTransferrer
		 */
		mHeadPredTermVariables = headVars.stream().map(var -> (TermVariable) ttf.transform(var))
				.collect(Collectors.toList());
		mBodyPredToTermVariables = bodyPredToTermVariables.stream()
				.map(list -> list.stream().map(var -> (TermVariable) ttf.transform(var)).collect(Collectors.toList()))
				.collect(Collectors.toList());
		
		// transfer the transition formula to the solver script
		mFormula = ttf.transform(constraint);
		
		for (TermVariable fv : mFormula.getFreeVars()) {
			mHornClauseSymbolTable.registerTermVariable(fv);
		}

		mHeadPredicate = headPred;
		mBodyPreds = bodyPreds;
	}

	public HornClause(final ManagedScript script, final HCSymbolTable symbolTable,
			 final Term transitionFormula,
			final HornClausePredicateSymbol head, final List<TermVariable> headVars,
			final List<HornClausePredicateSymbol> bodyPreds, final List<List<TermVariable>> bodyPredToTermVariables) {
		this(script, symbolTable, transitionFormula, head, headVars, bodyPreds, bodyPredToTermVariables, 0);
	}

	public HornClausePredicateSymbol getHeadPredicate() {
		return mHeadPredicate;
	}

	public List<HornClausePredicateSymbol> getBodyPredicates() {
		return mBodyPreds;
	}

	public int getNoBodyPredicates() {
		return mBodyPreds.size();
	}

	public TermVariable getPredArgTermVariable(int predPos, int argPos) {
		return mBodyPredToTermVariables.get(predPos).get(argPos);
	}

	public List<TermVariable> getTermVariablesForPredPos(int predPos) {
		return mBodyPredToTermVariables.get(predPos);
	}
	
	public List<List<TermVariable>> getBodyPredToTermVariables() {
		return Collections.unmodifiableList(mBodyPredToTermVariables);
	}

	public List<TermVariable> getTermVariablesForHeadPred() {
		return mHeadPredTermVariables;
	}

	@Override
	public String toString() {
		// String cobody = "";
		//
		// for (final HornClausePredicateSymbol symbol :
		// mBodyPredToTermVariables.keySet()) {
		// cobody += " " + symbol.getName() +
		// mBodyPredToTermVariables.get(symbol);
		// }
		// if (cobody.length() > 0) {
		// cobody = "and" + cobody;
		// } else {
		// cobody = "true";
		// }
		//
		// final String body = mHeadPredicate.getName() +
		// mHeadPredTermVariables;
//		if (mTransitionFormula == null) {
		if (mFormula == null) {
			return "unintialized HornClause";
		}

//		return mTransitionFormula.getFormula().toString();
		return mFormula.toString();
		// return String.format("(%s) ^^ (%s) ~~> (%s) || in : %s || out : %s ",
		// cobody, mTransitionFormula, body,
		// return String.format("(%s) ^^ (%s) ~~> (%s)", cobody,
		// mTransitionFormula.getFormula(), body);
		// return "HornClause TODO: better description"; //TODO
	}

	public HCSymbolTable getHornClauseSymbolTable() {
		return mHornClauseSymbolTable;
	}

	@Override
	public int getRank() {
//		if (mBodyPreds.isEmpty()) {//mTransitionFormula.getInVars().isEmpty()) {
//			// Initial state
//			return 1;
//		}
		return mBodyPreds.size();// mTransitionFormula.getInVars().size();
	}
	public Term getFormula() {
		return mFormula;
	}

}
