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

	// /**
	// * Stores for each predicate symbol in the body and, every argument
	// position of the represented atom, which
	// * TermVariable in the transition formula represents that argument in the
	// represented atom.
	// */
	// private final Map<HornClausePredicateSymbol, List<TermVariable>>
	// mBodyPredToTermVariables;

	private final List<HornClausePredicateSymbol> mBodyPreds;

	private final List<List<TermVariable>> mBodyPredToTermVariables;
//	private final List<List<HCInVar>> mBodyPredToHCInVars;
//	private List<List<IProgramVar>> mBodyPredToIProgramVar;

	/**
	 * Stores for the predicate symbol in the head at every argument position of
	 * the represented atom, which TermVariable in the transition formula
	 * represents that argument in the represented atom.
	 */
	private final List<TermVariable> mHeadPredTermVariables;
//	private final List<IProgramVar> mHeadPredProgramVariables;
	private final HornClausePredicateSymbol mHeadPredicate;

//	private final UnmodifiableTransFormula mTransitionFormula;

	private final HCSymbolTable mHornClauseSymbolTable;
	
	private final Term mFormula;

	/**
	 * Standard constructor for a Horn clause as used by TreeAutomizer.
	 * 
	 * @param script
	 *            The script that will be used in TreeAutomizer (not the
	 *            HornClauseParserScript)
	 * @param symbolTable
	 * @param transitionFormula
	 * @param headPred
	 * @param headVars
	 * @param bodyPreds
	 * @param bodyPredToTermVariables
	 */
	public HornClause(final ManagedScript script, final HCSymbolTable symbolTable,
			final Term transitionFormula,
			final HornClausePredicateSymbol headPred, final List<TermVariable> headVars,
			final List<HornClausePredicateSymbol> bodyPreds, final List<List<TermVariable>> bodyPredToTermVariables, int version) {

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
//		Term convertedFormula = ttf.transform(transitionFormula);
		mFormula = ttf.transform(transitionFormula);
		
		for (TermVariable fv : mFormula.getFreeVars()) {
			mHornClauseSymbolTable.registerTermVariable(fv);
		}

		mHeadPredicate = headPred;
		mBodyPreds = bodyPreds;

//		mBodyPredToHCInVars = new ArrayList<>();
//		mBodyPredToIProgramVar = new ArrayList<>();

//		mHeadPredProgramVariables = new ArrayList<>();

//		/*
//		 * build the TransFormula
//		 */
//		final Map<IProgramVar, TermVariable> outVars = new HashMap<>();
//		for (int i = 0; i < mHeadPredTermVariables.size(); ++i) {
//			final TermVariable tv = mHeadPredTermVariables.get(i);
//			final Sort sort = tv.getSort();
//			final HCOutVar hcOutVar = symbolTable.getOrConstructHCOutVar(i, sort);
//			mHeadPredProgramVariables.add(hcOutVar);
////			if (Arrays.asList(convertedFormula.getFreeVars()).contains(tv)) {
//				outVars.put(hcOutVar, tv);
////			}
//		}
//
//		final Map<IProgramVar, TermVariable> inVars = new HashMap<>();
//		for (int i = 0; i < mBodyPredToTermVariables.size(); i++) {
//			mBodyPredToHCInVars.add(new ArrayList<>());
//			mBodyPredToIProgramVar.add(new ArrayList<>());
//			for (int j = 0; j < mBodyPredToTermVariables.get(i).size(); j++) {
//				final TermVariable tv = mBodyPredToTermVariables.get(i).get(j);
//				final Sort sort = tv.getSort();
//				final HCInVar hcInVar = symbolTable.getOrConstructHCInVar(i, j, sort);
//				mBodyPredToHCInVars.get(i).add(hcInVar);
//				mBodyPredToIProgramVar.get(i).add(hcInVar);
////				if (Arrays.asList(convertedFormula.getFreeVars()).contains(tv)) {
//					inVars.put(hcInVar, tv);
////				}
//			}
//		}
		
		// introduce "x = x" for any unchanged var x, i.e., a var that occurs in head and body..
//		final Set<TermVariable> intersection = new HashSet<>();
//		mBodyPredToTermVariables.stream().forEach(bptvList -> intersection.addAll(bptvList));
//		intersection.retainAll(mHeadPredTermVariables);
//		script.lock(this);
//		for (TermVariable unchangedVar : intersection) {
//			convertedFormula = Util.and(script.getScript(), convertedFormula, 
//					script.term(this, "=", unchangedVar, unchangedVar));
//		}
//		script.unlock(this);


//		final TransFormulaBuilder tb = new TransFormulaBuilder(inVars, outVars, true, null, true, null, true);
//		tb.setFormula(convertedFormula);
//		tb.setInfeasibility(Infeasibility.NOT_DETERMINED);
//		mTransitionFormula = tb.finishConstruction(script);
	}
	public HornClause(final ManagedScript script, final HCSymbolTable symbolTable,
			 final Term transitionFormula,
			final HornClausePredicateSymbol head, final List<TermVariable> headVars,
			final List<HornClausePredicateSymbol> bodyPreds, final List<List<TermVariable>> bodyPredToTermVariables) {
		this(script, symbolTable, transitionFormula, head, headVars, bodyPreds, bodyPredToTermVariables, 0);
	}

//	@Override
//	public UnmodifiableTransFormula getTransformula() {
//		return mTransitionFormula;
//		// assert false : "TODO : what?";
//		// return null;
//	}

	public HornClausePredicateSymbol getHeadPredicate() {
		return mHeadPredicate;
	}

	public List<HornClausePredicateSymbol> getBodyPredicates() {
		// return mBodyPredToTermVariables.keySet();
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

//	public List<HCInVar> getHCInVarsForPredPos(int predPos) {
//		return mBodyPredToHCInVars.get(predPos);
//	}

//	public List<IProgramVar> getProgramVarsForPredPos(int predPos) {
//		return mBodyPredToIProgramVar.get(predPos);
//	}

	public List<TermVariable> getTermVariablesForHeadPred() {
		return mHeadPredTermVariables;
	}

//	public List<IProgramVar> getProgramVarsForHeadPred() {
//		return mHeadPredProgramVariables;
//	}

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

//	/**
//	 * This method is added only for fulfilling the IInternalAction interface.
//	 */
//	@Override
//	public String getPrecedingProcedure() {
//		return HornUtilConstants.HORNCLAUSEMETHODNAME;
//	}

//	/**
//	 * This method is added only for fulfilling the IInternalAction interface.
//	 */
//	@Override
//	public String getSucceedingProcedure() {
//		return HornUtilConstants.HORNCLAUSEMETHODNAME;
//	}

	public HCSymbolTable getHornClauseSymbolTable() {
		return mHornClauseSymbolTable;
	}

	@Override
	public int getRank() {
		if (mBodyPreds.isEmpty()) {//mTransitionFormula.getInVars().isEmpty()) {
			// Initial state
			return 1;
		}
		return mBodyPreds.size();// mTransitionFormula.getInVars().size();
		//return mBodyPreds.size();
	}
	public Term getFormula() {
		return mFormula;
	}

}
