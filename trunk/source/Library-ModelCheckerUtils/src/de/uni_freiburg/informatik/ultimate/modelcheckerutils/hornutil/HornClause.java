package de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * This is our internal representation of a Horn clause. A Horn clause consists of - a body with -- n uninterpreted
 * predicate symbols (n >= 0) -- a transition formula - a head with either -- an uninterpreted predicate symbol or --
 * false - a mapping that assigns each of the argument positions of the uninterpreted predicate a free variable in the
 * transition formula
 *
 * Note that the uninterpreted predicate symbols may only have an arity and a name. If in the formula there was a
 * complex expression in one of the arguments of the corresponding atom, this has to be encoded into the transition
 * formula.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class HornClause implements IInternalAction {

//	/**
//	 * Stores for each predicate symbol in the body and, every argument position of the represented atom, which
//	 * TermVariable in the transition formula represents that argument in the represented atom.
//	 */
//	private final Map<HornClausePredicateSymbol, List<TermVariable>> mBodyPredToTermVariables;
	
	private final List<HornClausePredicateSymbol> mBodyPreds;

	private final List<List<TermVariable>> mBodyPredToTermVariables;

	/**
	 * Stores for the predicate symbol in the head at every argument position of the represented atom, which
	 * TermVariable in the transition formula represents that argument in the represented atom.
	 */
	private final List<TermVariable> mHeadPredTermVariables;
	private final HornClausePredicateSymbol mHeadPredicate;

	private final UnmodifiableTransFormula mTransitionFormula;
	
//	private final HCTransFormula mHcTransFormula;
	
	/**
	 * Standard constructor for a Horn clause as used by TreeAutomizer.
	 * 
	 * @param script The script that will be used in TreeAutomizer (not the HornClauseParserScript)
	 * @param symbolTable
	 * @param transitionFormula
	 * @param headVars
	 * @param head
	 * @param bodyPredToTermVariables
	 */
	public HornClause(final ManagedScript script, 
			final IIcfgSymbolTable symbolTable, 
			final Term transitionFormula, 
			final HornClausePredicateSymbol head, 
			final List<TermVariable> headVars, 
			final List<HornClausePredicateSymbol> bodyPreds,
			final List<List<TermVariable>> bodyPredToTermVariables) {
//			final Map<HornClausePredicateSymbol, List<TermVariable>> bodyPredToTermVariables) {

		TermTransferrer ttf = new TermTransferrer(script.getScript());
		
		/*
		 * send all the TermVariables through the TermTransferrer
		 */
		mHeadPredTermVariables = headVars.stream()
				.map(var -> (TermVariable) ttf.transform(var))
				.collect(Collectors.toList());
		mBodyPredToTermVariables = bodyPredToTermVariables.stream()
				.map(list -> list.stream()
						.map(var -> (TermVariable) ttf.transform(var))
						.collect(Collectors.toList()))
				.collect(Collectors.toList());

		
		mHeadPredicate = head;
		mBodyPreds = bodyPreds;
		
		final Term convertedFormula = ttf.transform(transitionFormula);
		
//		assert false : "TODO";// TODO
//		mHcTransFormula = null;

		final Map<IProgramVar, TermVariable> outVars = new HashMap<>();
		for (int i = 0; i < mHeadPredTermVariables.size(); ++i) {
			outVars.put(head.getHCVars().get(i), mHeadPredTermVariables.get(i));
		}
	
		final Map<IProgramVar, TermVariable> inVars = new HashMap<>();
		for (final Entry<HornClausePredicateSymbol, List<TermVariable>> en : mBodyPredToTermVariables.entrySet()) {
			final List<TermVariable> vars = en.getValue();
	
			for (int i = 0; i < vars.size(); ++i) {
				inVars.put(en.getKey().getHCVars().get(i), vars.get(i));
			}
	
		}

		final TransFormulaBuilder tb = new TransFormulaBuilder(inVars, outVars, true, null, true, null, true);
		tb.setFormula(convertedFormula);
		tb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		mTransitionFormula = tb.finishConstruction(script);
	}

	@Override
	public UnmodifiableTransFormula getTransformula() {
		return mTransitionFormula;
//		assert false : "TODO : what?";
//		return null;
	}
	
	public HornClausePredicateSymbol getHeadPredicate() {
		return mHeadPredicate;
	}
	
	public List<HornClausePredicateSymbol> getBodyPredicates() {
//		return mBodyPredToTermVariables.keySet();
		return mBodyPreds;
	}
	
	@Override
	public String toString() {
//		String cobody = "";
//
//		for (final HornClausePredicateSymbol symbol : mBodyPredToTermVariables.keySet()) {
//			cobody += " " + symbol.getName() + mBodyPredToTermVariables.get(symbol);
//		}
//		if (cobody.length() > 0) {
//			cobody = "and" + cobody;
//		} else {
//			cobody = "true";
//		}
//
//		final String body = mHeadPredicate.getName() + mHeadPredTermVariables;

//		return mTransitionFormula.getFormula().toString();
		//return String.format("(%s) ^^ (%s) ~~> (%s) || in : %s || out : %s ", cobody, mTransitionFormula, body,
		//return String.format("(%s) ^^ (%s) ~~> (%s)", cobody, mTransitionFormula.getFormula(), body);
		return "HornClause TODO: better description"; //TODO
	}

	/**
	 * This method is added only for fulfilling the IInternalAction interface.
	 */
	@Override
	public String getPrecedingProcedure() {
		return HornUtilConstants.HORNCLAUSEMETHODNAME;
	}

	/**
	 * This method is added only for fulfilling the IInternalAction interface.
	 */
	@Override
	public String getSucceedingProcedure() {
		return HornUtilConstants.HORNCLAUSEMETHODNAME;
	}

//	public HCTransFormula getHcTransformula() {
//		return mHcTransFormula;
//	}


}
