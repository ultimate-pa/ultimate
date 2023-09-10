/*
 * Copyright (C) 2020 Jacob Maxam (jacob.maxam@googlemail.com)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.counting;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * Acceptance method for Counting Automata
 *
 * @author Jacob Maxam
 */

public class Acceptance<LETTER, STATE, CRSF extends IStateFactory<STATE>> implements IOperation<LETTER, STATE, CRSF> {

	private final AutomataLibraryServices mServices;
	private final Script mScript;
	private final ILogger mLogger;
	private final CountingAutomaton<LETTER, STATE> mOperand;
	private final List<LETTER> mWord;
	private final LBool mResult;

	public Acceptance(final AutomataLibraryServices services, final CountingAutomaton<LETTER, STATE> operand,
			final NestedWord<LETTER> word) throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(this.getClass());
		mOperand = operand;
		mWord = word.asList();
		mScript = new SMTInterpol();
		mScript.setLogic(Logics.LIA);

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mResult = computeResult();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	private LBool computeResult() {
		ArrayList<ArrayList<Guard>> preConditions = new ArrayList<ArrayList<Guard>>();
		preConditions.add(new ArrayList<Guard>());
		return iterativeAcceptance(mOperand, preConditions);
	}

	private LBool iterativeAcceptance(CountingAutomaton<LETTER, STATE> ca, ArrayList<ArrayList<Guard>> preConditions) {
	int wordLength = mWord.size();
	List<STATE> states = new ArrayList<STATE>();
	states.addAll(ca.getStates());
	
	LBool result = LBool.UNSAT;
	
	int step = 0;
	Term[] conditions = new Term[wordLength + 2];
	ArrayList<STATE> stateVisited = new ArrayList<STATE>();
	for (int i = 0; i < wordLength + 2; i++) {
		stateVisited.add((STATE) new Object());
	}
	int[] pathTaken = new int[wordLength + 2];
	
	conditions[0] = dnfToFormula(preConditions, 0);
	
	mLogger.log(LogLevel.INFO, wordLength);
	mLogger.log(LogLevel.INFO, stateVisited.size());
	
	while(step > 0 || pathTaken[step] < states.size()){
		mLogger.log(LogLevel.INFO, "entering loop with step = " + step +", trying path #" + (pathTaken[step] + 1));
		if (step > wordLength) {
			mLogger.log(LogLevel.INFO, "end of word reached. checking term satisfiability:");
			conditions[step] = mScript.term("and", conditions[step], dnfToFormula(ca.getFinalConditions().get(stateVisited.get(step)).getCondition(), step));
			Term conditionsQuantified = mScript.quantifier(mScript.EXISTS, conditions[step].getFreeVars(), conditions[step], null);
			mLogger.log(LogLevel.INFO, conditionsQuantified);
			mScript.assertTerm(conditionsQuantified);
			LBool pathResult = mScript.checkSat();
			mScript.resetAssertions();
			if (pathResult == LBool.SAT) { return LBool.SAT; } else if(pathResult == LBool.UNKNOWN) {result = LBool.UNKNOWN;}
			mLogger.log(LogLevel.INFO, "term unsatisfiable");
			step--;
			pathTaken[step]++;
		} else if (step > 0 && pathTaken[step] >= ca.getTransitions().get(stateVisited.get(step)).size()){
			mLogger.log(LogLevel.INFO, "only " + ca.getTransitions().get(stateVisited.get(step)).size() + " possible transitions. going back");
			step--;
			pathTaken[step]++;
		} else if (step == 0){
			mLogger.log(LogLevel.INFO, "choosing initial state: " + states.get(pathTaken[step]));
			conditions[step + 1] = mScript.term("and", conditions[step], dnfToFormula(ca.getInitialConditions().get(states.get(pathTaken[step])).getCondition(), step));
			conditions[step + 1] = mScript.term("and", conditions[step + 1], updateToFormula(new ArrayList<Update>(), ca.getCounter(), step));
			stateVisited.set(step + 1, states.get(pathTaken[step]));
			pathTaken[step + 1] = 0;
			step++;
		} else {
			mLogger.log(LogLevel.INFO, "state: " + stateVisited.get(step));
			Transition t = ca.getTransitions().get(stateVisited.get(step)).get(pathTaken[step]);
			mLogger.log(LogLevel.INFO, "checking transition to " + t.getSucState());
			LETTER a = mWord.get(step-1);
			LETTER b = (LETTER) t.getLetter();
			mLogger.log(LogLevel.INFO, "required letter: '" + a + "', letter in transition: '" + b + "'");
			if (a.equals(b)){
				mLogger.log(LogLevel.INFO, "found transition. going on");
				conditions[step + 1] = mScript.term("and", conditions[step], dnfToFormula(t.getGuards(), step), updateToFormula(t.getUpdates(), ca.getCounter(), step));
				stateVisited.set(step + 1, (STATE) t.getSucState());
				pathTaken[step + 1] = 0;
				step++;
			} else {
				mLogger.log(LogLevel.INFO, "transition unavailable");
				pathTaken[step]++;
			}
		}
	}
	
	mLogger.log(LogLevel.INFO, "no more states left");
	
	return result;
}

	private Term dnfToFormula(ArrayList<ArrayList<Guard>> dnf, int step) {
		String counterSuffix = "#" + String.valueOf(step);
		Term dnfFormula, conjunctionFormula, atomicGuardFormula, leftCounterVariable, rightSide, rightCounterVariable,
				constant;
		dnfFormula = null;
		for (List<Guard> guardList : dnf) {
			conjunctionFormula = null;
			for (Guard guard : guardList) {
				atomicGuardFormula = null;
				leftCounterVariable = null;
				rightSide = null;
				switch (guard.getTermType()) {
				case TRUE:
					atomicGuardFormula = mScript.term("true");
					break;
				case FALSE:
					atomicGuardFormula = mScript.term("false");
					break;
				case CONSTANT:
					leftCounterVariable = mScript.variable(guard.getCounterLeft().getCounterName() + counterSuffix,
							SmtSortUtils.getIntSort(mScript));
					rightSide = mScript.numeral(BigInteger.valueOf(guard.getConstant()));
					break;
				case COUNTER:
					leftCounterVariable = mScript.variable(guard.getCounterLeft().getCounterName() + counterSuffix,
							SmtSortUtils.getIntSort(mScript));
					rightSide = mScript.variable(guard.getCounterRight().getCounterName() + counterSuffix,
							SmtSortUtils.getIntSort(mScript));
					break;
				case SUM:
					leftCounterVariable = mScript.variable(guard.getCounterLeft().getCounterName() + counterSuffix,
							SmtSortUtils.getIntSort(mScript));
					rightCounterVariable = mScript.variable(guard.getCounterRight().getCounterName() + counterSuffix,
							SmtSortUtils.getIntSort(mScript));
					constant = mScript.numeral(BigInteger.valueOf(guard.getConstant()));
					rightSide = mScript.term("+", rightCounterVariable, constant);
					break;
				}
				if (atomicGuardFormula == null) {
					switch (guard.getRelationSymbol()) {
					case EQ:
						atomicGuardFormula = mScript.term("=", leftCounterVariable, rightSide);
						break;
					case DISTINCT:
						atomicGuardFormula = mScript.term("distinct", leftCounterVariable, rightSide);
						break;
					case GREATER:
						atomicGuardFormula = mScript.term(">", leftCounterVariable, rightSide);
						break;
					case LESS:
						atomicGuardFormula = mScript.term("<", leftCounterVariable, rightSide);
						break;
					case GEQ:
						atomicGuardFormula = mScript.term(">=", leftCounterVariable, rightSide);
						break;
					case LEQ:
						atomicGuardFormula = mScript.term("<=", leftCounterVariable, rightSide);
						break;
					}
				}
				if (conjunctionFormula == null) {
					conjunctionFormula = atomicGuardFormula;
				} else {
					conjunctionFormula = mScript.term("and", conjunctionFormula, atomicGuardFormula);
				}
			}
			if (conjunctionFormula == null) {
				conjunctionFormula = mScript.term("true");
			}
			if (dnfFormula == null) {
				dnfFormula = conjunctionFormula;
			} else {
				dnfFormula = mScript.term("or", dnfFormula, conjunctionFormula);
			}
		}
		if (dnfFormula == null) {
			dnfFormula = mScript.term("false");
		}
		return dnfFormula;
	}

	private Term updateToFormula(List<Update> updates, List<Counter> allCount, int step) {
		List<Counter> allCounters = new ArrayList<Counter>();
		allCounters.addAll(allCount);
		Term updateFormula, atomicUpdateFormula, leftCounterVariable, rightSide, constant, rightCounterVariable;
		updateFormula = null;
		for (Update update : updates) {
			atomicUpdateFormula = null;
			leftCounterVariable = mScript.variable(
					update.getCounterLeft().getCounterName() + "#" + String.valueOf(step + 1),
					SmtSortUtils.getIntSort(mScript));
			allCounters.remove(update.getCounterLeft());
			switch (update.getTermType()) {
			case CONSTANT:
				constant = mScript.numeral(BigInteger.valueOf(update.getConstant()));
				atomicUpdateFormula = mScript.term("=", leftCounterVariable, constant);
				break;
			case COUNTER:
				rightCounterVariable = mScript.variable(
						update.getCounterRight().getCounterName() + "#" + String.valueOf(step),
						SmtSortUtils.getIntSort(mScript));
				atomicUpdateFormula = mScript.term("=", leftCounterVariable, rightCounterVariable);
				break;
			case SUM:
				constant = mScript.numeral(BigInteger.valueOf(update.getConstant()));
				rightCounterVariable = mScript.variable(
						update.getCounterRight().getCounterName() + "#" + String.valueOf(step),
						SmtSortUtils.getIntSort(mScript));
				rightSide = mScript.term("+", constant, rightCounterVariable);
				atomicUpdateFormula = mScript.term("=", leftCounterVariable, rightSide);
				break;
			}
			if (updateFormula == null) {
				updateFormula = atomicUpdateFormula;
			} else {
				updateFormula = mScript.term("and", updateFormula, atomicUpdateFormula);
			}
		}
		for (Counter notUpdatedCounter : allCounters) {
			leftCounterVariable = mScript.variable(
					notUpdatedCounter.getCounterName() + "#" + String.valueOf(step + 1),
					SmtSortUtils.getIntSort(mScript));
			rightCounterVariable = mScript.variable(
					notUpdatedCounter.getCounterName() + "#" + String.valueOf(step),
					SmtSortUtils.getIntSort(mScript));
			atomicUpdateFormula = mScript.term("=", leftCounterVariable, rightCounterVariable);
			if (updateFormula == null) {
				updateFormula = atomicUpdateFormula;
			} else {
				updateFormula = mScript.term("and", updateFormula, atomicUpdateFormula);
			}
		}
		return updateFormula;
	}

	@Override
	public Object getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(CRSF stateFactory) throws AutomataLibraryException {
    // TODO: Check the result
		return true;
	}
}