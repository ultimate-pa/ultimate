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
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * Complement method for Counting Automata
 * Needs a deterministic Automaton as Input
 *
 * @author Jacob Maxam
 */

public class Acceptance<LETTER, STATE, CRSF extends IStateFactory<STATE>> implements IOperation<LETTER, STATE, CRSF> {

	private final AutomataLibraryServices mServices;
	private final Script mScript;
	private final ILogger mLogger;
	private final CountingAutomaton<LETTER, STATE> mOperand;
	private final List<LETTER> mWord;
	private final boolean mResult;
	//private final IIntersectionStateFactory<STATE> mStateFactory;


	public Acceptance(
			final AutomataLibraryServices services, 
			final CountingAutomaton<LETTER, STATE> operand,
			final List<LETTER> word) throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(this.getClass());
		mOperand = operand;
		mWord = word;
		mScript = new SMTInterpol();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mResult = computeResult();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}
	
	private boolean computeResult() {
		return false;
	}
	
	private boolean iterativeAcceptance(CountingAutomaton<LETTER, STATE> ca, List<List<Guard>> preConditions, List<LETTER> word) {
		
		return false;
	}


	private Term dnfToFormula(List<List<Guard>> dnf){
		Term dnfFormula, conjunctionFormula, atomicGuardFormula, leftCounterVariable, rightSide, rightCounterVariable, constant;
		dnfFormula = null;
		for (List<Guard> guardList : dnf) {
			conjunctionFormula = null;
			for (Guard guard : guardList) {
				atomicGuardFormula = null;
				leftCounterVariable = null;
				rightSide = null;
				switch (guard.getTermType()) {
				case TRUE :
					//?
					break;
				case FALSE:
					//?
					break;
				case CONSTANT:
					leftCounterVariable = mScript.variable(guard.getCounterLeft().getCounterName(), SmtSortUtils.getIntSort(mScript));
					rightSide = mScript.numeral(BigInteger.valueOf(guard.getConstant()));
					break;
				case COUNTER:
					leftCounterVariable = mScript.variable(guard.getCounterLeft().getCounterName(), SmtSortUtils.getIntSort(mScript));
					rightSide = mScript.variable(guard.getCounterRight().getCounterName(), SmtSortUtils.getIntSort(mScript));
					break;
				case SUM:
					leftCounterVariable = mScript.variable(guard.getCounterLeft().getCounterName(), SmtSortUtils.getIntSort(mScript));
					rightCounterVariable = mScript.variable(guard.getCounterRight().getCounterName(), SmtSortUtils.getIntSort(mScript));
					constant = mScript.numeral(BigInteger.valueOf(guard.getConstant()));
					rightSide = mScript.term("+", rightCounterVariable, constant);
					break;
				}
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
				if (conjunctionFormula == null) {
					conjunctionFormula = atomicGuardFormula;
				} else {
					conjunctionFormula = mScript.term("and", conjunctionFormula, atomicGuardFormula);
				}
			}
			if (dnfFormula == null) {
				dnfFormula = conjunctionFormula;
			} else {
				dnfFormula = mScript.term("and", dnfFormula, conjunctionFormula);
			}
		}
		return dnfFormula;
	}

	
	@Override
	public Object getResult() {
		return mResult;
	}


	@Override
	public boolean checkResult(CRSF stateFactory) throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return false;
	}
}