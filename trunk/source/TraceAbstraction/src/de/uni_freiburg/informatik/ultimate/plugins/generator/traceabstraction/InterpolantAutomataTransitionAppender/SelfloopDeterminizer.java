/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;


/**
 * Tradeoff between PowersetDeterminizer and BestApproximationDeterminizer.
 * Idea: Make a selfloop if inductive. If not inductive use PowersetDeterminizer
 * @author heizmann@informatik.uni-freiburg.de
 * 
 * TODO: For Call and Return this does not make much sense. Use there
 * generally the PowersetDeterminizer or the BestApproximationDeterminizer.
 */
public class SelfloopDeterminizer 
					implements IStateDeterminizer<CodeBlock, IPredicate> {

	IHoareTripleChecker m_HoareTriplechecker;
	PowersetDeterminizer<CodeBlock, IPredicate> m_PowersetDeterminizer;
	
	INestedWordAutomaton<CodeBlock, IPredicate> m_InterpolantAutomaton;
	private final StateFactory<IPredicate> m_StateFactory;
	IPredicate m_InterpolantAutomatonFinalState;
	
	DeterminizedState<CodeBlock, IPredicate> m_ResultFinalState;
	
	public int m_InternalSelfloop = 0;
	public int m_InternalNonSelfloop = 0;

	public int m_CallSelfloop = 0;
	public int m_CallNonSelfloop = 0;

	public int m_ReturnSelfloop = 0;
	public int m_ReturnNonSelfloop = 0;
	
	public SelfloopDeterminizer(SmtManager mSmtManager,
			TAPreferences taPreferences,
			INestedWordAutomaton<CodeBlock, IPredicate> interpolantAutom,
			StateFactory<IPredicate> stateFactory) {
		super();
		m_HoareTriplechecker = new MonolithicHoareTripleChecker(
				mSmtManager.getManagedScript(), mSmtManager.getModifiableGlobals());
		m_InterpolantAutomaton = interpolantAutom;
		m_StateFactory = stateFactory;
		m_PowersetDeterminizer = 
			new PowersetDeterminizer<CodeBlock, IPredicate>(m_InterpolantAutomaton, true, m_StateFactory);
		for (IPredicate state : m_InterpolantAutomaton.getStates()) {
			if (m_InterpolantAutomatonFinalState == null) {
				if (m_InterpolantAutomaton.isFinal(state)) {
					m_InterpolantAutomatonFinalState = state;
				}
			}
			else {
				throw new IllegalArgumentException("Interpolant Automaton" +
						" must have one final state");
			}
		}
		m_ResultFinalState = 
			new DeterminizedState<CodeBlock, IPredicate>(m_InterpolantAutomaton);
		m_ResultFinalState.addPair(m_InterpolantAutomaton.getEmptyStackState(),
											m_InterpolantAutomatonFinalState, m_InterpolantAutomaton);
	}
	
	@Override
	public DeterminizedState<CodeBlock, IPredicate> initialState() {
		return m_PowersetDeterminizer.initialState();
	}
	

	@Override
	public DeterminizedState<CodeBlock, IPredicate> internalSuccessor(
						DeterminizedState<CodeBlock, IPredicate> detState,
						CodeBlock symbol) {
		if (detState == m_ResultFinalState) {
			m_InternalSelfloop++;
			return m_ResultFinalState;
		}
		DeterminizedState<CodeBlock, IPredicate> powersetSucc = 
					m_PowersetDeterminizer.internalSuccessor(detState, symbol);
		if (containsFinal(powersetSucc)) {
			m_InternalNonSelfloop++;
			return m_ResultFinalState;
		}
		if (powersetSucc.isSubsetOf(detState)) {
			IPredicate detStateContent = getState(detState);
			Validity isInductive = m_HoareTriplechecker.checkInternal(detStateContent,
													   (IInternalAction) symbol, detStateContent);
			if (isInductive == Validity.VALID) {
				m_InternalSelfloop++;
				return detState;
			}
		}
		m_InternalNonSelfloop++;
		return powersetSucc;
	}
	

	@Override
	public DeterminizedState<CodeBlock, IPredicate> callSuccessor(
						DeterminizedState<CodeBlock, IPredicate> detState,
						CodeBlock symbol) {
		if (detState == m_ResultFinalState) {
			m_CallSelfloop++;
			return m_ResultFinalState;
		}
		DeterminizedState<CodeBlock, IPredicate> powersetSucc = 
					m_PowersetDeterminizer.callSuccessor(detState, symbol);
		if (containsFinal(powersetSucc)) {
			m_CallNonSelfloop++;
			return m_ResultFinalState;
		}
		if (powersetSucc.isSubsetOf(detState)) {
			IPredicate detStateContent = getState(detState);
			Validity isInductive = m_HoareTriplechecker.checkCall(detStateContent,
										   (Call) symbol, detStateContent);
			if (isInductive == Validity.VALID) {
				m_CallSelfloop++;
				return detState;
			}
		}
		m_CallNonSelfloop++;
		return powersetSucc;
	}


	@Override
	public DeterminizedState<CodeBlock, IPredicate> returnSuccessor(
			DeterminizedState<CodeBlock, IPredicate> detState,
			DeterminizedState<CodeBlock, IPredicate> derHier,
			CodeBlock symbol) {
		if (detState == m_ResultFinalState) {
			m_ReturnSelfloop++;
			return m_ResultFinalState;
		}
		if (derHier == m_ResultFinalState) {
			throw new AssertionError("I guess this never happens");
		}		
		DeterminizedState<CodeBlock, IPredicate> powersetSucc = 
			m_PowersetDeterminizer.returnSuccessor(detState, derHier, symbol);
		if (containsFinal(powersetSucc)) {
			m_ReturnNonSelfloop++;
			return m_ResultFinalState;
		}
		if (powersetSucc.isSubsetOf(detState)) {
			IPredicate detStateContent = getState(detState);
			IPredicate detHierContent = getState(derHier);
			Validity isInductive = m_HoareTriplechecker.checkReturn(detStateContent, 
						detHierContent, (Return) symbol, detStateContent);
			if (isInductive == Validity.VALID) {
				m_ReturnSelfloop++;
				return detState;
			}
		}
		m_ReturnNonSelfloop++;
		return powersetSucc;
	}
	

	
	
	private boolean containsFinal(
						DeterminizedState<CodeBlock, IPredicate> detState) {
		for (IPredicate down : detState.getDownStates()) {
			for (IPredicate up : detState.getUpStates(down)) {
				if (up == m_InterpolantAutomatonFinalState) {
					return true;
				}
			}
		}
		return false;
	}

	@Override
	public int getMaxDegreeOfNondeterminism() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public boolean useDoubleDeckers() {
		return true;
	}
	
	@Override
	public IPredicate getState(
			DeterminizedState<CodeBlock, IPredicate> determinizedState) {
		return determinizedState.getContent(m_StateFactory);
	}

}
