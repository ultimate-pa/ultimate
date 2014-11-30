/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DoubleDeckerVisitor;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;


/**
 * Check if an NWA contains states which are not reachable in any run.
 * Does not change the input automaton.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class HasUnreachableStates<LETTER,STATE> extends DoubleDeckerVisitor<LETTER,STATE>
										   implements IOperation<LETTER,STATE> {
	private static Logger s_Logger = 
			NestedWordAutomata.getLogger();
	
	
	private final Set<STATE> m_VisitedStates = new HashSet<STATE>();
	private int m_UnreachalbeStates = 0;

	
	public HasUnreachableStates(IUltimateServiceProvider services,
			INestedWordAutomatonOldApi<LETTER,STATE> operand) throws OperationCanceledException {
		super(services);
		m_TraversedNwa = operand;
		s_Logger.info(startMessage());
		traverseDoubleDeckerGraph();
		for (STATE state : m_TraversedNwa.getStates()) {
			if (!m_VisitedStates.contains(state)) {
				m_UnreachalbeStates++;
				s_Logger.warn("Unreachalbe state: " + state);
			}
		}
		s_Logger.info(exitMessage());
	}

	@Override
	protected Collection<STATE> getInitialStates() {
		m_VisitedStates.addAll(m_TraversedNwa.getInitialStates());
		return m_TraversedNwa.getInitialStates();
	}

	@Override
	protected Collection<STATE> visitAndGetInternalSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		STATE state = doubleDecker.getUp();
		Set<STATE> succs = new HashSet<STATE>();
		for (LETTER letter : m_TraversedNwa.lettersInternal(state)) {
			for (STATE succ : m_TraversedNwa.succInternal(state, letter)) {
				succs.add(succ);
			}
		}
		m_VisitedStates.addAll(succs);
		return succs;
	}
	
	

	@Override
	protected Collection<STATE> visitAndGetCallSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		STATE state = doubleDecker.getUp();
		Set<STATE> succs = new HashSet<STATE>();
		for (LETTER letter : m_TraversedNwa.lettersCall(state)) {
			for (STATE succ : m_TraversedNwa.succCall(state, letter)) {
				succs.add(succ);
			}
		}
		m_VisitedStates.addAll(succs);
		return succs;
	}
	
	

	@Override
	protected Collection<STATE> visitAndGetReturnSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		STATE state = doubleDecker.getUp();
		STATE hier = doubleDecker.getDown();
		Set<STATE> succs = new HashSet<STATE>();
		for (LETTER letter : m_TraversedNwa.lettersReturn(state)) {
			for (STATE succ : m_TraversedNwa.succReturn(state, hier, letter)) {
				succs.add(succ);
			}
		}
		m_VisitedStates.addAll(succs);
		return succs;
	}

	@Override
	public String operationName() {
		return "detectUnreachableStates";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + 
			m_TraversedNwa.sizeInformation();
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Operand has " + 
			m_UnreachalbeStates + " unreachalbe states";
	}
	
	public boolean result() {
		return m_UnreachalbeStates != 0;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return true;
	}
	

}
