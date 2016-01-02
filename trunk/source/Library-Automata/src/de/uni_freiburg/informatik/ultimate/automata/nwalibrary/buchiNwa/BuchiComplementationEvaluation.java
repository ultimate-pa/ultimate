/*
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.LevelRankingGenerator.FkvOptimization;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveNonLiveStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;

	

/**
 * Auxiliary class for doing some benchmarks
 * @author heizmann@informatik.uni-freiburg.de
 */
public class BuchiComplementationEvaluation<LETTER,STATE> implements IOperation<LETTER,STATE> {
	
	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	
	private final INestedWordAutomaton<LETTER,STATE> m_Operand;
	private final String m_Result;
	
	
	
	@Override
	public String operationName() {
		return "BuchiComplementationEvaluation";
	}
	
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + 
			m_Operand.sizeInformation();
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Operand " + 
				m_Operand.sizeInformation() + " Result " + 
				m_Result;
	}
	
	public BuchiComplementationEvaluation(IUltimateServiceProvider services,
			StateFactory<STATE> stateFactory, 
			INestedWordAutomatonSimple<LETTER,STATE> input) throws AutomataLibraryException {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		this.m_Operand = new NestedWordAutomatonReachableStates<>(m_Services, input);
		m_Logger.info(startMessage());
		m_Result = evaluate(stateFactory);
		m_Logger.info(exitMessage());
	}
	


	private String evaluate(StateFactory<STATE> stateFactory) throws AutomataLibraryException {
		LinkedHashMap<String, Integer> results = new LinkedHashMap<>();
		{
			String name = "BuchiComplementBS";
			NestedWordAutomatonReachableStates<LETTER, STATE> result = (new BuchiComplementNCSB<LETTER, STATE>(m_Services, stateFactory, m_Operand)).getResult();
			addToResultsWithSizeReduction(results, name, result);
		}
		for (FkvOptimization fkvOptimization : FkvOptimization.values()) {
			{
				String name = "FKV_" + fkvOptimization;
				NestedWordAutomatonReachableStates<LETTER, STATE> result = (new BuchiComplementFKV<LETTER, STATE>(m_Services, stateFactory, m_Operand, fkvOptimization.toString(), Integer.MAX_VALUE)).getResult();
				addToResultsWithSizeReduction(results, name, result);
			}
			{
				String name = "FKV_" + fkvOptimization + "_MaxRank3";
				NestedWordAutomatonReachableStates<LETTER, STATE> result = (new BuchiComplementFKV<LETTER, STATE>(m_Services, stateFactory, m_Operand, fkvOptimization.toString(), 3)).getResult();
				addToResultsWithSizeReduction(results, name, result);
			}
		}
		return prettyPrint(results);
	}


	private String prettyPrint(LinkedHashMap<String, Integer> results) {
		StringBuilder sb = new StringBuilder();
		for (Entry<String, Integer> entry : results.entrySet()) {
			sb.append(entry.getKey());
			sb.append(" ");
			sb.append(entry.getValue());
			sb.append(System.lineSeparator());
		}
		return sb.toString();
	}


	private void addToResultsWithSizeReduction(LinkedHashMap<String, Integer> results,
			String name,
			NestedWordAutomatonReachableStates<LETTER, STATE> result) throws AutomataLibraryException {
		addToResults(results, name, result);
		INestedWordAutomatonOldApi<LETTER, STATE> nl = (new RemoveNonLiveStates<LETTER, STATE>(m_Services, result)).getResult();
		addToResults(results, name + "_nonLiveRemoved", nl);
		INestedWordAutomaton<LETTER, STATE> bc = (new BuchiClosure<>(m_Services, nl)).getResult();
		NestedWordAutomatonReachableStates<LETTER, STATE> bcru = (new RemoveUnreachable<LETTER, STATE>(m_Services, bc)).getResult();
		INestedWordAutomatonOldApi<LETTER, STATE> minmized = (new MinimizeSevpa<LETTER, STATE>(m_Services, bcru)).getResult();
		addToResults(results, name + "_MsSizeReduction", minmized);
	}
	
	private void addToResults(LinkedHashMap<String, Integer> results,
			String name,
			INestedWordAutomaton<LETTER, STATE> result) {
		int size = result.getStates().size();
		results.put(name, size);
	}


	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return true;
	}
	
	
	@Override
	public String getResult() throws AutomataLibraryException {
		return m_Result;
	}
















}
