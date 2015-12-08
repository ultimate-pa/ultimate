/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
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
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.TightLevelRankingStateGeneratorBuilder.FkvOptimization;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;

	

/**
 * Buchi Complementation based on 
 * 2004ATVA - Friedgut,Kupferman,Vardi - Büchi Complementation Made Tighter
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BuchiComplementFKV<LETTER,STATE> implements IOperation<LETTER,STATE> {
	
	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	
	/**
	 * TODO Allow definition of a maximal rank for cases where you know that
	 * this is sound. E.g. if the automaton is reverse deterministic a maximal
	 * rank of 2 is suffient, see paper of Seth Forgaty.
	 */
	private final int m_UserDefinedMaxRank;
	
	private final INestedWordAutomatonSimple<LETTER,STATE> m_Operand;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> m_Result;
	private final StateFactory<STATE> m_StateFactory;
	private final IStateDeterminizer<LETTER, STATE> m_StateDeterminizer;
	private final BuchiComplementFKVNwa<LETTER, STATE> m_Complemented;
	private final FkvOptimization m_Optimization;	
	
	
	
	@Override
	public String operationName() {
		return "buchiComplementFKV";
	}
	
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + " with optimization " + m_Optimization 
				+ ". Operand " +	m_Operand.sizeInformation();
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " with optimization " + m_Optimization 
				+ ". Operand " + 
				m_Operand.sizeInformation() + " Result " + 
				m_Result.sizeInformation() + 
				m_Complemented.getPowersetStates() + " powerset states" +
				m_Complemented.getRankStates() + " rank states" +
			" the highest rank that occured is " + m_Complemented.getHighesRank();
	}
	
	public int getHighestRank() {
		return m_Complemented.getHighesRank();
	}

	public BuchiComplementFKV(IUltimateServiceProvider services,
			StateFactory<STATE> stateFactory, 
			INestedWordAutomatonSimple<LETTER,STATE> input,
			String optimization,
			int userDefinedMaxRank) throws AutomataLibraryException {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		this.m_StateDeterminizer = new PowersetDeterminizer<LETTER, STATE>(input, true, stateFactory);
		this.m_StateFactory = input.getStateFactory();
		this.m_Operand = input;
		this.m_UserDefinedMaxRank = userDefinedMaxRank;
		this.m_Optimization = FkvOptimization.valueOf(optimization);
		m_Logger.info(startMessage());
		m_Complemented = new BuchiComplementFKVNwa<LETTER, STATE>(m_Services, input,m_StateDeterminizer,m_StateFactory, m_Optimization, m_UserDefinedMaxRank);
		m_Result = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Services, m_Complemented);
		m_Logger.info(exitMessage());
	}
	
	public BuchiComplementFKV(IUltimateServiceProvider services,
			StateFactory<STATE> stateFactory, 
			INestedWordAutomatonSimple<LETTER,STATE> input) throws AutomataLibraryException {
		this(services, stateFactory, input, FkvOptimization.HeiMat2.toString(), Integer.MAX_VALUE);
		
	}
	
	public BuchiComplementFKV(IUltimateServiceProvider services,
			INestedWordAutomatonSimple<LETTER,STATE> input, IStateDeterminizer<LETTER, STATE> stateDeterminizier) throws AutomataLibraryException {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		this.m_StateDeterminizer = stateDeterminizier;
		this.m_StateFactory = input.getStateFactory();
		this.m_Operand = input;
		this.m_UserDefinedMaxRank = Integer.MAX_VALUE;
		this.m_Optimization = FkvOptimization.HeiMat2;
		m_Logger.info(startMessage());
		m_Complemented = new BuchiComplementFKVNwa<LETTER, STATE>(m_Services, input,m_StateDeterminizer,m_StateFactory, m_Optimization, m_UserDefinedMaxRank);
		m_Result = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Services, m_Complemented);
		m_Logger.info(exitMessage());
	}
	
	
	
	


	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		boolean underApproximationOfComplement = false;
		boolean correct = true;
		m_Logger.info("Start testing correctness of " + operationName());
		INestedWordAutomatonOldApi<LETTER, STATE> operandOldApi = 
				ResultChecker.getOldApiNwa(m_Services, m_Operand);
		List<NestedLassoWord<LETTER>> lassoWords = new ArrayList<NestedLassoWord<LETTER>>();
		BuchiIsEmpty<LETTER, STATE> operandEmptiness = new BuchiIsEmpty<LETTER, STATE>(m_Services, operandOldApi);
		boolean operandEmpty = operandEmptiness.getResult();
		if (!operandEmpty) {
			lassoWords.add(operandEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		BuchiIsEmpty<LETTER, STATE> resultEmptiness = new BuchiIsEmpty<LETTER, STATE>(m_Services, m_Result);
		boolean resultEmpty = resultEmptiness.getResult();
		if (!resultEmpty) {
			lassoWords.add(resultEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		correct &= !(operandEmpty && resultEmpty);
		assert correct;
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, m_Result.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, m_Result.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, operandOldApi.size()));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 1));
		lassoWords.addAll((new LassoExtractor<LETTER, STATE>(m_Services, operandOldApi)).getResult());
		lassoWords.addAll((new LassoExtractor<LETTER, STATE>(m_Services, m_Result)).getResult());

		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(m_Result, 2));
		

		for (NestedLassoWord<LETTER> nlw : lassoWords) {
			boolean thistime = checkAcceptance(nlw, operandOldApi, underApproximationOfComplement);
			if (!thistime) {
				thistime = checkAcceptance(nlw, operandOldApi, underApproximationOfComplement);
			}
			correct &= thistime;
//			assert correct;
		}

		if (!correct) {
			ResultChecker.writeToFileIfPreferred(m_Services, operationName() + "Failed", "", m_Operand);
			ResultChecker.writeToFileIfPreferred(m_Services, operationName() + "FailedRes", "", m_Result);
		}
		m_Logger.info("Finished testing correctness of " + operationName());
		return correct;
	}
	
	
	private boolean checkAcceptance(NestedLassoWord<LETTER> nlw,
			INestedWordAutomatonOldApi<LETTER, STATE> operand , 
			boolean underApproximationOfComplement) throws AutomataLibraryException {
		boolean op = (new BuchiAccepts<LETTER, STATE>(m_Services, operand, nlw)).getResult();
		boolean res = (new BuchiAccepts<LETTER, STATE>(m_Services, m_Result, nlw)).getResult();
		boolean correct;
		if (underApproximationOfComplement) {
			correct = !res || op;
		} else {
			correct = op ^ res;
		}
//		assert correct : operationName() + " wrong result!";
		return correct;
	}


	@Override
	public NestedWordAutomatonReachableStates<LETTER, STATE> getResult() throws AutomataLibraryException {
		return m_Result;
	}

}
