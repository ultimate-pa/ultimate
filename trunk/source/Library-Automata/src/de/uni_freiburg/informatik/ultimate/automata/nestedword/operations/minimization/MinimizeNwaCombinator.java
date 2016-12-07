/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 3 of the License,
 * or (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see
 * <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automata Library, or any covered work, by linking or combining it
 * with Eclipse RCP (or a modified version of Eclipse RCP), containing parts
 * covered by the terms of the Eclipse Public License, the licensors of the
 * ULTIMATE Automata Library grant you additional permission to convey the
 * resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.direct.nwa.ReduceNwaDirectSimulation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Minimization of nested word automata which wraps several minimization operations and uses one of them.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class MinimizeNwaCombinator<LETTER, STATE> extends AbstractMinimizeNwaDd<LETTER, STATE> {
	private static final String MAP_NOT_SUPPORTED_MESSAGE = "Map from old to new automaton is not supported with ";

	/**
	 * Possible minimization methods.
	 */
	public enum MinimizationMethods {
		/**
		 * Use {@link MinimizeSevpa}.
		 */
		SEVPA,
		/**
		 * Use {@link ShrinkNwa}.
		 */
		SHRINK_NWA,
		/**
		 * Use {@link MinimizeNwaMaxSat2}.
		 */
		NWA_MAX_SAT2,
		/**
		 * Use {@link ReduceNwaDirectSimulation}.
		 */
		NWA_RAQ_DIRECT,
		/**
		 * Use no minimization.
		 */
		NONE,
		/**
		 * Undefined mode.
		 */
		UNDEFINED;
	}
	
	public static final String UNDEFINED_ENUM_STATE_MESSAGE = "Undefined enum state.";
	
	// current minimization object (input automaton in case of no minimization)
	protected Object mBackingMinimization;
	// current minimization method
	protected MinimizationMethods mMode;
	
	protected MinimizeNwaCombinator(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final String name, final IDoubleDeckerAutomaton<LETTER, STATE> operand) {
		super(services, stateFactory, name, operand);
		mMode = MinimizationMethods.UNDEFINED;
	}
	
	/**
	 * This method must be called by all implementing subclasses at the end of the constructor.
	 */
	protected final void run(final Collection<Set<STATE>> partition,
			final boolean addMapOldState2newState) throws AutomataOperationCanceledException {
		switch (mMode) {
			case SEVPA:
				mBackingMinimization = new MinimizeSevpa<>(mServices, mOperand,
						partition, mStateFactory, addMapOldState2newState, false);
				break;
			case SHRINK_NWA:
				mBackingMinimization = new ShrinkNwa<>(mServices, mStateFactory,
						mOperand, partition, addMapOldState2newState, false,
						false, ShrinkNwa.SUGGESTED_RANDOM_SPLIT_SIZE, false, 0, false, false, true, false);
				break;
			case NWA_MAX_SAT2:
				mBackingMinimization = new MinimizeNwaMaxSat2<>(mServices, mStateFactory,
						(IDoubleDeckerAutomaton<LETTER, STATE>) mOperand, addMapOldState2newState, partition);
				break;
			case NWA_RAQ_DIRECT:
				checkForNoMapping(addMapOldState2newState);
				mBackingMinimization = new ReduceNwaDirectSimulation<>(mServices, mStateFactory,
						(IDoubleDeckerAutomaton<LETTER, STATE>) mOperand, false, partition);
				break;
			case NONE:
				if (mLogger.isInfoEnabled()) {
					mLogger.info("No minimization is used.");
				}
				mBackingMinimization = mOperand;
				break;
			default:
				throw new IllegalArgumentException(UNDEFINED_ENUM_STATE_MESSAGE);
		}
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public final IDoubleDeckerAutomaton<LETTER, STATE> getResult() {
		switch (mMode) {
			case SEVPA:
				return (IDoubleDeckerAutomaton<LETTER, STATE>) ((MinimizeSevpa<LETTER, STATE>) mBackingMinimization)
						.getResult();
			case SHRINK_NWA:
				return (IDoubleDeckerAutomaton<LETTER, STATE>) ((ShrinkNwa<LETTER, STATE>) mBackingMinimization)
						.getResult();
			case NWA_MAX_SAT2:
				return ((MinimizeNwaMaxSat2<LETTER, STATE>) mBackingMinimization).getResult();
			case NWA_RAQ_DIRECT:
				return (IDoubleDeckerAutomaton<LETTER, STATE>) ((ReduceNwaDirectSimulation<LETTER, STATE>) mBackingMinimization)
						.getResult();
			case NONE:
				return (IDoubleDeckerAutomaton<LETTER, STATE>) mBackingMinimization;
			default:
				throw new IllegalArgumentException(UNDEFINED_ENUM_STATE_MESSAGE);
		}
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public final Map<STATE, STATE> getOldState2newState() {
		switch (mMode) {
			case SEVPA:
				return ((MinimizeSevpa<LETTER, STATE>) mBackingMinimization).getOldState2newState();
			case SHRINK_NWA:
				return ((ShrinkNwa<LETTER, STATE>) mBackingMinimization).getOldState2newState();
			case NWA_MAX_SAT2:
				return ((MinimizeNwaMaxSat2<LETTER, STATE>) mBackingMinimization).getOldState2newState();
			case NWA_RAQ_DIRECT:
				throw new UnsupportedOperationException(MAP_NOT_SUPPORTED_MESSAGE + mMode);
			case NONE:
				throw new IllegalArgumentException("Do not ask for Hoare annotation if no minimization was used.");
			default:
				throw new IllegalArgumentException(UNDEFINED_ENUM_STATE_MESSAGE);
		}
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public final boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		switch (mMode) {
			case SEVPA:
				return ((MinimizeSevpa<LETTER, STATE>) mBackingMinimization).checkResult(stateFactory);
			case SHRINK_NWA:
				return ((ShrinkNwa<LETTER, STATE>) mBackingMinimization).checkResult(stateFactory);
			case NWA_MAX_SAT2:
				return ((MinimizeNwaMaxSat2<LETTER, STATE>) mBackingMinimization).checkResult(stateFactory);
			case NWA_RAQ_DIRECT:
				return ((ReduceNwaDirectSimulation<LETTER, STATE>) mBackingMinimization).checkResult(stateFactory);
			case NONE:
				return true;
			default:
				throw new IllegalArgumentException(UNDEFINED_ENUM_STATE_MESSAGE);
		}
	}
	
	private void checkForNoMapping(final boolean addMapOldState2newState) {
		if (addMapOldState2newState) {
			throw new IllegalArgumentException(MAP_NOT_SUPPORTED_MESSAGE + mMode);
		}
	}

	public MinimizationMethods getMode() {
		return mMode;
	}
	
	
}
