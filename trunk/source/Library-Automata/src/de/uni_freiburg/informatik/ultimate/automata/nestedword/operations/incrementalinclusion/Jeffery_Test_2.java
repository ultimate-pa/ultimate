/*
 * Copyright (C) 2015 Jeffery Hsu (a71128@gmail.com)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Parameters are the same as IncrementalInclsuionCheck except for an extra integer parameter. The parameter is used to
 * assign which IncrementalInclusionCheck will be tested. Example: Testing IncrementalInclusionCheck2 ->
 * Jeffery_Test_2(Iservices, sf, a, b,2) Testing IncrementalInclusionCheck3 -> Jeffery_Test_2(Iservices, sf, a, b,3)...
 * 
 * @author jefferyyjhsu@iis.sinica.edu.tw
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class Jeffery_Test_2<LETTER, STATE> implements IOperation<LETTER, STATE, IStateFactory<STATE>> {

	private static ILogger mLogger;
	ArrayList<INestedWordAutomaton<LETTER, STATE>> automataCollection;
	Boolean result1, result2;

	public Jeffery_Test_2(final AutomataLibraryServices services, final IDeterminizeStateFactory<STATE> sf,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> a, final List<INwaOutgoingLetterAndTransitionProvider<LETTER, STATE>> b,
			final int num) throws AutomataLibraryException {
		switch (num) {
			default:
				break;
			case 2:
				result1 = new IncrementalInclusionCheck2<>(services, sf, a, b).getResult();
				final IncrementalInclusionCheck2<LETTER, STATE> IIC2 =
						new IncrementalInclusionCheck2<>(services, sf, a, b.subList(0, 1));
				for (int i = 1; i < b.size(); i++) {
					IIC2.addSubtrahend(b.get(i));
				}
				result2 = IIC2.getResult();
				break;
			case 3:
				result1 = new IncrementalInclusionCheck3<>(services, sf, a, b).getResult();
				final IncrementalInclusionCheck3<LETTER, STATE> IIC3 =
						new IncrementalInclusionCheck3<>(services, sf, a, b.subList(0, 1));
				for (int i = 1; i < b.size(); i++) {
					IIC3.addSubtrahend(b.get(i));
				}
				result2 = IIC3.getResult();
				break;
			case 4:
				result1 = new IncrementalInclusionCheck4<>(services, sf, a, b).getResult();
				final IncrementalInclusionCheck4<LETTER, STATE> IIC4 =
						new IncrementalInclusionCheck4<>(services, sf, a, b.subList(0, 1));
				for (int i = 1; i < b.size(); i++) {
					IIC4.addSubtrahend(b.get(i));
				}
				result2 = IIC4.getResult();
				break;
			case 5:
				result1 = new IncrementalInclusionCheck5<>(services, sf, a, b).getResult();
				final IncrementalInclusionCheck5<LETTER, STATE> IIC5 =
						new IncrementalInclusionCheck5<>(services, sf, a, b.subList(0, 1));
				for (int i = 1; i < b.size(); i++) {
					IIC5.addSubtrahend(b.get(i));
				}
				result2 = IIC5.getResult();
				break;
			case 32:
				result1 = new IncrementalInclusionCheck3_2<>(services, sf, a, b).getResult();
				final IncrementalInclusionCheck3_2<LETTER, STATE> IIC3_2 =
						new IncrementalInclusionCheck3_2<>(services, sf, a, b.subList(0, 1));
				for (int i = 1; i < b.size(); i++) {
					IIC3_2.addSubtrahend(b.get(i));
				}
				result2 = IIC3_2.getResult();
				break;
			case 42:
				result1 = new IncrementalInclusionCheck4_2<>(services, sf, a, b).getResult();
				final IncrementalInclusionCheck4_2<LETTER, STATE> IIC4_2 =
						new IncrementalInclusionCheck4_2<>(services, sf, a, b.subList(0, 1));
				for (int i = 1; i < b.size(); i++) {
					IIC4_2.addSubtrahend(b.get(i));
				}
				result2 = IIC4_2.getResult();
				break;
			case 52:
				result1 = new IncrementalInclusionCheck5_2<>(services, sf, a, b).getResult();
				final IncrementalInclusionCheck5_2<LETTER, STATE> IIC5_2 =
						new IncrementalInclusionCheck5_2<>(services, sf, a, b.subList(0, 1));
				for (int i = 1; i < b.size(); i++) {
					IIC5_2.addSubtrahend(b.get(i));
				}
				result2 = IIC5_2.getResult();
				break;
		}
	}

	@Override
	public String startMessage() {
		return "Start " + operationName();
	}

	@Override
	public String exitMessage() {
		return "Exit " + operationName();
	}

	@Override
	public Boolean getResult() {
		return result1.equals(result2);
	}
	/*
	 * public String getResult() throws OperationCanceledException { return
	 * "Jeffery_Test_2_result:"+automataCollection.size(); }
	 */

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}

}
