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

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Date;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * compare speed between difference and IncrementalInclusionCheck4. If one algorithm is 10 times slower than the other
 * one, the automaton being used will be dumped to a folder which can be assigned by one of the constructor's
 * parameters.
 * 
 * @author jefferyyjhsu@iis.sinica.edu.tw
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class Jeffery_Test_4<LETTER, STATE> implements IOperation<LETTER, STATE, IStateFactory<STATE>> {
	static long faster_i = 0, slower_i = 0;
	static long timeBuffer1, timeBuffer2;
	String folder;

	public Jeffery_Test_4(final AutomataLibraryServices services, final IIncrementalInclusionStateFactory<STATE> sf,
			final INestedWordAutomatonSimple<LETTER, STATE> a, final List<INestedWordAutomatonSimple<LETTER, STATE>> b)
			throws AutomataLibraryException, IOException {
		folder = "/media/user_data/Java/trunk/examples/Automata/finiteAutomata/incrementalInclusion/randomCasesDumpedResults/";
		timeBuffer1 = new Date().getTime();
		final IncrementalInclusionCheckDifference<LETTER, STATE, ?> IIC1 =
				new IncrementalInclusionCheckDifference<>(services, sf, a, b.subList(0, 1));
		for (int i = 1; i < b.size(); i++) {
			IIC1.addSubtrahend(b.get(i));
		}
		timeBuffer1 = new Date().getTime() - timeBuffer1;
		timeBuffer2 = new Date().getTime();
		final IncrementalInclusionCheck4<LETTER, STATE> IIC4 =
				new IncrementalInclusionCheck4<>(services, sf, a, b.subList(0, 1));
		for (int i = 1; i < b.size(); i++) {
			IIC4.addSubtrahend(b.get(i));
		}
		timeBuffer2 = new Date().getTime() - timeBuffer2;
		long x = new Long(timeBuffer1), y = new Long(timeBuffer2);
		if (x == 0) {
			x = 1;
		}
		if (y == 0) {
			y = 1;
		}
		if (y > x * 10) {
			final FileWriter fw = new FileWriter(folder + "faster_" + faster_i + ".ats");
			faster_i++;
			final BufferedWriter bw = new BufferedWriter(fw);
			bw.write("//Result:" + IIC1.getResult());
			bw.newLine();
			bw.write("//Difference: Time:" + timeBuffer1 + " Total states:" + IIC1.size());
			bw.newLine();
			bw.write("//IncrementalInclusionCheck4: Time:" + timeBuffer2 + " Total states:" + IIC4.counter_total_nodes
					+ " States in the end:" + IIC4.completeLeafSet.size() + " Run:" + IIC4.counter_run);
			bw.newLine();
			bw.write(new AutomatonDefinitionPrinter<String, String>(services, "A", Format.ATS, a)
					.getDefinitionAsString());
			bw.newLine();
			int i;
			for (i = 0; i < b.size(); i++) {
				bw.write(new AutomatonDefinitionPrinter<String, String>(services, "B" + i, Format.ATS, b.get(i))
						.getDefinitionAsString());
				bw.newLine();
			}
			bw.close();
			fw.close();
		} else if (x > y * 10) {
			final FileWriter fw = new FileWriter(folder + "slower_" + slower_i + ".ats");
			slower_i++;
			final BufferedWriter bw = new BufferedWriter(fw);
			bw.write("//Result:" + IIC1.getResult());
			bw.newLine();
			bw.write("//Difference: Time:" + timeBuffer1 + " Total states:" + IIC1.size());
			bw.newLine();
			bw.write("//IncrementalInclusionCheck4: Time:" + timeBuffer2 + " Total states:" + IIC4.counter_total_nodes
					+ " States in the end:" + IIC4.completeLeafSet.size() + " Run:" + IIC4.counter_run);
			bw.newLine();
			bw.write(new AutomatonDefinitionPrinter<String, String>(services, "A", Format.ATS, a)
					.getDefinitionAsString());
			bw.newLine();
			int i;
			for (i = 0; i < b.size(); i++) {
				bw.write(new AutomatonDefinitionPrinter<String, String>(services, "B" + i, Format.ATS, b.get(i))
						.getDefinitionAsString());
				bw.newLine();
			}
			bw.close();
			fw.close();
		}

	}

	public Jeffery_Test_4(final AutomataLibraryServices services, final IIncrementalInclusionStateFactory<STATE> sf,
			final INestedWordAutomatonSimple<LETTER, STATE> a, final List<INestedWordAutomatonSimple<LETTER, STATE>> b,
			final String folderInput) throws AutomataLibraryException, IOException {
		folder = folderInput;
		timeBuffer1 = new Date().getTime();
		final IncrementalInclusionCheckDifference<LETTER, STATE, ?> IIC1 =
				new IncrementalInclusionCheckDifference<>(services, sf, a, b.subList(0, 1));
		for (int i = 1; i < b.size(); i++) {
			IIC1.addSubtrahend(b.get(i));
		}
		timeBuffer1 = new Date().getTime() - timeBuffer1;
		timeBuffer2 = new Date().getTime();
		final IncrementalInclusionCheck4<LETTER, STATE> IIC4 =
				new IncrementalInclusionCheck4<>(services, sf, a, b.subList(0, 1));
		for (int i = 1; i < b.size(); i++) {
			IIC4.addSubtrahend(b.get(i));
		}
		timeBuffer2 = new Date().getTime() - timeBuffer2;
		long x = new Long(timeBuffer1), y = new Long(timeBuffer2);
		if (x == 0) {
			x = 1;
		}
		if (y == 0) {
			y = 1;
		}
		if (y > x * 10) {
			final FileWriter fw = new FileWriter(folder + "faster_" + faster_i + ".ats");
			faster_i++;
			final BufferedWriter bw = new BufferedWriter(fw);
			bw.write("//Result:" + IIC1.getResult());
			bw.newLine();
			bw.write("//Difference: Time:" + timeBuffer1 + " Total states:" + IIC1.size());
			bw.newLine();
			bw.write("//IncrementalInclusionCheck4: Time:" + timeBuffer2 + " Total states:" + IIC4.counter_total_nodes
					+ " States in the end:" + IIC4.completeLeafSet.size() + " Run:" + IIC4.counter_run);
			bw.newLine();
			bw.write(new AutomatonDefinitionPrinter<String, String>(services, "A", Format.ATS, a)
					.getDefinitionAsString());
			bw.newLine();
			int i;
			for (i = 0; i < b.size(); i++) {
				bw.write(new AutomatonDefinitionPrinter<String, String>(services, "B" + i, Format.ATS, b.get(i))
						.getDefinitionAsString());
				bw.newLine();
			}
			bw.close();
			fw.close();
		} else if (x > y * 10) {
			final FileWriter fw = new FileWriter(folder + "slower_" + slower_i + ".ats");
			slower_i++;
			final BufferedWriter bw = new BufferedWriter(fw);
			bw.write("//Result:" + IIC1.getResult());
			bw.newLine();
			bw.write("//Difference: Time:" + timeBuffer1 + " Total states:" + IIC1.size());
			bw.newLine();
			bw.write("//IncrementalInclusionCheck4: Time:" + timeBuffer2 + " Total states:" + IIC4.counter_total_nodes
					+ " States in the end:" + IIC4.completeLeafSet.size() + " Run:" + IIC4.counter_run);
			bw.newLine();
			bw.write(new AutomatonDefinitionPrinter<String, String>(services, "A", Format.ATS, a)
					.getDefinitionAsString());
			bw.newLine();
			int i;
			for (i = 0; i < b.size(); i++) {
				bw.write(new AutomatonDefinitionPrinter<String, String>(services, "B" + i, Format.ATS, b.get(i))
						.getDefinitionAsString());
				bw.newLine();
			}
			bw.close();
			fw.close();
		}

	}

	@Override
	public String operationName() {
		return "Jeffery_Test_4";
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
	public String getResult() {
		final String log = "Output cases:\r\nfaster:" + faster_i + "\r\nslower:" + slower_i;
		return log;
	}
	/*
	 * public String getResult() throws OperationCanceledException { return
	 * "Jeffery_Test_4_result:"+automataCollection.size(); }
	 */

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}

}
