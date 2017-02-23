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
import java.util.Date;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Parameters are the same as IncrementalInclsuionCheck except for an extra integer parameter. The parameter is used to
 * assign which IncrementalInclusionCheck will be tested. Example: Testing IncrementalInclusionCheck2 ->
 * Jeffery_Test_3(Iservices, sf, a, b,2) Testing IncrementalInclusionCheck3 -> Jeffery_Test_3(Iservices, sf, a, b,3)...
 * 
 * @author jefferyyjhsu@iis.sinica.edu.tw
 * @param <LETTER>
 * @param <STATE>
 */

public class Jeffery_Test_3<LETTER, STATE> implements IOperation<LETTER, STATE, IStateFactory<STATE>> {
	static long trueSumNodeInTheEnd1 = 0, trueSumNodeInTheEnd2 = 0, trueSumNodeInTheEnd3 = 0, trueSumNodeInTheEnd4 = 0,
			trueSumNodeInTheEnd5 = 0, trueSumNodeInTheEnd32 = 0, trueSumNodeInTheEnd42 = 0, trueSumNodeInTheEnd52 = 0;
	static long trueSumTotalNode1 = 0, trueSumTotalNode2 = 0, trueSumTotalNode3 = 0, trueSumTotalNode4 = 0,
			trueSumTotalNode5 = 0, trueSumTotalNode32 = 0, trueSumTotalNode42 = 0, trueSumTotalNode52 = 0;
	static long trueSumRun2 = 0, trueSumRun3 = 0, trueSumRun4 = 0, trueSumRun5 = 0, trueSumRun32 = 0, trueSumRun42 = 0,
			trueSumRun52 = 0;
	static long trueTestnum1 = 0, trueTestnum2 = 0, trueTestnum3 = 0, trueTestnum4 = 0, trueTestnum5 = 0,
			trueTestnum32 = 0, trueTestnum42 = 0, trueTestnum52 = 0;
	static long trueTime1 = 0, trueTime2 = 0, trueTime3 = 0, trueTime4 = 0, trueTime5 = 0, trueTime32 = 0,
			trueTime42 = 0, trueTime52 = 0, timeBuffer;
	static long falseSumNodeInTheEnd1 = 0, falseSumNodeInTheEnd2 = 0, falseSumNodeInTheEnd3 = 0,
			falseSumNodeInTheEnd4 = 0, falseSumNodeInTheEnd5 = 0, falseSumNodeInTheEnd32 = 0,
			falseSumNodeInTheEnd42 = 0, falseSumNodeInTheEnd52 = 0;
	static long falseSumTotalNode1 = 0, falseSumTotalNode2 = 0, falseSumTotalNode3 = 0, falseSumTotalNode4 = 0,
			falseSumTotalNode5 = 0, falseSumTotalNode32 = 0, falseSumTotalNode42 = 0, falseSumTotalNode52 = 0;
	static long falseSumRun2 = 0, falseSumRun3 = 0, falseSumRun4 = 0, falseSumRun5 = 0, falseSumRun32 = 0,
			falseSumRun42 = 0, falseSumRun52 = 0;
	static long falseTestnum1 = 0, falseTestnum2 = 0, falseTestnum3 = 0, falseTestnum4 = 0, falseTestnum5 = 0,
			falseTestnum32 = 0, falseTestnum42 = 0, falseTestnum52 = 0;
	static long falseTime1 = 0, falseTime2 = 0, falseTime3 = 0, falseTime4 = 0, falseTime5 = 0, falseTime32 = 0,
			falseTime42 = 0, falseTime52 = 0;
	static long trueAvgNodeInTheEnd = 0, trueAvgNodeGenerated = 0, trueAvgRun = 0, trueTestNum = 0, trueAvgTime = 0;
	static long falseAvgNodeInTheEnd = 0, falseAvgNodeGenerated = 0, falseAvgRun = 0, falseTestNum = 0,
			falseAvgTime = 0;
	ArrayList<INestedWordAutomaton<LETTER, STATE>> automataCollection;
	private static ILogger mLogger;

	public Jeffery_Test_3(final AutomataLibraryServices services, final IIncrementalInclusionStateFactory<STATE> sf,
			final INestedWordAutomatonSimple<LETTER, STATE> a, final List<INestedWordAutomatonSimple<LETTER, STATE>> b,
			final int num) throws AutomataLibraryException {

		switch (num) {
			default:

			case 1:
				timeBuffer = new Date().getTime();
				final IncrementalInclusionCheckDifference<LETTER, STATE, ?> IIC1 =
						new IncrementalInclusionCheckDifference<>(services, sf, a, b.subList(0, 1));
				for (int i = 1; i < b.size(); i++) {
					IIC1.addSubtrahend(b.get(i));
				}
				timeBuffer = new Date().getTime() - timeBuffer;
				if (IIC1.getResult()) {
					trueTime1 += timeBuffer;
					trueTestnum1++;
					trueSumTotalNode1 += IIC1.size();
					trueSumNodeInTheEnd1 += IIC1.size();
				} else {
					falseTime1 += timeBuffer;
					falseTestnum1++;
					falseSumTotalNode1 += IIC1.size();
					falseSumNodeInTheEnd1 += IIC1.size();
				}
				if (trueTestnum1 != 0) {
					trueAvgNodeInTheEnd = trueSumNodeInTheEnd1 / trueTestnum1;
					trueAvgNodeGenerated = trueSumTotalNode1 / trueTestnum1;
					trueAvgRun = 0;
					trueTestNum = trueTestnum1;
					trueAvgTime = trueTime1 / trueTestnum1;
				}
				if (falseTestnum1 != 0) {
					falseAvgNodeInTheEnd = falseSumNodeInTheEnd1 / falseTestnum1;
					falseAvgNodeGenerated = falseSumTotalNode1 / falseTestnum1;
					falseAvgRun = 0;
					falseTestNum = falseTestnum1;
					falseAvgTime = falseTime1 / falseTestnum1;
				}
				break;
			case 2:
				timeBuffer = new Date().getTime();
				final IncrementalInclusionCheck2<LETTER, STATE> IIC2 =
						new IncrementalInclusionCheck2<>(services, sf, a, b.subList(0, 1));
				for (int i = 1; i < b.size(); i++) {
					IIC2.addSubtrahend(b.get(i));
				}
				timeBuffer = new Date().getTime() - timeBuffer;
				if (IIC2.getResult()) {
					trueTime2 += timeBuffer;
					trueTestnum2++;
					trueSumRun2 += IIC2.counter_run;
					trueSumTotalNode2 += IIC2.counter_total_nodes;
					trueSumNodeInTheEnd2 += IIC2.counter_total_nodes;
				} else {
					falseTime2 += timeBuffer;
					falseTestnum2++;
					falseSumRun2 += IIC2.counter_run;
					falseSumTotalNode2 += IIC2.counter_total_nodes;
					falseSumNodeInTheEnd2 += IIC2.counter_total_nodes;
				}
				if (trueTestnum2 != 0) {
					trueAvgNodeInTheEnd = trueSumNodeInTheEnd2 / trueTestnum2;
					trueAvgNodeGenerated = trueSumTotalNode2 / trueTestnum2;
					trueAvgRun = trueSumRun2 / trueTestnum2;
					trueTestNum = trueTestnum2;
					trueAvgTime = trueTime2 / trueTestnum2;
				}
				if (falseTestnum2 != 0) {
					falseAvgNodeInTheEnd = falseSumNodeInTheEnd2 / falseTestnum2;
					falseAvgNodeGenerated = falseSumTotalNode2 / falseTestnum2;
					falseAvgRun = falseSumRun2 / falseTestnum2;
					falseTestNum = falseTestnum2;
					falseAvgTime = falseTime2 / falseTestnum2;
				}
				break;
			case 3:
				timeBuffer = new Date().getTime();
				final IncrementalInclusionCheck3<LETTER, STATE> IIC3 =
						new IncrementalInclusionCheck3<>(services, sf, a, b.subList(0, 1));
				for (int i = 1; i < b.size(); i++) {
					IIC3.addSubtrahend(b.get(i));
				}
				timeBuffer = new Date().getTime() - timeBuffer;
				if (IIC3.getResult()) {
					trueTime3 += timeBuffer;
					trueTestnum3++;
					trueSumRun3 += IIC3.counter_run;
					trueSumTotalNode3 += IIC3.counter_total_nodes;
					trueSumNodeInTheEnd3 += IIC3.completeLeafSet.size();
				} else {
					falseTime3 += timeBuffer;
					falseTestnum3++;
					falseSumRun3 += IIC3.counter_run;
					falseSumTotalNode3 += IIC3.counter_total_nodes;
					falseSumNodeInTheEnd3 += IIC3.completeLeafSet.size();
				}
				if (trueTestnum3 != 0) {
					trueAvgNodeInTheEnd = trueSumNodeInTheEnd3 / trueTestnum3;
					trueAvgNodeGenerated = trueSumTotalNode3 / trueTestnum3;
					trueAvgRun = trueSumRun3 / trueTestnum3;
					trueTestNum = trueTestnum3;
					trueAvgTime = trueTime3 / trueTestnum3;
				}
				if (falseTestnum3 != 0) {
					falseAvgNodeInTheEnd = falseSumNodeInTheEnd3 / falseTestnum3;
					falseAvgNodeGenerated = falseSumTotalNode3 / falseTestnum3;
					falseAvgRun = falseSumRun3 / falseTestnum3;
					falseTestNum = falseTestnum3;
					falseAvgTime = falseTime3 / falseTestnum3;
				}
				break;
			case 4:
				timeBuffer = new Date().getTime();
				final IncrementalInclusionCheck4<LETTER, STATE> IIC4 =
						new IncrementalInclusionCheck4<>(services, sf, a, b.subList(0, 1));
				for (int i = 1; i < b.size(); i++) {
					IIC4.addSubtrahend(b.get(i));
				}
				timeBuffer = new Date().getTime() - timeBuffer;
				if (IIC4.getResult()) {
					trueTime4 += timeBuffer;
					trueTestnum4++;
					trueSumRun4 += IIC4.counter_run;
					trueSumTotalNode4 += IIC4.counter_total_nodes;
					trueSumNodeInTheEnd4 += IIC4.completeLeafSet.size();
				} else {
					falseTime4 += timeBuffer;
					falseTestnum4++;
					falseSumRun4 += IIC4.counter_run;
					falseSumTotalNode4 += IIC4.counter_total_nodes;
					falseSumNodeInTheEnd4 += IIC4.completeLeafSet.size();
				}
				if (trueTestnum4 != 0) {
					trueAvgNodeInTheEnd = trueSumNodeInTheEnd4 / trueTestnum4;
					trueAvgNodeGenerated = trueSumTotalNode4 / trueTestnum4;
					trueAvgRun = trueSumRun4 / trueTestnum4;
					trueTestNum = trueTestnum4;
					trueAvgTime = trueTime4 / trueTestnum4;
				}
				if (falseTestnum4 != 0) {
					falseAvgNodeInTheEnd = falseSumNodeInTheEnd4 / falseTestnum4;
					falseAvgNodeGenerated = falseSumTotalNode4 / falseTestnum4;
					falseAvgRun = falseSumRun4 / falseTestnum4;
					falseTestNum = falseTestnum4;
					falseAvgTime = falseTime4 / falseTestnum4;
				}
				break;
			case 5:
				timeBuffer = new Date().getTime();
				final IncrementalInclusionCheck5<LETTER, STATE> IIC5 =
						new IncrementalInclusionCheck5<>(services, sf, a, b.subList(0, 1));
				for (int i = 1; i < b.size(); i++) {
					IIC5.addSubtrahend(b.get(i));
				}
				timeBuffer = new Date().getTime() - timeBuffer;
				if (IIC5.getResult()) {
					trueTime5 += timeBuffer;
					trueTestnum5++;
					trueSumRun5 += IIC5.counter_run;
					trueSumTotalNode5 += IIC5.counter_total_nodes;
					trueSumNodeInTheEnd5 += IIC5.completeLeafSet.size();
				} else {
					falseTime5 += timeBuffer;
					falseTestnum5++;
					falseSumRun5 += IIC5.counter_run;
					falseSumTotalNode5 += IIC5.counter_total_nodes;
					falseSumNodeInTheEnd5 += IIC5.completeLeafSet.size();
				}
				if (trueTestnum5 != 0) {
					trueAvgNodeInTheEnd = trueSumNodeInTheEnd5 / trueTestnum5;
					trueAvgNodeGenerated = trueSumTotalNode5 / trueTestnum5;
					trueAvgRun = trueSumRun5 / trueTestnum5;
					trueTestNum = trueTestnum5;
					trueAvgTime = trueTime5 / trueTestnum5;
				}
				if (falseTestnum5 != 0) {
					falseAvgNodeInTheEnd = falseSumNodeInTheEnd5 / falseTestnum5;
					falseAvgNodeGenerated = falseSumTotalNode5 / falseTestnum5;
					falseAvgRun = falseSumRun5 / falseTestnum5;
					falseTestNum = falseTestnum5;
					falseAvgTime = falseTime5 / falseTestnum5;
				}
				break;
			case 32:
				timeBuffer = new Date().getTime();
				final IncrementalInclusionCheck3_2<LETTER, STATE> IIC3_2 =
						new IncrementalInclusionCheck3_2<>(services, sf, a, b.subList(0, 1));
				for (int i = 1; i < b.size(); i++) {
					IIC3_2.addSubtrahend(b.get(i));
				}
				timeBuffer = new Date().getTime() - timeBuffer;
				if (IIC3_2.getResult()) {
					trueTime32 += timeBuffer;
					trueTestnum32++;
					trueSumRun32 += IIC3_2.counter_run;
					trueSumTotalNode32 += IIC3_2.counter_total_nodes;
					trueSumNodeInTheEnd32 += IIC3_2.completeLeafSet.size();
				} else {
					falseTime32 += timeBuffer;
					falseTestnum32++;
					falseSumRun32 += IIC3_2.counter_run;
					falseSumTotalNode32 += IIC3_2.counter_total_nodes;
					falseSumNodeInTheEnd32 += IIC3_2.completeLeafSet.size();
				}
				if (trueTestnum32 != 0) {
					trueAvgNodeInTheEnd = trueSumNodeInTheEnd32 / trueTestnum32;
					trueAvgNodeGenerated = trueSumTotalNode32 / trueTestnum32;
					trueAvgRun = trueSumRun32 / trueTestnum32;
					trueTestNum = trueTestnum32;
					trueAvgTime = trueTime32 / trueTestnum32;
				}
				if (falseTestnum32 != 0) {
					falseAvgNodeInTheEnd = falseSumNodeInTheEnd32 / falseTestnum32;
					falseAvgNodeGenerated = falseSumTotalNode32 / falseTestnum32;
					falseAvgRun = falseSumRun32 / falseTestnum32;
					falseTestNum = falseTestnum32;
					falseAvgTime = falseTime32 / falseTestnum32;
				}
				break;
			case 42:
				timeBuffer = new Date().getTime();
				final IncrementalInclusionCheck4_2<LETTER, STATE> IIC4_2 =
						new IncrementalInclusionCheck4_2<>(services, sf, a, b.subList(0, 1));
				for (int i = 1; i < b.size(); i++) {
					IIC4_2.addSubtrahend(b.get(i));
				}
				timeBuffer = new Date().getTime() - timeBuffer;
				if (IIC4_2.getResult()) {
					trueTime42 += timeBuffer;
					trueTestnum42++;
					trueSumRun42 += IIC4_2.counter_run;
					trueSumTotalNode42 += IIC4_2.counter_total_nodes;
					trueSumNodeInTheEnd42 += IIC4_2.completeLeafSet.size();
				} else {
					falseTime42 += timeBuffer;
					falseTestnum42++;
					falseSumRun42 += IIC4_2.counter_run;
					falseSumTotalNode42 += IIC4_2.counter_total_nodes;
					falseSumNodeInTheEnd42 += IIC4_2.completeLeafSet.size();
				}
				if (trueTestnum42 != 0) {
					trueAvgNodeInTheEnd = trueSumNodeInTheEnd42 / trueTestnum42;
					trueAvgNodeGenerated = trueSumTotalNode42 / trueTestnum42;
					trueAvgRun = trueSumRun42 / trueTestnum42;
					trueTestNum = trueTestnum42;
					trueAvgTime = trueTime42 / trueTestnum42;
				}
				if (falseTestnum42 != 0) {
					falseAvgNodeInTheEnd = falseSumNodeInTheEnd42 / falseTestnum42;
					falseAvgNodeGenerated = falseSumTotalNode42 / falseTestnum42;
					falseAvgRun = falseSumRun42 / falseTestnum42;
					falseTestNum = falseTestnum42;
					falseAvgTime = falseTime42 / falseTestnum42;
				}
				break;
			case 52:
				timeBuffer = new Date().getTime();
				final IncrementalInclusionCheck5_2<LETTER, STATE> IIC5_2 =
						new IncrementalInclusionCheck5_2<>(services, sf, a, b.subList(0, 1));
				for (int i = 1; i < b.size(); i++) {
					IIC5_2.addSubtrahend(b.get(i));
				}
				timeBuffer = new Date().getTime() - timeBuffer;
				if (IIC5_2.getResult()) {
					trueTime52 += timeBuffer;
					trueTestnum52++;
					trueSumRun52 += IIC5_2.counter_run;
					trueSumTotalNode52 += IIC5_2.counter_total_nodes;
					trueSumNodeInTheEnd52 += IIC5_2.completeLeafSet.size();
				} else {
					falseTime52 += timeBuffer;
					falseTestnum52++;
					falseSumRun52 += IIC5_2.counter_run;
					falseSumTotalNode52 += IIC5_2.counter_total_nodes;
					falseSumNodeInTheEnd52 += IIC5_2.completeLeafSet.size();
				}
				if (trueTestnum52 != 0) {
					trueAvgNodeInTheEnd = trueSumNodeInTheEnd52 / trueTestnum52;
					trueAvgNodeGenerated = trueSumTotalNode52 / trueTestnum52;
					trueAvgRun = trueSumRun52 / trueTestnum52;
					trueTestNum = trueTestnum52;
					trueAvgTime = trueTime52 / trueTestnum52;
				}
				if (falseTestnum52 != 0) {
					falseAvgNodeInTheEnd = falseSumNodeInTheEnd52 / falseTestnum52;
					falseAvgNodeGenerated = falseSumTotalNode52 / falseTestnum52;
					falseAvgRun = falseSumRun52 / falseTestnum52;
					falseTestNum = falseTestnum52;
					falseAvgTime = falseTime52 / falseTestnum52;
				}
				break;
		}
	}

	@Override
	public String operationName() {
		return "Jeffery_Test_3";
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
		final String log = "\r\nTrue cases: avg Nodes generated:" + trueAvgNodeGenerated + " avg Nodes in the end:"
				+ trueAvgNodeInTheEnd + " avgRuns:" + trueAvgRun + " Total test:" + trueTestNum + " avg Time:"
				+ trueAvgTime + "\r\nFalse cases: avg Nodes generated:" + falseAvgNodeGenerated
				+ " avg Nodes in the end:" + falseAvgNodeInTheEnd + " avgRuns:" + falseAvgRun + " Total test:"
				+ falseTestNum + " avg Time:" + falseAvgTime;
		return log;
	}
	/*
	 * public String getResult() throws OperationCanceledException { return
	 * "Jeffery_Test_3_result:"+automataCollection.size(); }
	 */

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}

}
