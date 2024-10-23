/*
 * Copyright (C) 2024 Marcel Ebbinghaus
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

/**
 * Interface for all tracked statistics regarding conditional commutativity checking. This interface mainly serves as a
 * workaround for package dependencies.
 * 
 * @author Marcel Ebbinghaus
 *
 */
public interface IConditionalCommutativityCheckerStatisticsUtils {
	public void startCheckerStopwatch();

	public void stopCheckerStopwatch();

	public void addDFSRestart();

	public void addIAIntegration();

	public void addCommutingCounterexample();

	public void addConditionCalculation();

	public void addTraceCheck();

	public void addImperfectProof();

	public void addUnknownTraceCheck();

	public void addQuantifiedCondition();

	public void addFalseCondition();
}
