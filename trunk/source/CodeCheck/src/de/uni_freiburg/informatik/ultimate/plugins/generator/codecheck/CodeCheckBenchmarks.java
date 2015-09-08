/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CodeCheck plug-in.
 * 
 * The ULTIMATE CodeCheck plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CodeCheck plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CodeCheck plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CodeCheck plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CodeCheck plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

public class CodeCheckBenchmarks implements ICsvProviderProvider<Object> {

	private SimpleCsvProvider<Object> mCsvP;
	
//	/**
//	 * true, if we are benchmarking a TraceCheckerSPWP ("Betim interpolation"),
//	 * false for a normal TraceChecker (SMTInterpol interpolation)
//	 */
//	private boolean weHaveTraceCheckerSPWP;
//
//	public CodeCheckBenchmarks(boolean b) {
//		weHaveTraceCheckerSPWP = b;
//	}

	@Override
	public ICsvProvider<Object> createCvsProvider() {
		if (mCsvP == null) {
			ArrayList<String> columnTitles = new ArrayList<>();
			columnTitles.add("time (ms)");
			columnTitles.add("Overall iterations");
			columnTitles.add(CodeCheckObserver.s_NumberOfCodeBlocks);
//			columnTitles.add(CodeCheckObserver.s_SizeOfPredicates);
			columnTitles.add(CodeCheckObserver.s_SizeOfPredicatesFP);
			columnTitles.add(CodeCheckObserver.s_SizeOfPredicatesBP);
			columnTitles.add(CodeCheckObserver.s_ConjunctsInSSA);
			columnTitles.add(CodeCheckObserver.s_ConjunctsInUnsatCore);
			columnTitles.add("InterpolantCoveringCapability");
			columnTitles.add("ICC %");
			mCsvP = new SimpleCsvProvider<Object>(columnTitles);
		}
		return mCsvP;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("CodeCheck benchmark data:\n");
		sb.append(mCsvP.getColumnTitles() + "\n");
		for (List<Object> l : mCsvP.getTable()) {
			for (Object i : l) {
				sb.append(i);
				sb.append("\t");
			}
			sb.append("\n");
		}
		return sb.toString();
//		return "---- bmdata -----\n" + mCsvP.getTable().toString();
	}
}
