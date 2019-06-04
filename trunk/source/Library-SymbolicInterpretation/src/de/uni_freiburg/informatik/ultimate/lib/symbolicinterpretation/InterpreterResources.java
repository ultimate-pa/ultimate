/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation;

import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.summarizers.ILoopSummarizer;

/**
 * Class to resolve cyclic dependencies between {@link IcfgInterpreter}, {@link DagInterpreter}, and some
 * {@link ILoopSummarizer}s.
 * 
 * TODO add more shared resources (for instance domain) to simplify constructor signatures.
 * 
 * @author schaetzc@tf.uni-freiburg.de
 */
public class InterpreterResources {

	private ILoopSummarizer mSummarizer;
	private DagInterpreter mDagInterpreter;
	private IcfgInterpreter mIcfgInterpreter;

	public void setIcfgInterpreter(final IcfgInterpreter icfgInterpreter) {
		mIcfgInterpreter = icfgInterpreter;
	}
	public void setDagInterpreter(final DagInterpreter dagInterpreter) {
		mDagInterpreter = dagInterpreter;
	}
	public void setLoopSummarizer(final ILoopSummarizer summarizer) {
		mSummarizer = summarizer;
	}
	public ILoopSummarizer getLoopSummarizer() {
		return mSummarizer;
	}
	public DagInterpreter getDagInterpreter() {
		return mDagInterpreter;
	}
	public IcfgInterpreter getIcfgInterpreter() {
		return mIcfgInterpreter;
	}

}
